import OAI.Analysis.CircleDomains.Selection.RoundHoleOffsets
import OAI.Analysis.CircleDomains.Sobolev.SourceArea
import Mathlib.Analysis.Normed.Module.Ball.Pointwise

namespace OAI

/-! Finitely many source disks can be enlarged so that every remaining
disk meets at most one enlargement. The radius-square sum supplies the
finite set of large remaining disks. -/
open Set Function Filter Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem finite_large_square_summable_radii {ι : Type*} {r : ι → ℝ}
    (hr : ∀ j, 0 ≤ r j) (hs : Summable (fun j => r j^2)) {ε : ℝ} (hε : 0 < ε) :
    {j | ε ≤ r j}.Finite := by
  have he : ∀ᶠ j in cofinite, r j^2 < ε^2 :=
    hs.tendsto_cofinite_zero (Iio_mem_nhds (sq_pos_of_pos hε))
  have hf := mem_cofinite.mp he
  apply hf.subset
  intro j hj
  change ¬ r j^2 < ε^2
  exact not_lt.mpr ((sq_le_sq₀ hε.le (hr j)).mpr hj)

 theorem dist_centers_le_of_closedBall_inter {c d : ℂ} {r s : ℝ}
    (h : (closedBall c r ∩ closedBall d s).Nonempty) : dist c d ≤ r+s := by
  obtain ⟨x,hx,hx'⟩ := h
  exact (dist_triangle c x d).trans (add_le_add (by simpa only [dist_comm,mem_closedBall] using hx) hx')

 theorem exists_finite_tail_disk_separation {ι : Type*}
    (c : ι → ℂ) (r : ι → ℝ) (hr : ∀ j, 0 ≤ r j)
    (hd : Pairwise (Disjoint on fun j => closedBall (c j) (r j)))
    (hs : Summable (fun j => r j^2)) (F : Finset ι) :
    ∃ ε > 0, ∀ ρ ∈ Ioc (0 : ℝ) ε,
      Pairwise (Disjoint on fun j : F => closedBall (c j) (r j+ρ)) ∧
      ∀ k ∉ F, ∀ i ∈ F, ∀ j ∈ F,
        (closedBall (c k) (r k) ∩ closedBall (c i) (r i+ρ)).Nonempty →
        (closedBall (c k) (r k) ∩ closedBall (c j) (r j+ρ)).Nonempty → i = j := by
  classical
  obtain ⟨δ,hδ,hδprop⟩ := exists_common_round_hole_offset
    (fun j : F => c j) (fun j : F => r j) (fun j => hr j)
    (fun i j hij => hd (fun he => hij (Subtype.ext he))) isOpen_univ
    (fun _ => subset_univ _)
  let B := (finite_large_square_summable_radii hr hs (show 0 < δ/4 by positivity)).toFinset
  let T := F ∪ B
  obtain ⟨η,hη,hηprop⟩ := exists_common_round_hole_offset
    (fun j : T => c j) (fun j : T => r j) (fun j => hr j)
    (fun i j hij => hd (fun he => hij (Subtype.ext he))) isOpen_univ
    (fun _ => subset_univ _)
  refine ⟨min (δ/4) η,lt_min (by positivity) hη,?_⟩
  intro ρ hρ
  have hρδ : ρ ≤ δ/4 := hρ.2.trans (min_le_left _ _)
  have hρη : ρ ≤ η := hρ.2.trans (min_le_right _ _)
  have hpair := (hδprop δ ⟨hδ,le_rfl⟩).2
  refine ⟨?_,?_⟩
  · intro i j hij
    exact (hpair hij).mono
      (closedBall_subset_closedBall (by linarith))
      (closedBall_subset_closedBall (by linarith))
  · intro k hk i hi j hj hki hkj
    by_contra hij
    by_cases hkB : k ∈ B
    · have hkT : k ∈ T := Finset.mem_union_right F hkB
      have hiT : i ∈ T := Finset.mem_union_left B hi
      have hki' : (⟨k,hkT⟩ : T) ≠ ⟨i,hiT⟩ := by
        intro he
        have hki : k = i := congrArg Subtype.val he
        exact hk (hki.symm ▸ hi)
      have hdis : Disjoint (closedBall (c k) (r k)) (closedBall (c i) (r i+ρ)) :=
        ((hηprop ρ ⟨hρ.1,hρη⟩).2 hki').mono_left
          (closedBall_subset_closedBall (le_add_of_nonneg_right hρ.1.le))
      exact Set.disjoint_left.mp hdis hki.choose_spec.1 hki.choose_spec.2
    · have hsmall : r k < δ/4 := by
        have hn : ¬ δ/4 ≤ r k := by simpa only [B,Set.Finite.mem_toFinset,mem_ofPred_eq] using hkB
        exact lt_of_not_ge hn
      have hdij := (disjoint_closedBall_closedBall_iff
        (add_nonneg (hr i) hδ.le) (add_nonneg (hr j) hδ.le)).mp
        (hpair (show (⟨i,hi⟩ : F) ≠ ⟨j,hj⟩ from fun he => hij (congrArg Subtype.val he)))
      have hdi := dist_centers_le_of_closedBall_inter hki
      have hdj := dist_centers_le_of_closedBall_inter hkj
      have htri := dist_triangle (c i) (c k) (c j)
      rw [dist_comm (c i) (c k)] at htri
      linarith

end CircleDomainRigidity

end

end OAI
