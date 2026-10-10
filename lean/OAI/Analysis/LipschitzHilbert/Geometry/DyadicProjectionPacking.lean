import OAI.Analysis.LipschitzHilbert.Fourier.DyadicProjectionCarleson
import OAI.Analysis.LipschitzHilbert.Fourier.LineConvolutionLocal

namespace OAI

/-! Finite collections of the actual dyadic projection cell energies
satisfy the Carleson packing condition. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace LipschitzHilbert.DyadicLineGrid

theorem cell_level_le_of_subset {q k l i j : ℤ}
    (hsub : cell q k i⊆cell q l j) : k≤l := by
  have hv := ENNReal.toReal_mono (show volume (cell q l j)≠⊤ from measure_Ico_lt_top.ne)
    (measure_mono hsub)
  change volume.real (cell q k i)≤volume.real (cell q l j) at hv
  rw [cell_length,cell_length] at hv
  exact (zpow_le_zpow_iff_right₀ (by norm_num : (1:ℝ)<2)).mp hv

theorem sum_cell_integral_le {ι : Type*} (I : Finset ι) (q k top root : ℤ)
    (pos : ι → ℤ) (hinj : Set.InjOn pos I)
    (hsub : ∀ i∈I, cell q k (pos i)⊆cell q top root)
    (g : ℝ → ℝ) (hg : IntegrableOn g (cell q top root)) (hg0 : ∀ x, 0≤g x) :
    (∑ i∈I, ∫ x in cell q k (pos i), g x)≤∫ x in cell q top root, g x := by
  classical
  have hd : (↑I : Set ι).PairwiseDisjoint (fun i => cell q k (pos i)) := by
    intro i hi j hj hij
    exact cells_disjoint q k (fun he => hij (hinj hi hj he))
  rw [←integral_biUnion_finset I (fun _ _ => cell_measurable _ _ _) hd
    (fun i hi => hg.mono_set (hsub i hi))]
  apply setIntegral_mono_set hg (Filter.Eventually.of_forall hg0)
  apply Filter.Eventually.of_forall
  intro x hx
  obtain ⟨i,hi,hx⟩ := mem_iUnion₂.mp hx
  exact hsub i hi hx

end LipschitzHilbert.DyadicLineGrid
namespace LipschitzHilbert.PacketRepresentation
open DyadicLineGrid

theorem dyadic_projection_carleson_packing {ι : Type*} (I : Finset ι)
    (q top root : ℤ) (level pos : ι → ℤ)
    (hinj : ∀ i∈I, ∀ j∈I, level i=level j → pos i=pos j → i=j)
    (hsub : ∀ i∈I, cell q (level i) (pos i)⊆cell q top root)
    (f : ℝ → ℂ) (hfm : Measurable f) (B : ℝ) (hB : 0≤B) (hfb : ∀ x, ‖f x‖≤B) :
    (∑ i∈I, ∫ x in cell q (level i) (pos i),
      ‖lineConvolution (lineProjectionKernel dyadicDifference (scale (level i))
        (scale_pos _).ne') f x‖^2)≤dyadicCarlesonConstant*B^2*scale top := by
  classical
  let index := fun i => (top-level i).toNat
  let N := I.sup index+1
  have hindex (i : ι) (hi : i∈I) : index i∈Finset.range N := by
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.le_sup hi))
  have hlevel (i : ι) (hi : i∈I) : level i=top-(index i:ℤ) := by
    have hh := cell_level_le_of_subset (hsub i hi)
    dsimp [index]
    rw [Int.toNat_of_nonneg (by omega)]
    omega
  let energy := fun i => ∫ x in cell q (level i) (pos i),
    ‖lineConvolution (lineProjectionKernel dyadicDifference (scale (level i))
      (scale_pos _).ne') f x‖^2
  have hgroup (n : ℕ) : (∑ i∈I with index i=n, energy i)≤
      ∫ x in cell q top root,
        ‖lineConvolution (lineProjectionKernel dyadicDifference (scale (top-(n:ℤ)))
          (scale_pos _).ne') f x‖^2 := by
    let g := fun x => ‖lineConvolution
      (lineProjectionKernel dyadicDifference (scale (top-(n:ℤ))) (scale_pos _).ne') f x‖^2
    have he (i : ι) (hi : i∈I.filter (fun i => index i=n)) :
        energy i=∫ x in cell q (top-(n:ℤ)) (pos i), g x := by
      have hl := hlevel i (Finset.mem_filter.mp hi).1
      rw [(Finset.mem_filter.mp hi).2] at hl
      dsimp [energy]
      simp only [hl,g]
    calc
      _ = ∑ i∈I with index i=n, ∫ x in cell q (top-(n:ℤ)) (pos i), g x :=
        Finset.sum_congr rfl he
      _ ≤ _ := sum_cell_integral_le _ q (top-(n:ℤ)) top root pos
        (by
          intro i hi j hj hp
          exact hinj i (Finset.mem_filter.mp hi).1 j (Finset.mem_filter.mp hj).1
            (by rw [hlevel i (Finset.mem_filter.mp hi).1,hlevel j (Finset.mem_filter.mp hj).1,
              (Finset.mem_filter.mp hi).2,(Finset.mem_filter.mp hj).2]) hp)
        (by
          intro i hi
          have hs := hsub i (Finset.mem_filter.mp hi).1
          rw [hlevel i (Finset.mem_filter.mp hi).1,(Finset.mem_filter.mp hi).2] at hs
          exact hs)
        g (lineConvolution_integrableOn_sq _ f hfm B hfb _ measure_Ico_lt_top.ne)
        (fun _ => sq_nonneg _)
  calc
    _ = ∑ n∈Finset.range N, ∑ i∈I with index i=n, energy i :=
      (Finset.sum_fiberwise_of_maps_to hindex energy).symm
    _ ≤ ∑ n∈Finset.range N, ∫ x in cell q top root,
        ‖lineConvolution (lineProjectionKernel dyadicDifference (scale (top-(n:ℤ)))
          (scale_pos _).ne') f x‖^2 := Finset.sum_le_sum fun n _ => hgroup n
    _ ≤ _ := dyadic_projection_carleson_cell N q top root f hfm B hB hfb

end LipschitzHilbert.PacketRepresentation

end

end OAI
