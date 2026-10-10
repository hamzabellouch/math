import OAI.MeasureTheory.Falconer.Estimates.WeightedDyadicRegularity
import OAI.MeasureTheory.Falconer.Graphs.GraphBallCover

namespace OAI

/-! Push original fine incidences to coarse line parameters, preserving their
multiplicities and the weighted ball bound. -/
namespace Falconer
open scoped BigOperators
attribute [local instance] Classical.propDecidable

noncomputable def coarsePencilWeight (P : Finset (Space 2))
    (T : Space 2 → Finset (Space 2)) (q : Space 2 → Space 2) (a : Space 2) : ℕ :=
  ∑ x ∈ P, ((T x).filter fun l => q l = a).card

theorem sum_coarsePencilWeight (P A : Finset (Space 2))
    (T : Space 2 → Finset (Space 2)) (q : Space 2 → Space 2) :
    (∑ a ∈ A, coarsePencilWeight P T q a) =
      ∑ x ∈ P, ((T x).filter fun l => q l ∈ A).card := by
  unfold coarsePencilWeight
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun x _ => Finset.sum_card_fiberwise_eq_card_filter (T x) A q

theorem sum_coarsePencilWeight_union (P : Finset (Space 2))
    (T : Space 2 → Finset (Space 2)) (q : Space 2 → Space 2) :
    (∑ a ∈ (P.biUnion T).image q, coarsePencilWeight P T q a) =
      ∑ x ∈ P, (T x).card := by
  rw [sum_coarsePencilWeight]
  apply Finset.sum_congr rfl
  intro x hx
  congr 1
  apply Finset.filter_eq_self.mpr
  intro l hl
  exact Finset.mem_image_of_mem q (Finset.mem_biUnion.mpr ⟨x,hx,hl⟩)

theorem coarsePencilWeight_pos (P : Finset (Space 2))
    (T : Space 2 → Finset (Space 2)) (q : Space 2 → Space 2)
    {a : Space 2} (ha : a ∈ (P.biUnion T).image q) :
    0 < coarsePencilWeight P T q a := by
  obtain ⟨l,hl,rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨x,hx,hl⟩ := Finset.mem_biUnion.mp hl
  have hf : 0 < ((T x).filter fun z => q z = q l).card :=
    Finset.card_pos.mpr ⟨l,Finset.mem_filter.mpr ⟨hl,rfl⟩⟩
  unfold coarsePencilWeight
  exact hf.trans_le (Finset.single_le_sum
    (f := fun y => ((T y).filter fun z => q z = q l).card)
    (fun _ _ => Nat.zero_le _) hx)

theorem coarsePencilWeight_le (P : Finset (Space 2))
    (T : Space 2 → Finset (Space 2)) (q : Space 2 → Space 2) (a : Space 2) :
    coarsePencilWeight P T q a ≤ ∑ x ∈ P, (T x).card :=
  Finset.sum_le_sum fun _ _ => Finset.card_filter_le _ _

theorem coarse_pencil_weight_ball_mul {δ Δ s K C : ℝ}
    (hΔ : 0 < Δ) (hδΔ : δ ≤ Δ) (hs : 0 ≤ s) (hK : 1 ≤ K) (hC : 0 ≤ C)
    (P : Finset (Space 2)) (T : Space 2 → Finset (Space 2))
    (q : Space 2 → Space 2)
    (hnear : ∀ x ∈ P, ∀ l ∈ T x, dist l (q l) ≤ C*Δ)
    (hball : ∀ x ∈ P, NormalizedFiniteBallBound δ s K (T x)) :
    ∀ z r, Δ ≤ r → r ≤ 1 →
      (∑ a ∈ ((P.biUnion T).image q).filter (fun a => dist a z ≤ r),
        (coarsePencilWeight P T q a:ℝ)) ≤
      (K*(C+1)^s)*r^s*
        (∑ a ∈ (P.biUnion T).image q, (coarsePencilWeight P T q a:ℝ)) := by
  intro z r hr _
  have hr0 : 0 < r := hΔ.trans_le hr
  have he (A : Finset (Space 2)) : (∑ a ∈ A, (coarsePencilWeight P T q a:ℝ)) =
      ∑ x ∈ P, (((T x).filter fun l => q l ∈ A).card:ℝ) := by
    exact_mod_cast sum_coarsePencilWeight P A T q
  have htotal : (∑ a ∈ (P.biUnion T).image q, (coarsePencilWeight P T q a:ℝ)) =
      ∑ x ∈ P, ((T x).card:ℝ) := by
    exact_mod_cast sum_coarsePencilWeight_union P T q
  rw [he,htotal]
  calc
    _ ≤ ∑ x ∈ P, K*((C+1)*r)^s*((T x).card:ℝ) := by
      apply Finset.sum_le_sum
      intro x hx
      have hsub : (T x).filter (fun l => q l ∈ ((P.biUnion T).image q).filter
          (fun a => dist a z ≤ r)) ⊆ (T x).filter (fun l => dist l z ≤ (C+1)*r) := by
        intro l hl
        obtain ⟨hlT,hlq⟩ := Finset.mem_filter.mp hl
        have hqr := (Finset.mem_filter.mp hlq).2
        exact Finset.mem_filter.mpr ⟨hlT,(dist_triangle l (q l) z).trans
          ((add_le_add (hnear x hx l hlT) hqr).trans (by nlinarith only [hr,hC]))⟩
      exact (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans
        (normalized_ball_bound_all_radii hs hK (hball x hx) z ((C+1)*r)
          (hδΔ.trans (by nlinarith only [hr,hΔ,hC])))
    _ = _ := by rw [← Finset.mul_sum,Real.mul_rpow (by linarith : (0:ℝ) ≤ C+1) hr0.le]; ring

theorem coarse_pencil_weight_ball {δ Δ s K : ℝ}
    (hΔ : 0 < Δ) (hδΔ : δ ≤ Δ) (hs : 0 ≤ s) (hK : 1 ≤ K)
    (P : Finset (Space 2)) (T : Space 2 → Finset (Space 2))
    (q : Space 2 → Space 2)
    (hnear : ∀ x ∈ P, ∀ l ∈ T x, dist l (q l) ≤ Δ)
    (hball : ∀ x ∈ P, NormalizedFiniteBallBound δ s K (T x)) :
    ∀ z r, Δ ≤ r → r ≤ 1 →
      (∑ a ∈ ((P.biUnion T).image q).filter (fun a => dist a z ≤ r),
        (coarsePencilWeight P T q a:ℝ)) ≤
      (K*(2:ℝ)^s)*r^s*
        (∑ a ∈ (P.biUnion T).image q, (coarsePencilWeight P T q a:ℝ)) := by
  simpa only [one_add_one_eq_two,one_mul] using
    coarse_pencil_weight_ball_mul hΔ hδΔ hs hK (C := 1) (by norm_num) P T q (by simpa only [one_mul] using hnear) hball

end Falconer

end OAI
