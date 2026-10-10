import OAI.NumberTheory.CubicMoment.Estimates.ComplementAbsoluteMass

namespace OAI

/-! Exact collection of absolute tuple weights by their primary product.
This is a finite identity, before any cancellation estimate. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma complement_absolute_collection (S : ι → Finset Eisenstein) (i : ι)
    (W : ι → Eisenstein → ℂ) (F : Eisenstein → ℝ) :
    (∑ g ∈ coordinateComplementTuples S i,
      (∏ j ∈ Finset.univ.erase i, ‖W j (g j)‖)*F (∏ j, g j)) =
    ∑ r ∈ complementProductSupport S i, complementAbsoluteWeight S i W r*F r := by
  calc
    _ = ∑ r ∈ complementProductSupport S i,
        ∑ g ∈ (coordinateComplementTuples S i).filter (fun g => (∏ j, g j) = r),
          (∏ j ∈ Finset.univ.erase i, ‖W j (g j)‖)*F (∏ j, g j) := by
      exact (Finset.sum_fiberwise_of_maps_to
        (fun g hg => Finset.mem_image.mpr ⟨g,hg,rfl⟩) _).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro r hr
      unfold complementAbsoluteWeight
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro g hg
      rw [(Finset.mem_filter.mp hg).2]

theorem complement_absolute_tuple_mass (S : ι → Finset Eisenstein)
    (hS : ∀ j, ∀ p ∈ S j, primaryPrime p) (i : ι)
    (W : ι → Eisenstein → ℂ) (hW : ∀ j, ∀ p ∈ S j, ‖W j p‖ ≤ 1)
    (D : Finset Eisenstein) (hD : ∀ d ∈ D, primary d) {Y w : ℝ}
    (hY : 0 ≤ Y) (hw : 1 ≤ w)
    (hrough : ∀ j, j ≠ i → ∀ p ∈ S j, W j p ≠ 0 → w ≤ norm p)
    {m : ℕ} (hsize : Y < w^m) :
    (∑ t ∈ (coordinateComplementTuples S i ×ˢ D).filter
      (fun t => Squarefree ((∏ j, t.1 j)*t.2) ∧ norm ((∏ j, t.1 j)*t.2) ≤ Y),
      ∏ j ∈ Finset.univ.erase i, ‖W j (t.1 j)‖) ≤
      18*Y*((2^m:ℕ)*((Fintype.card ι)^(Fintype.card ι):ℕ)) := by
  apply le_trans ?_ (complement_absolute_pair_mass S hS i W hW D hD hY hw hrough hsize)
  apply le_of_eq
  rw [Finset.sum_filter,Finset.sum_product,Finset.sum_filter,Finset.sum_product]
  rw [Finset.sum_comm,Finset.sum_comm (s := complementProductSupport S i)]
  apply Finset.sum_congr rfl
  intro d hd
  have hc := complement_absolute_collection S i W
    (fun r => if Squarefree (r*d) ∧ norm (r*d) ≤ Y then 1 else 0)
  simpa only [mul_ite,mul_one,mul_zero] using hc

end CubicFirstMoment

end

end OAI
