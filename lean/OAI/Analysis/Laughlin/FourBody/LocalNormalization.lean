import OAI.Analysis.Laughlin.FourBody.CoefficientNorm
import OAI.Analysis.Laughlin.Operators.LocalFourIndexEquiv

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators

theorem source_fourBody_local_normalization (Q r D : ℕ) (hr : r ≤ D) (hor : Odd r) (hQ : D+2 ≤ Q) :
    (∑ b : LocalFourIndex D,
      (fourBodyCoefficient Q r D D b.val.1.val b.val.2.1.val b.val.2.2.val)^2) = 1 := by
  classical
  let f := fun p : ℕ => ∑ j : Fin (Q+1), ∑ k : Fin (Q+1),
    if p+j.val+k.val=D ∧ j < k then (fourBodyCoefficient Q r D D p j.val k.val)^2 else 0
  have hi (p : ℕ) : (∑ i : WedgePairIndex Q,
      if p+i.val.1.val+i.val.2.val=D then (fourBodyCoefficient Q r D D p i.val.1.val i.val.2.val)^2 else 0) = f p := by
    have hs := Finset.sum_subtype (F := inferInstance) (p := fun i : SpinIndex Q Q => i.1 < i.2)
      (Finset.univ.filter (fun i : SpinIndex Q Q => i.1 < i.2)) (by simp)
      (fun i => if p+i.1.val+i.2.val=D then (fourBodyCoefficient Q r D D p i.1.val i.2.val)^2 else 0)
    rw [← hs,Finset.sum_filter,Fintype.sum_prod_type]
    apply Finset.sum_congr rfl; intro j hj
    apply Finset.sum_congr rfl; intro k hk
    by_cases h₁ : j < k <;> by_cases h₂ : p+j.val+k.val=D <;> simp [h₁,h₂]
  have hn := source_fourBody_coefficients_norm Q r D D hor hr (le_refl _) hQ
  simp_rw [hi] at hn
  rw [Fin.sum_univ_eq_sum_range] at hn
  have hsub : (∑ p ∈ Finset.range (D+1), f p) = ∑ p ∈ Finset.range ((2*Q-2)+1), f p := by
    apply Finset.sum_subset (Finset.range_mono (by omega))
    intro p hp hn
    have hpD : D < p := by simpa using hn
    apply Finset.sum_eq_zero; intro j hj
    apply Finset.sum_eq_zero; intro k hk
    simp [show p+j.val+k.val≠D by omega]
  have he := localFourIndex_sum Q D (by omega)
    (fun p j k => (fourBodyCoefficient Q r D D p j.val k.val)^2)
  rw [← he]
  change (∑ p : Fin (D+1), f p.val)=1
  rw [Fin.sum_univ_eq_sum_range,hsub]
  exact hn

end Laughlin.Spin

end OAI
