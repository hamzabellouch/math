import OAI.Analysis.Laughlin.FourBody.CoefficientNorm
import OAI.Analysis.Laughlin.Operators.LocalFourIndexEquiv

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators

theorem fourWeightSlice_sum {M : Type*} [AddCommMonoid M] (Q D : ℕ) (hQ : D+2 ≤ Q)
    (f : ℕ → Fin (Q+1) → Fin (Q+1) → M) :
    (∑ p : Fin (2*Q-2+1), ∑ i : WedgePairIndex Q,
      if p.val+i.val.1.val+i.val.2.val=D then f p.val i.val.1 i.val.2 else 0) =
      ∑ b : LocalFourIndex D, f b.val.1.val ⟨b.val.2.1.val,by omega⟩ ⟨b.val.2.2.val,by omega⟩ := by
  classical
  let F := fun p : ℕ => ∑ j : Fin (Q+1), ∑ k : Fin (Q+1),
    if p+j.val+k.val=D ∧ j < k then f p j k else 0
  have hi (p : ℕ) : (∑ i : WedgePairIndex Q,
      if p+i.val.1.val+i.val.2.val=D then f p i.val.1 i.val.2 else 0) = F p := by
    have hs := Finset.sum_subtype (F := inferInstance) (p := fun i : SpinIndex Q Q => i.1 < i.2)
      (Finset.univ.filter (fun i : SpinIndex Q Q => i.1 < i.2)) (by simp)
      (fun i => if p+i.1.val+i.2.val=D then f p i.1 i.2 else 0)
    rw [← hs,Finset.sum_filter,Fintype.sum_prod_type]
    apply Finset.sum_congr rfl; intro j hj
    apply Finset.sum_congr rfl; intro k hk
    by_cases h₁ : j < k <;> by_cases h₂ : p+j.val+k.val=D <;> simp [h₁,h₂]
  simp_rw [hi]
  rw [Fin.sum_univ_eq_sum_range]
  have hsub : (∑ p ∈ Finset.range (D+1), F p) = ∑ p ∈ Finset.range (2*Q-2+1), F p := by
    apply Finset.sum_subset (Finset.range_mono (by omega))
    intro p hp hn
    have hpD : D < p := by simpa using hn
    apply Finset.sum_eq_zero; intro j hj
    apply Finset.sum_eq_zero; intro k hk
    simp [show p+j.val+k.val≠D by omega]
  rw [← hsub,← Fin.sum_univ_eq_sum_range]
  exact localFourIndex_sum Q D (by omega) f

end Laughlin.Spin

end OAI
