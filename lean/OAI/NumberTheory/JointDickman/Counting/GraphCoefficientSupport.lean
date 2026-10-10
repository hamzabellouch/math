import OAI.NumberTheory.JointDickman.Amplification.ArithmeticGraphPair

namespace OAI

/-! # Canonical lags and the finite coefficient support of the graph -/

namespace JointDickman
open Finset

noncomputable def coefficientPairLag (D A E : Finset ℕ) : ℤ :=
  (((∏ p ∈ A, p : ℕ) : ℤ)-(∏ p ∈ E, p : ℕ))/(∏ p ∈ D, p : ℕ)

def GraphCoefficientAdmissible (T : ℕ) (D A E : Finset ℕ) : Prop :=
  A ≠ E ∧ coefficientPairLag D A E ≠ 0 ∧ (coefficientPairLag D A E).natAbs < T ∧
    ((∏ p ∈ A, p : ℕ) : ℤ)-(∏ p ∈ E, p : ℕ) = coefficientPairLag D A E*(∏ p ∈ D, p : ℕ) ∧
    (∏ p ∈ A, p).Coprime (coefficientPairLag D A E).natAbs

/-- Nonzero unequal-pair energy can only occur at an admissible small lag.
Thus discarding the other coefficient triples is an exact operation. -/
theorem nonzero_pairEnergy_admissible {B L T : ℕ} (τ C : ℝ) (u : ℕ → ℝ)
    (J : ℕ → ℂ) (N : ℕ) {D A E : Finset ℕ}
    (hD : D ⊆ auxiliaryPrimes B) (hA : A ⊆ auxiliaryPrimes B)
    (hE : E ⊆ auxiliaryPrimes B) (hAE : A ≠ E) (hT : T ≤ auxiliaryCutoff B)
    (h : firstFormPairEnergy B L τ C u (amplificationInnerWeight T) J N D A E ≠ 0) :
    GraphCoefficientAdmissible T D A E := by
  obtain ⟨m,_,hm⟩ := exists_ne_zero_of_sum_ne_zero h
  have hr := (mul_ne_zero_iff.mp hm).2
  have hp : star (firstFormAtom B L τ C (amplificationInnerWeight T) J N D m A) *
      firstFormAtom B L τ C (amplificationInnerWeight T) J N D m E ≠ 0 := by
    intro he
    exact hr (by rw [he]; rfl)
  have ha : firstFormAtom B L τ C (amplificationInnerWeight T) J N D m A ≠ 0 := by
    intro he
    apply hp
    rw [he,star_zero,zero_mul]
  have hb := (mul_ne_zero_iff.mp hp).2
  obtain ⟨j,hj0,hjT,hj,_,_,_,haj,_⟩ :=
    nonzero_atoms_small_coprime_lag τ C J N hD hA hE hAE hT m ha hb
  have hc : (∏ p ∈ D, p : ℕ) ≠ 0 := prod_ne_zero_iff.mpr
    (fun p hp => (auxiliaryPrimes_prime B p (hD hp)).ne_zero)
  have hlag : coefficientPairLag D A E = j := by
    unfold coefficientPairLag
    rw [hj,Int.mul_ediv_cancel _ (by exact_mod_cast hc)]
  exact ⟨hAE,by rwa [hlag],by rwa [hlag],by rwa [hlag],by rwa [hlag]⟩

end JointDickman

end OAI
