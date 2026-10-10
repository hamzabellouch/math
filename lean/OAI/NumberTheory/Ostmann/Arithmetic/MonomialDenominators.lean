import OAI.NumberTheory.Ostmann.Arithmetic.HistoryFieldEvaluation
import OAI.NumberTheory.Ostmann.Characters.RationalHistoryVariables

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.MonomialDenominators
open MvPolynomial

variable {ι : Type*}

inductive Generated (S : Set ℤ) : MvPolynomial ι ℤ → Prop
  | one : Generated S 1
  | constant (c : ℤ) (hc : c ∈ S) : Generated S (C c)
  | var (i : ι) : Generated S (X i)
  | mul {P Q : MvPolynomial ι ℤ} : Generated S P → Generated S Q → Generated S (P*Q)

theorem Generated.exists_monomial {S : Set ℤ} {P : MvPolynomial ι ℤ}
    (hP : Generated S P) {K : Type*} [Field K]
    (hS : ∀ c ∈ S, (c:K) ≠ 0) :
    ∃ (d : ι →₀ ℕ) (c : ℤ), P = monomial d c ∧ (c:K) ≠ 0 := by
  classical
  induction hP with
  | one => exact ⟨0,1,by simp,by simp⟩
  | constant c hc => exact ⟨0,c,rfl,hS c hc⟩
  | var i => exact ⟨Finsupp.single i 1,1,rfl,by simp⟩
  | @mul P Q hP hQ ihP ihQ =>
      obtain ⟨d,c,rfl,hc⟩ := ihP
      obtain ⟨e,b,rfl,hb⟩ := ihQ
      exact ⟨d+e,c*b,by rw [monomial_mul_monomial],by simpa only [Int.cast_mul] using mul_ne_zero hc hb⟩

theorem Generated.eval₂_ne_zero {S : Set ℤ} {P : MvPolynomial ι ℤ}
    (hP : Generated S P) {K : Type*} [Field K] [DecidableEq ι]
    (hS : ∀ c ∈ S, (c:K) ≠ 0) (x : ι → K)
    (hx : ∀ i ∈ P.vars, x i ≠ 0) : eval₂ (Int.castRingHom K) x P ≠ 0 := by
  obtain ⟨d,c,rfl,hc⟩ := hP.exists_monomial hS
  have hcZ : c ≠ 0 := by intro h; exact hc (by simp [h])
  rw [vars_monomial hcZ] at hx
  rw [eval₂_monomial]
  apply mul_ne_zero hc
  change (∏ i ∈ d.support, x i ^ d i) ≠ 0
  exact Finset.prod_ne_zero_iff.mpr (fun i hi => pow_ne_zero _ (hx i hi))

end Ostmann.Arithmetic.MonomialDenominators

end

end OAI
