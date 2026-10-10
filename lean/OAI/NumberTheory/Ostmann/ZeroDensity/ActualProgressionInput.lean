import OAI.NumberTheory.Ostmann.ZeroDensity.ActualLocalZeros

namespace OAI

/-! # The prime-progression estimate with constructed exceptional zeros

This is the theta estimate of Montgomery–Vaughan, Corollary 11.20. The actual
exceptional-zero family records divisibility, completeness and Page uniqueness.
-/

namespace Ostmann

def ActualProgressionTheta : Prop :=
  ∃ c C : ℝ, 0 < c ∧ 0 ≤ C ∧
    ∀ q : ℕ, 1 ≤ q → ∀ a : ℕ, a.Coprime q → ∀ x : ℝ, 2 ≤ x →
      |primeProgressionTheta q a x -
        thetaMainTerm (Nat.totient q) (pageCoefficient (actualLocalZero q) a)
          (pageBeta (actualLocalZero q)) x| ≤
        C * x * Real.exp (-c * Real.sqrt (Real.log x))

noncomputable def progressionInput_of_actual_theta (h : ActualProgressionTheta) :
    PublishedProgressionInput := {
  kappa := actualPageConstant
  decay := Classical.choose h
  errorConstant := Classical.choose (Classical.choose_spec h)
  kappa_pos := actualPageConstant_pos
  decay_pos := (Classical.choose_spec (Classical.choose_spec h)).1
  errorConstant_nonneg := (Classical.choose_spec (Classical.choose_spec h)).2.1
  localZero := actualLocalZero
  divides := fun q e he => (actualLocalZero_spec q e he).1
  complete := actualLocalZero_complete
  unique := actualPage_unique
  theta := (Classical.choose_spec (Classical.choose_spec h)).2.2 }

end Ostmann

end OAI
