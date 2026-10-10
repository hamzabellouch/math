import OAI.NumberTheory.Ostmann.QuadraticCenter.RationalApproximationLift
import OAI.NumberTheory.Ostmann.QuadraticCenter.UniformDenominatorLifts

namespace OAI

/-! # Common rational centers from the actual phase approximation witnesses -/

namespace Ostmann

open scoped BigOperators Classical

theorem exists_commonCenter_of_phase_approximations (P : Finset ℕ)
    (t : ℕ → ℤ) (k d K H Z Amax : ℕ) (hd : d ≤ k + 1)
    (A V : ℝ) (hA : 0 < A) (hV : 0 < V) (hZ : 0 < Z) (hAmax : 0 < Amax)
    (hprime : ∀ p ∈ P, p.Prime) (hap : ∀ p ∈ P, Amax < p)
    (hmin : ∀ p ∈ P, Z ≤ p) (hlog : ∀ p ∈ P, V ≤ Real.log (p : ℝ))
    (hbudget : Real.log (2 * (H : ℝ)) < (K + 1 : ℕ) * V)
    (hsmall : 2 * K * (P.card : ℝ) ≤ A ^ 2)
    (E : Finset (Fin (k + 1) ↪ P))
    (happrox : ∀ e ∈ E, ∃ a ∈ Finset.Icc 1 Amax, ∃ tM b : ℤ, ∃ δ : ℝ,
      |(a : ℝ) * ((tM : ℝ) / primeTupleProduct P e) - b| ≤ δ ∧
      (primeTupleProduct P e : ℝ) * δ ≤ H ∧
      ∀ i, ((e i).1 : ℤ) ∣ tM - t (e i).1)
    (hpositive : 0 < (E.card : ℝ) / Amax -
      A ^ d * liftMomentUpper P.card (k + 1 - d) H Z) :
    ∃ a ∈ Finset.Icc 1 Amax,
      ∃ n ∈ Finset.Ico (-(H : ℤ)) (H + 1), ∃ h : ℤ, ∃ m : ℕ,
        0 < m ∧ m ≤ Amax ∧ h.natAbs.Coprime m ∧ |h| ≤ |n| ∧
        A ≤ ((matchingPrimes P a t n).card : ℝ) ∧
        (E.card : ℝ) / Amax - A ^ d * liftMomentUpper P.card (k + 1 - d) H Z ≤
          2 * P.card * ((matchingPrimes P a t n).card : ℝ) ^ k ∧
        ∀ (p : ℕ) (hp : p ∈ matchingPrimes P a t n),
          let _ : Fact p.Prime := ⟨hprime p (Finset.mem_filter.mp hp).1⟩
          (t p : ZMod p) = (h : ZMod p) / (m : ZMod p) := by
  apply exists_commonCenter_of_bounded_denominators P t k d K H Z Amax hd A V
    hA hV hZ hAmax hprime hap hmin hlog hbudget hsmall E _ hpositive
  intro e he
  obtain ⟨a, ha, tM, b, δ, hphase, hsize, ht⟩ := happrox e he
  exact ⟨a, ha, approximationLift_tuple P hprime e a H tM b t δ hphase hsize ht⟩

end Ostmann

end OAI
