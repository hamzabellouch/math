import OAI.Combinatorics.Progressions.Probability.WeightedSliceFamilyLaw

namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

variable {D α : Type*} [Fintype D] [DecidableEq D]
variable [Fintype α] [DecidableEq α] [IsEmpty α]
variable (B : D → Type*) [∀ d, Fintype (B d)] [∀ d, DecidableEq (B d)]
variable (h : D → ℕ) (L : PrincipalTupleIndex B h → ℕ) (hL : ∀ j, 0 < L j)

theorem principalTupleWeights_zero_rationalForecast_error
    {I O : Type*} [Fintype O] [DecidableEq O]
    (poly : O → MvPolynomial (PrincipalTupleIndex B h ⊕ I) ℤ) (inactive : I → ℤ)
    {q N : ℕ} [NeZero q] [NeZero N] (hq : q ∣ N)
    (test : (O → ZMod q) → ℂ) (htest : ∀ r, ‖test r‖ ≤ 1)
    (hsmall : (∑ j, (q : ℝ) / (L j : ℝ)) ≤ 1 / 2) :
    ‖(principalTupleWeights (α := α) B h L hL).complexMean
      (fun y => test (fun o => (MvPolynomial.eval
        (Sum.elim (fun j => (y j none : ℤ)) inactive) (poly o) : ZMod q))) -
      (𝔼 b : O → ZMod N,
        (rationalOutputDensity
          (FiniteProbabilityWeights.uniform (PrincipalTupleIndex B h → ZMod N))
          (integerLongPolynomialOutput poly inactive N) N b : ℂ) *
            test (fun o => ZMod.castHom hq (ZMod q) (b o)))‖ ≤
      2 * ∑ j, (q : ℝ) / (L j : ℝ) := by
  rw [principalTupleWeights_zero_complexMean B h L hL
    (fun t => test (fun o => (MvPolynomial.eval (Sum.elim t inactive) (poly o) : ZMod q)))]
  simpa only [sub_zero, Int.cast_natCast] using
    rationalPolynomialForecast_box_error (fun _ => 0) (fun j => (L j : ℤ))
      (fun j => by exact_mod_cast hL j) poly inactive hq test htest
      (by simpa only [sub_zero, Int.cast_natCast] using hsmall)

theorem principalTupleWeights_zero_rationalInactiveForecast_error
    {Ω I O Z : Type*} [Fintype Ω] [Fintype O] [DecidableEq O] [Fintype Z]
    (inactive : FiniteProbabilityWeights Ω) (gridPoint : Ω → Z)
    (poly : O → MvPolynomial (PrincipalTupleIndex B h ⊕ I) ℤ)
    (inactiveCoord : Ω → I → ℤ)
    {q N : ℕ} [NeZero q] [NeZero N] (hq : q ∣ N)
    {gridVolume : ℝ} (hV : gridVolume ≠ 0)
    (test : Z → (O → ZMod q) → ℂ) (htest : ∀ z r, ‖test z r‖ ≤ 1)
    (hsmall : (∑ j, (q : ℝ) / (L j : ℝ)) ≤ 1 / 2) :
    ‖inactive.complexMean (fun i =>
      (principalTupleWeights (α := α) B h L hL).complexMean
        (fun y => test (gridPoint i) (fun o => (MvPolynomial.eval
          (Sum.elim (fun j => (y j none : ℤ)) (inactiveCoord i)) (poly o) : ZMod q)))) -
      (∑ z, 𝔼 b : O → ZMod N,
        ((rationalInactiveForecast inactive
          (fun _ => FiniteProbabilityWeights.uniform (PrincipalTupleIndex B h → ZMod N))
          gridPoint (fun i => integerLongPolynomialOutput poly (inactiveCoord i) N)
          N gridVolume z b / gridVolume : ℝ) : ℂ) *
            test z (fun o => ZMod.castHom hq (ZMod q) (b o)))‖ ≤
      2 * ∑ j, (q : ℝ) / (L j : ℝ) := by
  have he (i : Ω) := principalTupleWeights_zero_complexMean (α := α) B h L hL
    (fun t => test (gridPoint i) (fun o =>
      (MvPolynomial.eval (Sum.elim t (inactiveCoord i)) (poly o) : ZMod q)))
  simp_rw [he]
  simpa only [sub_zero, Int.cast_natCast] using
    rationalInactivePolynomialForecast_box_error inactive gridPoint
      (fun _ => 0) (fun j => (L j : ℤ)) (fun j => by exact_mod_cast hL j)
      poly inactiveCoord hq hV test htest
      (by simpa only [sub_zero, Int.cast_natCast] using hsmall)

end Erdos3

end

end OAI
