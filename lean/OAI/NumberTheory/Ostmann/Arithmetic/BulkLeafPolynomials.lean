import OAI.NumberTheory.Ostmann.Arithmetic.BulkSlotPolynomials
import OAI.NumberTheory.Ostmann.Arithmetic.MovingUnitSampleBound
import OAI.NumberTheory.Ostmann.Arithmetic.MovingLogLeaves

namespace OAI

/-! # Terminal moduli as polynomials in a bulk-prime coordinate -/

namespace Ostmann
open scoped Classical

noncomputable def MovingSlotData.bulkLeafPolynomials {σ : Type*} (value : σ → ℝ) (i : σ) :
    {n : ℕ} → MovingSlotData σ n → Polynomial ℝ → Polynomial ℝ →
      TreeLeafIndex n → Polynomial ℝ
  | _, .leaf _ regular, L, R, _ => L * R * bulkSlotProduct value i regular
  | _, .node s CL CR u left right, L, R, j =>
      let p := (MovingSlotData.step s CL CR u left right false).bulkPivotPolynomial value i L R
      match j with
      | .inl j => left.bulkLeafPolynomials value i p L j
      | .inr j => right.bulkLeafPolynomials value i p R j

theorem MovingSlotData.bulkLeafPolynomials_eval {σ : Type*} (value : σ → ℝ) (i : σ)
    {n : ℕ} (T : MovingSlotData σ n) (hT : T.CompensationAbsent i)
    (L R : Polynomial ℝ) (p : ℝ) (j : TreeLeafIndex n) :
    (T.bulkLeafPolynomials value i L R j).eval (p : ℝ) =
      T.realValueLeafModuli (Function.update value i p) (L.eval (p : ℝ)) (R.eval (p : ℝ)) j := by
  induction T generalizing L R with
  | leaf => simp only [bulkLeafPolynomials, Polynomial.eval_mul, bulkSlotProduct_eval,
      realValueLeafModuli]
  | node s CL CR u left right ihL ihR =>
    have hp := (MovingSlotData.step s CL CR u left right false).bulkPivotPolynomial_eval
      value i hT.1 L R p
    cases j with
    | inl j => simp only [bulkLeafPolynomials, realValueLeafModuli, ihL hT.2.1, hp]
    | inr j => simp only [bulkLeafPolynomials, realValueLeafModuli, ihR hT.2.2, hp]

/-- Degree grows with the fixed tree depth and the actual list lengths;
the size of a prime and every coefficient are irrelevant. -/
theorem MovingSlotData.bulkLeafPolynomials_degree {σ : Type*} (value : σ → ℝ) (i : σ)
    {n : ℕ} (T : MovingSlotData σ n) (L R : Polynomial ℝ) (d D e : ℕ)
    (hsize : T.SizeLE d) (hregular : T.RegularLengthLE D)
    (hL : L.natDegree ≤ e) (hR : R.natDegree ≤ e) (j : TreeLeafIndex n) :
    (T.bulkLeafPolynomials value i L R j).natDegree ≤ 2 * (n * d + e) + D := by
  induction T generalizing L R e with
  | leaf s regular =>
    change (L * R * bulkSlotProduct value i regular).natDegree ≤ _
    apply Polynomial.natDegree_mul_le.trans
    have hr := bulkSlotProduct_degree value i regular
    have hLR := Polynomial.natDegree_mul_le (p := L) (q := R)
    change regular.length ≤ D at hregular
    omega
  | @node n s CL CR u left right ihL ihR =>
    have hp := (MovingSlotData.step s CL CR u left right false).bulkPivotPolynomial_degree
      value i L R d e ⟨hsize.2.1, hsize.1, hsize.2.2.1⟩ hL hR
    have hLe : L.natDegree ≤ d + e := hL.trans (Nat.le_add_left _ _)
    have hRe : R.natDegree ≤ d + e := hR.trans (Nat.le_add_left _ _)
    have hn : n * d + (d + e) = (n + 1) * d + e := by ring
    cases j with
    | inl j =>
      simpa only [bulkLeafPolynomials, hn] using
        ihL _ _ (d + e) hsize.2.2.2.1 hregular.2.1 hp hLe j
    | inr j =>
      simpa only [bulkLeafPolynomials, hn] using
        ihR _ _ (d + e) hsize.2.2.2.2 hregular.2.2 hp hRe j

end Ostmann

end OAI
