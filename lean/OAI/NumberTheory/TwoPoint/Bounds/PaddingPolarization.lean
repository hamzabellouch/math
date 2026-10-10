import OAI.NumberTheory.TwoPoint.Walks.BlockTesting
import OAI.NumberTheory.TwoPoint.Bounds.ComplexPolarization

namespace OAI

/-! Transfer the existing quadratic graph tests to two bounded sequences. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma paddingTestVector_halfPair {V : Type*} [Fintype V] (Q : Finset ℕ) (L : ℝ)
    (site : V → ℤ) (f g : ℤ → ℂ) (z : ℂ) :
    paddingTestVector Q L site (halfPairFunction f g z) =
      halfPair (paddingTestVector Q L site f) (paddingTestVector Q L site g) z := by
  ext i
  by_cases hi : actualPaddingDegreeCut Q L (site i)
  · simp [paddingTestVector, halfPairFunction, halfPair, hi, div_eq_mul_inv]
    ring
  · simp [paddingTestVector, halfPairFunction, halfPair, hi]

theorem uniformAverage_padding_bilinear {Ω V : Type*} [Fintype Ω] [Fintype V]
    (Q : Finset ℕ) (L : ℝ) (site : Ω → V → ℤ)
    (T : Ω → EuclideanSpace ℂ V →L[ℂ] EuclideanSpace ℂ V) (C : ℝ)
    (hquad : ∀ f : ℤ → ℂ, (∀ n, ‖f n‖ ≤ 1) →
      uniformAverage (fun x =>
        let v := paddingTestVector Q L (site x) f
        ‖inner ℂ v (T x v)‖) ≤ C)
    (f g : ℤ → ℂ) (hf : ∀ n, ‖f n‖ ≤ 1) (hg : ∀ n, ‖g n‖ ≤ 1) :
    uniformAverage (fun x => ‖inner ℂ (paddingTestVector Q L (site x) f)
      (T x (paddingTestVector Q L (site x) g))‖) ≤ 4 * C := by
  let q (z : ℂ) (x : Ω) :=
    let v := paddingTestVector Q L (site x) (halfPairFunction f g z)
    ‖inner ℂ v (T x v)‖
  have hb (z : ℂ) (hz : ‖z‖ ≤ 1) : uniformAverage (q z) ≤ C :=
    hquad (halfPairFunction f g z) (halfPairFunction_norm_le f g z hf hg hz)
  have hp (x : Ω) : ‖inner ℂ (paddingTestVector Q L (site x) f)
      (T x (paddingTestVector Q L (site x) g))‖ ≤
        q 1 x + q (-1) x + q Complex.I x + q (-Complex.I) x := by
    have h := complex_polarization_norm (T x)
      (paddingTestVector Q L (site x) f) (paddingTestVector Q L (site x) g)
    simpa only [q, paddingTestVector_halfPair] using h
  have hav : uniformAverage (fun x => ‖inner ℂ (paddingTestVector Q L (site x) f)
      (T x (paddingTestVector Q L (site x) g))‖) ≤
      uniformAverage (q 1) + uniformAverage (q (-1)) +
        uniformAverage (q Complex.I) + uniformAverage (q (-Complex.I)) := by
    unfold uniformAverage
    simpa only [sum_add_distrib, add_div] using
      div_le_div_of_nonneg_right (sum_le_sum (fun x _ => hp x))
        (Nat.cast_nonneg (α := ℝ) (Fintype.card Ω))
  have h1 := hb 1 (by simp)
  have hm := hb (-1) (by simp)
  have hi := hb Complex.I (by simp)
  have hmi := hb (-Complex.I) (by simp)
  linarith

end TwoPointCorrelations

end OAI
