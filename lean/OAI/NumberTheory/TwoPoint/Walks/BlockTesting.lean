import OAI.NumberTheory.TwoPoint.Bounds.ActualPaddingIntegerBounds
import OAI.NumberTheory.TwoPoint.Bounds.CoordinateProjection
import OAI.NumberTheory.TwoPoint.Bounds.NonnegativeProgressionAverage

namespace OAI

/-! Test the retained graph against bounded arithmetic functions. The
norm average uses the truncated integer padding estimate. -/

namespace TwoPointCorrelations

open Finset Filter
open scoped Classical

lemma norm_inner_operator_le {V : Type*} [Fintype V]
    (T : EuclideanSpace ℂ V →L[ℂ] EuclideanSpace ℂ V) (v : EuclideanSpace ℂ V) :
    ‖inner ℂ v (T v)‖ ≤ ‖T‖ * ‖v‖ ^ 2 := by
  calc
    _ ≤ ‖v‖ * ‖T v‖ := norm_inner_le_norm _ _
    _ ≤ ‖v‖ * (‖T‖ * ‖v‖) :=
      mul_le_mul_of_nonneg_left (T.le_opNorm v) (norm_nonneg _)
    _ = _ := by ring

theorem FiniteLaw.average_operator_test {Ω V : Type*} [Fintype Ω] [Fintype V]
    (μ : FiniteLaw Ω) (T : Ω → EuclideanSpace ℂ V →L[ℂ] EuclideanSpace ℂ V)
    (v : Ω → EuclideanSpace ℂ V) (B D Z δ : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hv : μ.average (fun x => ‖v x‖ ^ 2) ≤ Z)
    (hbad : μ.probability (fun x => B < ‖T x‖) ≤ δ)
    (hbound : ∀ x, B < ‖T x‖ → ‖inner ℂ (v x) (T x (v x))‖ ≤ D) :
    μ.average (fun x => ‖inner ℂ (v x) (T x (v x))‖) ≤ B * Z + D * δ := by
  have hp (x : Ω) : ‖inner ℂ (v x) (T x (v x))‖ ≤
      B * ‖v x‖ ^ 2 + D * (if B < ‖T x‖ then 1 else 0) := by
    by_cases hx : B < ‖T x‖
    · rw [ite_eq_left hx, mul_one]
      exact (hbound x hx).trans (le_add_of_nonneg_left (mul_nonneg hB (sq_nonneg _)))
    · rw [ite_eq_right hx, mul_zero, add_zero]
      exact (norm_inner_operator_le (T x) (v x)).trans
        (mul_le_mul_of_nonneg_right (le_of_not_gt hx) (sq_nonneg _))
  calc
    _ ≤ μ.average (fun x => B * ‖v x‖ ^ 2 + D * (if B < ‖T x‖ then 1 else 0)) :=
      μ.average_mono hp
    _ = B * μ.average (fun x => ‖v x‖ ^ 2) +
        D * μ.probability (fun x => B < ‖T x‖) := by
      simp only [FiniteLaw.average, FiniteLaw.probability, mul_add, sum_add_distrib]
      congr 1 <;> rw [mul_sum] <;> apply sum_congr rfl <;> intro x _ <;> ring
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hv hB)
      (mul_le_mul_of_nonneg_left hbad hD)

noncomputable def paddingTestVector {V : Type*} (Q : Finset ℕ) (L : ℝ)
    (site : V → ℤ) (f : ℤ → ℂ) : EuclideanSpace ℂ V :=
  WithLp.toLp 2 (fun i => if actualPaddingDegreeCut Q L (site i) then
    (actualPaddingVertex Q (site i) : ℂ) * f (site i) else 0)

lemma paddingTestVector_norm_sq_le {V : Type*} [Fintype V]
    (Q : Finset ℕ) (L : ℝ) (site : V → ℤ) (f : ℤ → ℂ) (hf : ∀ n, ‖f n‖ ≤ 1) :
    ‖paddingTestVector Q L site f‖ ^ 2 ≤
      ∑ i, (actualPaddingVertex Q (site i)) ^ 2 *
        (if actualPaddingDegreeCut Q L (site i) then 1 else 0) := by
  rw [EuclideanSpace.norm_sq_eq]
  apply sum_le_sum
  intro i _
  by_cases hi : actualPaddingDegreeCut Q L (site i)
  · simp only [paddingTestVector, WithLp.ofLp_toLp, ite_eq_left hi, norm_mul,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (actualPaddingVertex_pos Q _), mul_one]
    apply pow_le_pow_left₀
      (mul_nonneg (actualPaddingVertex_pos Q (site i)).le (norm_nonneg _)) _ 2
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left (hf (site i)) (actualPaddingVertex_pos Q (site i)).le
  · simp [paddingTestVector, hi]

theorem BravermanDepth22Input.eventually_padding_test_norm
    (hBr : BravermanDepth22Input) :
    ∃ A : ℕ, 1000 ≤ A ∧ ∀ᶠ L : ℝ in atTop,
      ∀ (Q : Finset ℕ), (∀ p ∈ Q, p.Prime) →
      (∀ p ∈ Q, (p : ℝ) ≤ Real.exp L) →
      ∀ {V : Type*} [Fintype V] (site : V → ℤ) (f : ℤ → ℂ), (∀ n, ‖f n‖ ≤ 1) →
      ∀ a N : ℕ, Real.exp (L ^ A / 2) ≤ (N : ℝ) →
      uniformAverage (fun x : Fin N => ‖paddingTestVector Q L
        (fun i => ((a + x.val : ℕ) : ℤ) + site i) f‖ ^ 2) ≤
        2 * Fintype.card V * paddingTiltNormalizer Q := by
  obtain ⟨A, hA, hb⟩ := hBr.eventually_actual_padding_weight_sum
  refine ⟨A, hA, ?_⟩
  filter_upwards [hb] with L hb
  intro Q hQ hupper V _ site f hf a N hN
  classical
  calc
    _ ≤ uniformAverage (fun x : Fin N => ∑ i : V,
        (actualPaddingVertex Q (((a + x.val : ℕ) : ℤ) + site i)) ^ 2 *
          if actualPaddingDegreeCut Q L (((a + x.val : ℕ) : ℤ) + site i) then 1 else 0) := by
      unfold uniformAverage
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
      exact sum_le_sum (fun x _ => paddingTestVector_norm_sq_le Q L _ f hf)
    _ = ∑ i : V, uniformAverage (fun x : Fin N =>
        (actualPaddingVertex Q (((a + x.val : ℕ) : ℤ) + site i)) ^ 2 *
          if actualPaddingDegreeCut Q L (((a + x.val : ℕ) : ℤ) + site i) then 1 else 0) := by
      unfold uniformAverage
      rw [sum_comm, sum_div]
    _ ≤ _ := by simpa only [card_univ] using hb Q hQ hupper univ site a N hN

theorem BravermanDepth22Input.eventually_padding_test_progression_norm
    (hBr : BravermanDepth22Input) :
    ∃ A : ℕ, 1000 ≤ A ∧ ∀ᶠ L : ℝ in atTop,
      ∀ (Q : Finset ℕ), (∀ p ∈ Q, p.Prime) →
      (∀ p ∈ Q, (p : ℝ) ≤ Real.exp L) →
      ∀ {V : Type*} [Fintype V] (site : V → ℤ) (f : ℤ → ℂ), (∀ n, ‖f n‖ ≤ 1) →
      ∀ a l N : ℕ, 0 < l → Real.exp (L ^ A / 2) ≤ (N : ℝ) →
      uniformAverage (fun x : Fin N => ‖paddingTestVector Q L
        (fun i => ((a + l * x.val : ℕ) : ℤ) + site i) f‖ ^ 2) ≤
        (l : ℝ) * (2 * Fintype.card V * paddingTiltNormalizer Q) := by
  obtain ⟨A, hA, hb⟩ := hBr.eventually_padding_test_norm
  refine ⟨A, hA, ?_⟩
  filter_upwards [hb] with L hb
  intro Q hQ hupper V _ site f hf a l N hl hN
  have hlr : (1 : ℝ) ≤ l := by exact_mod_cast hl
  have hNl : Real.exp (L ^ A / 2) ≤ (l * N : ℕ) := by
    rw [Nat.cast_mul]
    exact hN.trans (by nlinarith [Nat.cast_nonneg (α := ℝ) N])
  have hp := uniformAverage_progression_le
    (fun n => ‖paddingTestVector Q L (fun i => (n : ℤ) + site i) f‖ ^ 2)
    (fun n => sq_nonneg _) a l N hl
  exact hp.trans (mul_le_mul_of_nonneg_left
    (hb Q hQ hupper site f hf a (l * N) hNl) (Nat.cast_nonneg _))

lemma projected_paddingTestVector_norm_sq_le {V : Type*} [Fintype V] [DecidableEq V]
    (Q : Finset ℕ) (L : ℝ) (site : V → ℤ) (f : ℤ → ℂ)
    (keep : V → Prop) :
    ‖coordinateProjection keep (paddingTestVector Q L site f)‖ ^ 2 ≤
      ‖paddingTestVector Q L site f‖ ^ 2 :=
  (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr (coordinateProjection_norm_le _ _)

end TwoPointCorrelations

end OAI
