import OAI.NumberTheory.TwoPointCorrelations.MRTSmoothEuler
import OAI.NumberTheory.TwoPointCorrelations.ModFiveSmoothedPsi
import Mathlib.NumberTheory.LSeries.Convolution

namespace OAI

/-! The smooth Euler series used in the triple-convolution Perron formula.
The finite prime factors and the smooth factor are absolutely convergent
on the line Re(s)=1. -/

namespace TwoPointCorrelations

open Finset Complex MeasureTheory Erdos970
open scoped Classical LSeries.notation

noncomputable def halaszSmoothFunction (f : ℕ → ℂ) (N n : ℕ) : ℂ :=
  if n ∈ Nat.smoothNumbers (N + 1) then f n else 0

noncomputable def halaszFiniteCoefficient (P : Finset ℕ) (a : ℕ → ℂ) (n : ℕ) : ℂ :=
  if n ∈ P then a n else 0

lemma halasz_smooth_term (f : ℕ → ℂ) (N : ℕ) (s : ℂ) (n : ℕ) :
    LSeries.term (halaszSmoothFunction f N) s n =
      (Nat.smoothNumbers (N + 1)).indicator (LSeries.term f s) n := by
  by_cases hn : n ∈ Nat.smoothNumbers (N + 1) <;>
    simp [LSeries.term, halaszSmoothFunction, hn]

lemma halasz_smooth_LSeries (f : ℕ → ℂ) (N : ℕ) (s : ℂ) :
    LSeries (halaszSmoothFunction f N) s =
      ∑' n : Nat.smoothNumbers (N + 1), LSeries.term f s n := by
  rw [LSeries, _root_.tsum_subtype (Nat.smoothNumbers (N + 1)) (LSeries.term f s)]
  exact tsum_congr (halasz_smooth_term f N s)

lemma halasz_smooth_LSeries_summable (f : ℕ → ℂ) (hf1 : f 1 = 1)
    (hf : ∀ m n, 0 < m → 0 < n → f (m * n) = f m * f n)
    (hbound : OneBounded f) (N : ℕ) (t : ℝ) :
    LSeriesSummable (halaszSmoothFunction f N) (1 + (t : ℂ) * Complex.I) := by
  let s : ℂ := 1 + (t : ℂ) * Complex.I
  have hs : Summable (fun n : Nat.smoothNumbers (N + 1) => LSeries.term f s n) :=
    (mrt_smooth_euler_product f hf1 hf hbound N t).1.of_norm
  have hi : Summable ((Nat.smoothNumbers (N + 1)).indicator (LSeries.term f s)) :=
    (summable_subtype_iff_indicator (s := Nat.smoothNumbers (N + 1))).mp hs
  change Summable (LSeries.term (halaszSmoothFunction f N) s)
  have he : LSeries.term (halaszSmoothFunction f N) s =
      (Nat.smoothNumbers (N + 1)).indicator (LSeries.term f s) :=
    funext (halasz_smooth_term f N s)
  rw [he]
  exact hi

lemma halasz_smooth_function_eq {f : ℕ → ℂ} {N n : ℕ} (hn : 0 < n) (hnN : n ≤ N) :
    halaszSmoothFunction f N n = f n := by
  exact ite_eq_left (Nat.mem_smoothNumbers_of_lt hn (Nat.lt_succ_of_le hnN))

lemma halasz_finite_term (P : Finset ℕ) (a : ℕ → ℂ) (s : ℂ) (n : ℕ) :
    LSeries.term (halaszFiniteCoefficient P a) s n =
      if n ∈ P then LSeries.term a s n else 0 := by
  by_cases hn : n ∈ P <;> simp [halaszFiniteCoefficient, LSeries.term, hn]

lemma halasz_finite_LSeries_summable (P : Finset ℕ) (a : ℕ → ℂ) (s : ℂ) :
    LSeriesSummable (halaszFiniteCoefficient P a) s := by
  apply summable_of_ne_finset_zero (s := P)
  intro n hn
  simp only [halasz_finite_term, hn, ite_false]

lemma halasz_finite_LSeries (P : Finset ℕ) (a : ℕ → ℂ) (s : ℂ) :
    LSeries (halaszFiniteCoefficient P a) s = ∑ n ∈ P, LSeries.term a s n := by
  unfold LSeries
  rw [tsum_eq_sum (s := P) (fun n hn => by simp [halasz_finite_term, hn])]
  exact sum_congr rfl (fun n hn => by simp [halasz_finite_term, hn])

/-- Triangular Perron inversion of the genuine prime-prime-smooth
convolution on Re(s)=1. -/
theorem halasz_smooth_triple_perron (f : ℕ → ℂ) (hf1 : f 1 = 1)
    (hf : ∀ m n, 0 < m → 0 < n → f (m * n) = f m * f n)
    (hbound : OneBounded f) (N : ℕ) (P Q : Finset ℕ) (a b : ℕ → ℂ)
    {x : ℝ} (hx : 0 < x) (hxnat : ∀ n : ℕ, x ≠ (n : ℝ)) :
    (∑ n ∈ Icc 1 ⌊x⌋₊,
      ((halaszFiniteCoefficient P a) ⍟
        ((halaszFiniteCoefficient Q b) ⍟ (halaszSmoothFunction f N))) n *
          ((1 - (n : ℝ) / x : ℝ) : ℂ)) =
      VerticalIntegral' (fun s =>
        (∑ p ∈ P, LSeries.term a s p) * (∑ q ∈ Q, LSeries.term b s q) *
          LSeries (halaszSmoothFunction f N) s * modFivePerronKernel x s) 1 := by
  have hc (t : ℝ) :=
    (halasz_finite_LSeries_summable P a (1 + (t : ℂ) * Complex.I)).convolution
      ((halasz_finite_LSeries_summable Q b (1 + (t : ℂ) * Complex.I)).convolution
        (halasz_smooth_LSeries_summable f hf1 hf hbound N t))
  have hc0 := hc 0
  simp only [Complex.ofReal_zero, zero_mul, add_zero] at hc0
  rw [← modFivePerron_finite_sum _ (x := x) (σ := 1) hx (by norm_num) hc0 hxnat]
  simp only [VerticalIntegral', VerticalIntegral]
  congr 2
  apply integral_congr_ae
  filter_upwards [] with t
  simp only [Complex.ofReal_one]
  rw [LSeries_convolution' (halasz_finite_LSeries_summable P a _)
    ((halasz_finite_LSeries_summable Q b _).convolution
      (halasz_smooth_LSeries_summable f hf1 hf hbound N t)),
    LSeries_convolution' (halasz_finite_LSeries_summable Q b _)
      (halasz_smooth_LSeries_summable f hf1 hf hbound N t),
    halasz_finite_LSeries, halasz_finite_LSeries]
  ring

end TwoPointCorrelations

end OAI
