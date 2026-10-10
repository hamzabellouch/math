import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.OneBounded

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical
open Filter
open Finset Classical Filter
open scoped Topology
open MeasureTheory intervalIntegral
open Finset Nat ArithmeticFunction
open scoped ArithmeticFunction.Moebius
open MeasureTheory Filter
open MeasureTheory
open MeasureTheory Set
open Set MeasureTheory Complex
open Set
open Finset Filter
open ArithmeticFunction
open MeasureTheory Finset
open Classical
open Classical Finset
open Classical Finset Real MeasureTheory
open scoped ContDiff
open Filter Finset

namespace OrdinaryCorrelations.ElliottReductions

def primeDefect (f : ℕ → ℂ) (p : ℕ) : ℝ :=
  if p.Prime then (1 - ‖f p‖) / (p : ℝ) else 0

def normFunction (f : ℕ → ℂ) (n : ℕ) : ℂ := (‖f n‖ : ℂ)

lemma normFunction_oneBounded {f : ℕ → ℂ} (hf : OneBounded f) :
    OneBounded (normFunction f) := by
  intro n
  simpa only [normFunction, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (norm_nonneg _)] using hf n

lemma normFunction_multiplicative {f : ℕ → ℂ} (hm : Multiplicative f) :
    Multiplicative (normFunction f) := by
  intro m n hm0 hn0 hmn
  simp only [normFunction, hm m n hm0 hn0 hmn, norm_mul, Complex.ofReal_mul]

lemma primeDefect_nonneg {f : ℕ → ℂ} (hf : OneBounded f) (p : ℕ) :
    0 ≤ primeDefect f p := by
  unfold primeDefect
  split_ifs
  · exact div_nonneg (sub_nonneg.mpr (hf p)) (Nat.cast_nonneg p)
  · exact le_rfl

lemma primeDefect_sum_le_distanceSq {f : ℕ → ℂ} (hf : OneBounded f)
    {q : ℕ} (χ : DirichletCharacter ℂ q) (t : ℝ) (N : ℕ) :
    (∑ p ∈ range N, primeDefect f p) ≤ distanceSq (normFunction f) χ t (N : ℝ) := by
  unfold distanceSq
  rw [Nat.floor_natCast]
  calc
    _ = ∑ p ∈ (range N).filter Nat.Prime, (1 - ‖f p‖) / (p : ℝ) := by
      simp only [sum_filter, primeDefect]
    _ ≤ ∑ p ∈ (Finset.Icc 2 N).filter Nat.Prime, (1 - ‖f p‖) / (p : ℝ) := by
      apply sum_le_sum_of_subset_of_nonneg
      · intro p hp
        have hp' := mem_filter.mp hp
        exact mem_filter.mpr ⟨mem_Icc.mpr ⟨hp'.2.two_le, (mem_range.mp hp'.1).le⟩, hp'.2⟩
      · intro p hp hn
        exact div_nonneg (sub_nonneg.mpr (hf p)) (Nat.cast_nonneg p)
    _ ≤ _ := by
      apply sum_le_sum
      intro p hp
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg p)
      apply sub_le_sub_left
      apply (Complex.re_le_norm _).trans
      rw [norm_mul]
      have ht : ‖star (χ (p : ZMod q) *
          Complex.exp ((t * Real.log (p : ℝ) : ℝ) * Complex.I))‖ ≤ 1 := by
        rw [norm_star, norm_mul, Complex.norm_exp]
        simp only [Complex.mul_re, Complex.ofReal_re, Complex.I_re, mul_zero,
          Complex.ofReal_im, Complex.I_im, sub_self, Real.exp_zero, mul_one]
        exact χ.norm_le_one _
      simpa only [normFunction, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (norm_nonneg _), mul_one] using
        mul_le_mul_of_nonneg_left ht (norm_nonneg (normFunction f p))

theorem normFunction_nonpretentious_of_divergent_defect {f : ℕ → ℂ}
    (hf : OneBounded f) (hdiv : ¬ Summable (primeDefect f)) :
    UniformlyNonpretentious (normFunction f) := by
  have hsum := (not_summable_iff_tendsto_nat_atTop_of_nonneg
    (primeDefect_nonneg hf)).mp hdiv
  intro q hq χ
  apply tendsto_atTop.mpr
  intro b
  filter_upwards [hsum.eventually (eventually_ge_atTop ((max b 0)^2))] with N hN
  apply le_csInf
  · exact ⟨distance (normFunction f) χ 0 (N : ℝ),
      ⟨0, ⟨neg_nonpos.mpr (Nat.cast_nonneg N), Nat.cast_nonneg N⟩, rfl⟩⟩
  · rintro x ⟨t, ht, rfl⟩
    calc
      b ≤ max b 0 := le_max_left b 0
      _ = Real.sqrt ((max b 0)^2) := (Real.sqrt_sq (le_max_right b 0)).symm
      _ ≤ distance (normFunction f) χ t (N : ℝ) :=
        Real.sqrt_le_sqrt (hN.trans (primeDefect_sum_le_distanceSq hf χ t N))

end OrdinaryCorrelations.ElliottReductions

end

end OAI
