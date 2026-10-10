import OAI.Analysis.KadisonKastler.ScalarWeakLimit
import OAI.Analysis.KadisonKastler.ScalarShiftCesaro

namespace OAI

/-! # Positivity of scalar averages and their weak limit -/

namespace KadisonKastler

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators

def scalarPositiveCone : Set ℂ := {z | z.im = 0 ∧ 0 ≤ z.re}

theorem scalarPositiveCone_isClosed : IsClosed scalarPositiveCone :=
  (isClosed_eq Complex.continuous_im continuous_const).inter
    (isClosed_le continuous_const Complex.continuous_re)

theorem scalarPositiveCone_convex : Convex ℝ scalarPositiveCone := by
  intro z hz w hw a b ha hb _hab
  change (a • z + b • w).im = 0 ∧ 0 ≤ (a • z + b • w).re
  simp only [Complex.add_im, Complex.smul_im, Complex.add_re, Complex.smul_re,
    smul_eq_mul, hz.1, hw.1, mul_zero, add_zero]
  exact ⟨trivial, add_nonneg (mul_nonneg ha hz.2) (mul_nonneg hb hw.2)⟩

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

def ScalarNonnegative (f : ScalarLInfinity μ) : Prop :=
  ∀ᵐ x ∂μ, f x ∈ scalarPositiveCone

theorem scalarNonnegative_pullback (T : X → X)
    (hT : Measure.QuasiMeasurePreserving T μ μ) {f : ScalarLInfinity μ}
    (hf : ScalarNonnegative f) : ScalarNonnegative (scalarInfinityPullback T hT f) := by
  filter_upwards [scalarInfinityPullback_ae T hT f, hT.ae hf] with x hx hp
  rwa [hx]

theorem scalarNonnegative_real_smul {f : ScalarLInfinity μ} (hf : ScalarNonnegative f)
    {c : ℝ} (hc : 0 ≤ c) : ScalarNonnegative ((c : ℂ) • f) := by
  filter_upwards [Lp.coeFn_smul (c : ℂ) f, hf] with x hx hp
  simp only [Pi.smul_apply] at hx
  rw [hx]
  change (((c : ℂ) * f x).im = 0 ∧ 0 ≤ ((c : ℂ) * f x).re)
  simp only [Complex.mul_im, Complex.mul_re, Complex.ofReal_im, Complex.ofReal_re,
    hp.1, mul_zero, zero_mul, add_zero, sub_zero]
  exact ⟨trivial, mul_nonneg hc hp.2⟩

theorem scalarNonnegative_sum (s : Finset ℕ) (f : ℕ → ScalarLInfinity μ)
    (hf : ∀ n, ScalarNonnegative (f n)) : ScalarNonnegative (∑ n ∈ s, f n) := by
  filter_upwards [Lp.coeFn_finsetSum s f, ae_all_iff.mpr hf] with x hx hp
  have he : (∑ n ∈ s, f n) x = ∑ n ∈ s, f n x := by
    simpa only [Finset.sum_apply] using hx
  rw [he]
  constructor
  · change Complex.imLm (∑ n ∈ s, f n x) = 0
    rw [map_sum]
    exact Finset.sum_eq_zero (fun n _ => (hp n).1)
  · change 0 ≤ Complex.reLm (∑ n ∈ s, f n x)
    rw [map_sum]
    exact Finset.sum_nonneg (fun n _ => (hp n).2)

theorem scalarNonnegative_pullback_power (S : X → X)
    (hS : Measure.QuasiMeasurePreserving S μ μ) [IsFiniteMeasure μ]
    {f : ScalarLInfinity μ} (hf : ScalarNonnegative f) (i : ℕ) :
    ScalarNonnegative (((scalarInfinityPullbackL S hS) ^ i) f) := by
  induction i with
  | zero => simpa using hf
  | succ i hi =>
    rw [pow_succ', mul_apply_eq_comp]
    exact scalarNonnegative_pullback S hS hi

theorem scalarNonnegative_weighted_sum (F : ℕ → ScalarLInfinity μ)
    (hF : ∀ i, ScalarNonnegative (F i)) (s : Finset ℕ) (c : ℝ) (hc : 0 ≤ c) :
    ScalarNonnegative ((c : ℂ) • ∑ i ∈ s, F i) :=
  scalarNonnegative_real_smul (μ := μ) (f := ∑ i ∈ s, F i) (c := c)
    (scalarNonnegative_sum s F hF) hc

theorem scalarNonnegative_shiftCesaro (S : X → X)
    (hS : Measure.QuasiMeasurePreserving S μ μ) [IsFiniteMeasure μ]
    {f : ScalarLInfinity μ} (hf : ScalarNonnegative f) (n : ℕ) :
    ScalarNonnegative (scalarShiftCesaro S hS n f) := by
  let U : ScalarLInfinity μ →L[ℂ] ScalarLInfinity μ := scalarInfinityPullbackL S hS
  have hp : ∀ i : ℕ, ScalarNonnegative ((U ^ i) f) := by
    intro i
    exact scalarNonnegative_pullback_power S hS (f := f) hf i
  have hh := scalarNonnegative_weighted_sum (μ := μ) (fun i => (U ^ i) f) hp
    (Finset.range (n + 1)) (((n + 1 : ℕ) : ℝ)⁻¹)
    (inv_nonneg.mpr (Nat.cast_nonneg (n + 1)))
  rw [scalarShiftCesaro_apply]
  simpa only [U, Complex.ofReal_inv] using hh

variable [IsProbabilityMeasure μ]

theorem scalarNonnegative_of_weak_limit {ι : Type*} {l : Filter ι} [l.NeBot]
    (f : ι → ScalarLInfinity μ) (b : ScalarLInfinity μ)
    (hf : ∀ i, ScalarNonnegative (f i))
    (ht : ∀ y, Tendsto (fun i => inner ℂ y (scalarInfinityToL2 (f i))) l
      (𝓝 (inner ℂ y (scalarInfinityToL2 b)))) : ScalarNonnegative b := by
  have hp (i : ι) : ∀ᵐ x ∂μ, scalarInfinityToL2 (f i) x ∈ scalarPositiveCone := by
    filter_upwards [scalarInfinityToL2_ae (f i), hf i] with x hx hf
    rwa [hx]
  have hl := L2_ae_mem_of_inner_tendsto scalarPositiveCone_isClosed scalarPositiveCone_convex
    (fun i => scalarInfinityToL2 (f i)) (scalarInfinityToL2 b) hp ht
  filter_upwards [scalarInfinityToL2_ae b, hl] with x hx hl
  rwa [← hx]

end

end KadisonKastler

end OAI
