import Mathlib

namespace OAI

section
section
noncomputable section
open MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace LogConcaveSampling
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

lemma natural_moment_norm {f : Ω → ℝ} (hf : ∀x,0 ≤ f x) {n : ℕ} (hn : 0<n) :
    eLpNorm' f (n:ℝ) μ ^ n = ∫⁻x,ENNReal.ofReal (f x)^n ∂μ := by
  rw [eLpNorm'_eq_lintegral_enorm, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul,
    one_div, inv_mul_cancel₀ (show (n : ℝ) ≠ 0 by exact_mod_cast hn.ne'),
    ENNReal.rpow_one]
  simp only [ENNReal.rpow_natCast, Real.enorm_eq_ofReal_abs, abs_of_nonneg (hf _)]

lemma norm_le_iff_natural_moment {f : Ω → ℝ} (hf : ∀x,0 ≤ f x) {n : ℕ} (hn : 0<n)
    (B : ℝ≥0∞) :
    eLpNorm' f (n:ℝ) μ  ≤  B ↔ (∫⁻x,ENNReal.ofReal (f x)^n ∂μ)  ≤  B^n := by
  rw [←natural_moment_norm hf hn]
  simpa only [ENNReal.rpow_natCast] using
    (ENNReal.rpow_le_rpow_iff (show (0:ℝ)<n by exact_mod_cast hn)).symm

lemma natural_moment_sum {ι : Type*} [Fintype ι] (f : ι → Ω → ℝ)
    (hf : ∀i,AEStronglyMeasurable (f i) μ) (hf0 : ∀i x,0 ≤ f i x)
    {n : ℕ} (hn : 0<n) (B : ι → ℝ≥0∞)
    (hB : ∀i,(∫⁻x,ENNReal.ofReal (f i x)^n ∂μ)  ≤  B i^n) :
    (∫⁻x,ENNReal.ofReal (∑i,f i x)^n ∂μ)  ≤  (∑i,B i)^n := by
  apply (norm_le_iff_natural_moment (fun x => Finset.sum_nonneg (fun i _ => hf0 i x)) hn _).mp
  have hnorm {g : Ω → ℝ} (hg : AEStronglyMeasurable g μ) :
      eLpNorm g (n : ℝ≥0∞) μ = eLpNorm' g (n : ℝ) μ := by
    simpa only [ENNReal.coe_natCast, NNReal.coe_natCast] using
      (eLpNorm_nnreal_eq_eLpNorm' (p := (n : ℝ≥0)) (by exact_mod_cast hn.ne') hg)
  rw [← hnorm (Finset.univ.aestronglyMeasurable_fun_sum (fun i _ => hf i))]
  have hsum := eLpNorm_sum_le (μ:=μ) (s:=Finset.univ) (f:=f)
    (show 1 ≤ (n:ℝ≥0∞) by exact_mod_cast hn)
  have he : (fun x => ∑i,f i x)=∑i,f i := by ext x; simp
  rw [he]
  apply hsum.trans
  apply Finset.sum_le_sum
  intro i _
  rw [hnorm (hf i)]
  exact (norm_le_iff_natural_moment (hf0 i) hn _).mpr (hB i)

lemma natural_moment_lower {f : Ω → ℝ} [IsProbabilityMeasure μ]
    (hf : AEStronglyMeasurable f μ) (hf0 : ∀x,0 ≤ f x)
    {n m : ℕ} (hn : 0<n) (hnm : n ≤ m) (B : ℝ≥0∞)
    (hB : (∫⁻x,ENNReal.ofReal (f x)^m ∂μ)  ≤  B^m) :
    (∫⁻x,ENNReal.ofReal (f x)^n ∂μ)  ≤  B^n := by
  apply (norm_le_iff_natural_moment hf0 hn B).mp
  have hnorm (degree : ℕ) (hdegree : 0 < degree) :
      eLpNorm f (degree : ℝ≥0∞) μ = eLpNorm' f (degree : ℝ) μ := by
    simpa only [ENNReal.coe_natCast, NNReal.coe_natCast] using
      (eLpNorm_nnreal_eq_eLpNorm' (p := (degree : ℝ≥0))
        (by exact_mod_cast hdegree.ne') hf)
  rw [← hnorm n hn]
  have hbound := (norm_le_iff_natural_moment hf0 (hn.trans_le hnm) B).mpr hB
  rw [← hnorm m (hn.trans_le hnm)] at hbound
  exact (eLpNorm_le_eLpNorm_of_exponent_le
    (show (n:ℝ≥0∞) ≤ (m:ℝ≥0∞) by exact_mod_cast hnm)).trans hbound

end LogConcaveSampling

end

end

end

end OAI
