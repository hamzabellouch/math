import OAI.Analysis.CircleDomains.Probability.DensityMassBound
import Mathlib.MeasureTheory.Measure.Prod

namespace OAI

/-! The two-sided kernel estimate used for local domain meetings. The
reference measure and kernel will be the spherical area and the normalized
small-ball indicator; no boundedness of the occupation densities is needed. -/

open Set Function MeasureTheory
open scoped ENNReal

noncomputable section
namespace CircleDomainRigidity

variable {X : Type*} [MeasurableSpace X]

theorem pair_kernel_energy_bound (σ : Measure X) [SFinite σ]
    (K : X × X → ℝ≥0∞) (hK : Measurable K)
    (g h : X → ℝ≥0∞) (hg : Measurable g) (hh : Measurable h)
    {C E : ℝ≥0∞}
    (hrow : ∀ x, (∫⁻ y, K (x, y) ∂σ) ≤ C)
    (hcol : ∀ y, (∫⁻ x, K (x, y) ∂σ) ≤ C)
    (hgE : (∫⁻ x, g x ^ 2 ∂σ) ≤ E)
    (hhE : (∫⁻ x, h x ^ 2 ∂σ) ≤ E) :
    (∫⁻ p, K p * (g p.1 * h p.2) ∂σ.prod σ) ≤ C * E := by
  let ν := (σ.prod σ).withDensity K
  have hgg : Measurable (fun p : X × X => g p.1 ^ 2) :=
    (hg.comp measurable_fst).pow_const 2
  have hhh : Measurable (fun p : X × X => h p.2 ^ 2) :=
    (hh.comp measurable_snd).pow_const 2
  have hG : (∫⁻ p, g p.1 ^ 2 ∂ν) ≤ C * E := by
    rw [show ν = (σ.prod σ).withDensity K from rfl,
      lintegral_withDensity_eq_lintegral_mul _ hK hgg,
      lintegral_prod _ (hK.mul hgg).aemeasurable]
    calc
      _ = ∫⁻ x, (∫⁻ y, K (x, y) ∂σ) * g x ^ 2 ∂σ := by
        apply lintegral_congr
        intro x
        simpa only [Pi.mul_apply, Function.comp_def, id_eq] using
          (lintegral_mul_const (μ := σ) (g x ^ 2)
            (hK.comp (measurable_const.prodMk measurable_id)))
      _ ≤ ∫⁻ x, C * g x ^ 2 ∂σ :=
        lintegral_mono fun x => mul_le_mul' (hrow x) le_rfl
      _ = C * ∫⁻ x, g x ^ 2 ∂σ := lintegral_const_mul _ (hg.pow_const 2)
      _ ≤ C * E := mul_le_mul' le_rfl hgE
  have hH : (∫⁻ p, h p.2 ^ 2 ∂ν) ≤ C * E := by
    rw [show ν = (σ.prod σ).withDensity K from rfl,
      lintegral_withDensity_eq_lintegral_mul _ hK hhh,
      lintegral_prod_symm _ (hK.mul hhh).aemeasurable]
    calc
      _ = ∫⁻ y, (∫⁻ x, K (x, y) ∂σ) * h y ^ 2 ∂σ := by
        apply lintegral_congr
        intro y
        simpa only [Pi.mul_apply, Function.comp_def, id_eq] using
          (lintegral_mul_const (μ := σ) (h y ^ 2)
            (hK.comp (measurable_id.prodMk measurable_const)))
      _ ≤ ∫⁻ y, C * h y ^ 2 ∂σ :=
        lintegral_mono fun y => mul_le_mul' (hcol y) le_rfl
      _ = C * ∫⁻ y, h y ^ 2 ∂σ := lintegral_const_mul _ (hh.pow_const 2)
      _ ≤ C * E := mul_le_mul' le_rfl hhE
  have hconj : (2 : ℝ).HolderConjugate 2 :=
    Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩
  have hCS := ENNReal.lintegral_mul_le_Lp_mul_Lq ν hconj
    (hg.comp measurable_fst).aemeasurable (hh.comp measurable_snd).aemeasurable
  have hCS' : (∫⁻ p, g p.1 * h p.2 ∂ν) ≤
      (∫⁻ p, g p.1 ^ 2 ∂ν) ^ (1 / 2 : ℝ) *
      (∫⁻ p, h p.2 ^ 2 ∂ν) ^ (1 / 2 : ℝ) := by
    simpa only [Pi.mul_apply, Function.comp_def, ENNReal.rpow_two] using hCS
  have hid : (∫⁻ p, g p.1 * h p.2 ∂ν) =
      ∫⁻ p, K p * (g p.1 * h p.2) ∂σ.prod σ :=
    lintegral_withDensity_eq_lintegral_mul _ hK
      (show Measurable (fun p : X × X => g p.1 * h p.2) from
        (hg.comp measurable_fst).mul (hh.comp measurable_snd))
  rw [← hid]
  apply hCS'.trans
  calc
    _ ≤ (C * E) ^ (1 / 2 : ℝ) * (C * E) ^ (1 / 2 : ℝ) :=
      mul_le_mul' (ENNReal.rpow_le_rpow hG (by norm_num))
        (ENNReal.rpow_le_rpow hH (by norm_num))
    _ = C * E := by rw [← sq, ← ENNReal.rpow_two, ← ENNReal.rpow_mul]; norm_num

end CircleDomainRigidity

end

end OAI
