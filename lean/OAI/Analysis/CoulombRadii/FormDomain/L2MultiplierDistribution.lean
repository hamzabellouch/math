import Mathlib

namespace OAI

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set
open scoped BigOperators ENNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open scoped Classical
open scoped BigOperators ComplexConjugate
open scoped Classical
open scoped Classical
open MeasureTheory Set Filter
open scoped Classical ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Filter
open scoped ENNReal NNReal FourierTransform SchwartzMap LineDeriv ComplexConjugate
namespace Coulomb
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma l2_multiplier_distribution {u w : Lp ℂ 2 (volume : Measure E)} (a : E)
    (hw : w =ᵐ[volume] fun ξ => (2 * Real.pi * Complex.I) *
      (inner ℝ ξ a : ℂ) * u ξ) :
    (w : 𝓢'(E,ℂ)) = (2 * Real.pi * Complex.I) •
      TemperedDistribution.smulLeftCLM ℂ (fun ξ => (inner ℝ ξ a : ℂ)) (u : 𝓢'(E,ℂ)) := by
  have ht : (fun ξ => (inner ℝ ξ a : ℂ)).HasTemperateGrowth := by fun_prop
  ext φ
  change Lp.toTemperedDistribution w φ = (2 * Real.pi * Complex.I) •
    Lp.toTemperedDistribution u (SchwartzMap.smulLeftCLM ℂ (fun ξ => (inner ℝ ξ a : ℂ)) φ)
  simp only [Lp.toTemperedDistribution_apply]
  rw [← integral_smul]
  apply integral_congr_ae
  filter_upwards [hw] with ξ hξ
  simp only [hξ, SchwartzMap.smulLeftCLM_apply ht, smul_eq_mul]
  ring

lemma l2_fourier_weakDeriv_distribution {u w : Lp ℂ 2 (volume : Measure E)} (a : E)
    (hw : w =ᵐ[volume] fun ξ => (2 * Real.pi * Complex.I) *
      (inner ℝ ξ a : ℂ) * (𝓕 u : Lp ℂ 2 (volume : Measure E)) ξ) :
    ∂_{a} (u : 𝓢'(E,ℂ)) = (𝓕⁻ w : Lp ℂ 2 (volume : Measure E)) := by
  have h := l2_multiplier_distribution a hw
  rw [← Lp.fourier_toTemperedDistribution_eq u,
    ← TemperedDistribution.fourier_lineDerivOp_eq] at h
  have H := congrArg (fun z : 𝓢'(E,ℂ) => 𝓕⁻ z) h
  simpa only [Lp.fourierInv_toTemperedDistribution_eq,
    FourierTransform.fourierInv_fourier_eq] using H.symm

lemma l2_fourier_weakDeriv {u w : Lp ℂ 2 (volume : Measure E)} (a : E)
    (hw : w =ᵐ[volume] fun ξ => (2 * Real.pi * Complex.I) *
      (inner ℝ ξ a : ℂ) * (𝓕 u : Lp ℂ 2 (volume : Measure E)) ξ)
    (φ : E → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφC : HasCompactSupport φ) :
    (∫ x : E, (fderiv ℝ φ x a : ℂ) * u x) =
      -(∫ x : E, (φ x : ℂ) * (𝓕⁻ w : Lp ℂ 2 (volume : Measure E)) x) := by
  let φc : E → ℂ := fun x => (φ x : ℂ)
  have hφc : ContDiff ℝ (⊤ : ℕ∞) φc := Complex.ofRealCLM.contDiff.comp hφ
  have hφcC : HasCompactSupport φc := hφC.comp_left Complex.ofReal_zero
  let Φ : 𝓢(E,ℂ) := hφcC.toSchwartzMap hφc
  have h := congrArg (fun T : 𝓢'(E,ℂ) => T Φ) (l2_fourier_weakDeriv_distribution a hw)
  have hd (x : E) : (∂_{a} Φ) x = (fderiv ℝ φ x a : ℂ) := by
    rw [SchwartzMap.lineDerivOp_apply_eq_fderiv]
    change fderiv ℝ φc x a = _
    exact congrArg (fun L : E →L[ℝ] ℂ => L a)
      ((Complex.ofRealCLM.hasFDerivAt.comp x
        ((hφ.differentiable (by simp)) x).hasFDerivAt).fderiv)
  simp only [TemperedDistribution.lineDerivOp_apply_apply, map_neg,
    Lp.toTemperedDistribution_apply, smul_eq_mul] at h
  have h' : -(∫ x : E, (fderiv ℝ φ x a : ℂ) * u x) =
      ∫ x : E, (φ x : ℂ) * (𝓕⁻ w : Lp ℂ 2 (volume : Measure E)) x := by
    have hp (x : E) : Φ x = (φ x : ℂ) := rfl
    simpa only [hd, hp] using h
  simpa only [neg_neg] using congrArg Neg.neg h'

lemma fourierMultiplier_norm_sq (r : ℝ) (z : ℂ) :
    ‖(2 * Real.pi * Complex.I) * (r : ℂ) * z‖^2 = (2*Real.pi*r)^2 * ‖z‖^2 := by
  have he : (2 * Real.pi * Complex.I) * (r : ℂ) * z =
      ((2*Real.pi*r : ℝ) : ℂ) * Complex.I * z := by push_cast; ring
  rw [he, norm_mul, norm_mul, Complex.norm_real, Complex.norm_I, mul_one, mul_pow]
  rw [Real.norm_eq_abs, sq_abs]

lemma l2_norm_sq_fourier (u : Lp ℂ 2 (volume : Measure E)) :
    ‖u‖^2 = ∫ y, ‖u y‖^2 := by
  rw [@norm_sq_eq_re_inner ℂ, L2.inner_def, ← integral_re (L2.integrable_inner u u)]
  apply integral_congr_ae
  filter_upwards [] with y
  simp [inner_self_eq_norm_sq_to_K, ← Complex.ofReal_pow]

lemma l2_fourier_weighted_derivative (u : Lp ℂ 2 (volume : Measure E)) (a : E)
    (hI : Integrable (fun ξ => (2*Real.pi*inner ℝ ξ a)^2 *
      ‖(𝓕 u : Lp ℂ 2 (volume : Measure E)) ξ‖^2)) :
    ∃ g : Lp ℂ 2 (volume : Measure E),
      (∀ (φ : E → ℝ), ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        (∫ x : E, (fderiv ℝ φ x a : ℂ) * u x) = -(∫ x : E, (φ x : ℂ) * g x)) ∧
      ‖g‖^2 = ∫ ξ, (2*Real.pi*inner ℝ ξ a)^2 *
        ‖(𝓕 u : Lp ℂ 2 (volume : Measure E)) ξ‖^2 := by
  let F : E → ℂ := fun ξ => (2 * Real.pi * Complex.I) * (inner ℝ ξ a : ℂ) *
    (𝓕 u : Lp ℂ 2 (volume : Measure E)) ξ
  have hm : AEStronglyMeasurable F volume := by
    exact (by fun_prop : Continuous (fun ξ => (2 * Real.pi * Complex.I) *
      (inner ℝ ξ a : ℂ))).aestronglyMeasurable.mul (Lp.aestronglyMeasurable _)
  have hF : MemLp F 2 volume := by
    apply (memLp_two_iff_integrable_sq_norm hm).mpr
    simpa only [F, fourierMultiplier_norm_sq] using hI
  refine ⟨𝓕⁻ (hF.toLp F), ?_, ?_⟩
  · intro φ hφ hφC
    exact l2_fourier_weakDeriv a hF.coeFn_toLp φ hφ hφC
  · change ‖(Lp.fourierTransformₗᵢ E ℂ).symm (hF.toLp F)‖^2 = _
    rw [(Lp.fourierTransformₗᵢ E ℂ).symm.norm_map, l2_norm_sq_fourier]
    apply integral_congr_ae
    filter_upwards [hF.coeFn_toLp] with ξ hξ
    rw [hξ]
    exact fourierMultiplier_norm_sq _ _
end Coulomb

open scoped LineDeriv

end

end OAI
