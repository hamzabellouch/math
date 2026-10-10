import Mathlib
import OAI.Geometry.TamingCompatibility.Functional.FourierCutoff

namespace OAI

section
section
section
section
noncomputable section
open MeasureTheory
open scoped BoundedContinuousFunction
noncomputable section
open MeasureTheory FourierTransform
open scoped BoundedContinuousFunction RealInnerProductSpace ENNReal
namespace TamingCompatibility.FourierCutoff

variable {E F K : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
  [MetricSpace K] [CompactSpace K]

lemma pairing_modulate_eq_inverse (g : Lp ℂ 2 (volume : Measure E))
    (u : Lp F 2 (volume : Measure E)) (x : E) :
    pairing (modulate g x) u = Real.Lp.fourierTransformInv (multiply g u) x := by
  change L1.integralCLM' ℂ (modulate g x • u) = _
  rw [← L1.integral_eq' ℂ, L1.integral_eq_integral, Real.Lp.fourierTransformInv_apply, Real.fourierInv_eq]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_lpSMul (r := (1 : ℝ≥0∞)) (modulate g x) u,
    Lp.coeFn_lpSMul (r := (1 : ℝ≥0∞)) g u, modulate_coe g x] with ξ h1 h2 h3
  change _ = (Real.fourierChar ⟪ξ,x⟫ : ℂ) • (g • u : Lp F 1 (volume : Measure E)) ξ
  rw [h1, h2]
  change modulate g x ξ • u ξ = (Real.fourierChar ⟪ξ,x⟫ : ℂ) • (g ξ • u ξ)
  rw [h3, mul_smul]

def kernel (loc : C(K,E)) (g : Lp ℂ 2 (volume : Measure E))
    {R : ℝ} (hR : 0 ≤ R) (hg : ∀ᵐ ξ ∂volume, R < ‖ξ‖ → g ξ = 0) :
    K →ᵇ (Lp F 2 (volume : Measure E) →L[ℂ] F) :=
  .mkOfCompact ⟨fun x => pairingCLM (modulate g (loc x)),
    pairingCLM.continuous.comp ((continuous_modulate g hR hg).comp loc.continuous)⟩

theorem compact_inverse_cutoff [ProperSpace F] (loc : C(K,E))
    (g : Lp ℂ 2 (volume : Measure E)) {R : ℝ} (hR : 0 ≤ R)
    (hg : ∀ᵐ ξ ∂volume, R < ‖ξ‖ → g ξ = 0) :
    IsCompactOperator (CompactKernel.operator (kernel (F := F) loc g hR hg)) :=
  CompactKernel.compact_operator _

lemma inverse_cutoff_apply (loc : C(K,E)) (g : Lp ℂ 2 (volume : Measure E))
    {R : ℝ} (hR : 0 ≤ R) (hg : ∀ᵐ ξ ∂volume, R < ‖ξ‖ → g ξ = 0)
    (u : Lp F 2 (volume : Measure E)) (x : K) :
    CompactKernel.operator (kernel loc g hR hg) u x =
      Real.Lp.fourierTransformInv (multiply g u) (loc x) :=
  pairing_modulate_eq_inverse g u (loc x)

end TamingCompatibility.FourierCutoff

end
end

noncomputable section
open MeasureTheory FourierTransform
open scoped SchwartzMap BoundedContinuousFunction RealInnerProductSpace ENNReal ContDiff

namespace TamingCompatibility.FourierIdentification

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

lemma ae_eq_of_distribution_eq {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (f : Lp F p (volume : Measure E)) (g : Lp F q (volume : Measure E))
    (h : (f : 𝓢'(E,F)) = (g : 𝓢'(E,F))) : f =ᵐ[volume] g := by
  apply ae_eq_of_integral_contDiff_smul_eq
    ((Lp.memLp f).locallyIntegrable (Fact.out : 1 ≤ p))
    ((Lp.memLp g).locallyIntegrable (Fact.out : 1 ≤ q))
  intro φ hφ hc
  have hc' : HasCompactSupport (Complex.ofRealCLM ∘ φ) := hc.comp_left rfl
  have hd' : ContDiff ℝ ∞ (Complex.ofRealCLM ∘ φ) := by fun_prop
  have heq := congrArg (fun u : 𝓢'(E,F) => u (hc'.toSchwartzMap hd')) h
  simpa using heq

lemma integral_inverse_smul_swap {f : E → ℂ} {g : E → F}
    (hf : Integrable f) (hg : Integrable g) :
    (∫ x, 𝓕⁻ f x • g x) = ∫ x, f x • 𝓕⁻ g x := by
  simpa [FourierTransformInv.fourierInv, VectorFourier.fourierIntegral,
    real_inner_comm] using
    (VectorFourier.integral_fourierIntegral_smul_eq_flip (L := -(innerₗ E))
      Real.continuous_fourierChar (by
        change Continuous (fun p : E × E => -⟪p.1,p.2⟫)
        exact continuous_inner.neg) hf hg)

def inverseTop (f : Lp F 1 (volume : Measure E)) : Lp F ⊤ (volume : Measure E) :=
  ((Real.Lp.fourierTransformInv f).memLp_top (μ := volume)).toLp _

omit [CompleteSpace F] in
lemma inverseTop_coe (f : Lp F 1 (volume : Measure E)) :
    inverseTop f =ᵐ[volume] Real.Lp.fourierTransformInv f :=
  ((Real.Lp.fourierTransformInv f).memLp_top (μ := volume)).coeFn_toLp

lemma inverseTop_to_distribution (f : Lp F 1 (volume : Measure E)) :
    𝓕⁻ (f : 𝓢'(E,F)) = (inverseTop f : 𝓢'(E,F)) := by
  ext φ
  simp only [TemperedDistribution.fourierInv_apply, Lp.toTemperedDistribution_apply]
  calc
    (∫ x, 𝓕⁻ φ x • f x) = ∫ x, φ x • Real.Lp.fourierTransformInv f x := by
      simpa only [SchwartzMap.fourierInv_coe, Real.Lp.fourierTransformInv_apply] using
        integral_inverse_smul_swap φ.integrable (L1.integrable_coeFn f)
    _ = ∫ x, φ x • inverseTop f x := by
      apply integral_congr_ae
      filter_upwards [inverseTop_coe f] with x hx
      rw [hx]

lemma distribution_eq_of_ae_eq {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (f : Lp F p (volume : Measure E)) (g : Lp F q (volume : Measure E))
    (h : f =ᵐ[volume] g) : (f : 𝓢'(E,F)) = (g : 𝓢'(E,F)) := by
  ext φ
  simp only [Lp.toTemperedDistribution_apply]
  apply integral_congr_ae
  filter_upwards [h] with x hx
  rw [hx]

end TamingCompatibility.FourierIdentification

namespace TamingCompatibility.FourierIdentification
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem inverse_L1_L2 (f : Lp F 1 (volume : Measure E))
    (g : Lp F 2 (volume : Measure E)) (h : f =ᵐ[volume] g) :
    Real.Lp.fourierTransformInv f =ᵐ[volume] (𝓕⁻ g : Lp F 2 (volume : Measure E)) := by
  apply (inverseTop_coe f).symm.trans
  apply ae_eq_of_distribution_eq
  rw [← inverseTop_to_distribution, distribution_eq_of_ae_eq f g h,
    Lp.fourierInv_toTemperedDistribution_eq]

end TamingCompatibility.FourierIdentification

end

noncomputable section
open MeasureTheory
open scoped ENNReal

end
end
end
end
end

end OAI
