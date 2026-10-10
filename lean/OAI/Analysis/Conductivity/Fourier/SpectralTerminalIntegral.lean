import Mathlib
import OAI.Analysis.Conductivity.Fourier.SpectralTerminalL2
import OAI.Analysis.Conductivity.Sources.FluxCylinder

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory Matrix UnitAddTorus
open scoped ENNReal
local instance spectralTerminalIntegralMeasureSpace : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance spectralTerminalIntegralIsProbabilityMeasure : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

lemma spectralTerminalDensity_coeff (s : Fin 3 → ℝ) {R : ℝ} (hR : 0<R)
    (f : spectralTraceGraph (torusRate s)) (h : TorusModes) :
    spectralTerminalDensity s hR f h=
      (torusRate s h:ℂ)*(Real.exp (-torusRate s h*R):ℂ)*f.val 0 h := by
  change ((Real.sqrt (torusRate s h)*Real.exp (-torusRate s h*R):ℝ):ℂ)*f.val 1 h=_
  rw [f.property h]
  have he : (Real.sqrt (torusRate s h):ℂ)^2=(torusRate s h:ℂ) := by
    exact_mod_cast Real.sq_sqrt (Real.sqrt_nonneg _)
  simp only [Complex.ofReal_mul]
  calc
    _ = (Real.sqrt (torusRate s h):ℂ)^2*(Real.exp (-torusRate s h*R):ℂ)*f.val 0 h := by ring
    _ = _ := by rw [he]

lemma spectralTerminalDensity_synthesis_ae {s : Fin 3 → ℝ}
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    {R : ℝ} (hR : 0<R) (f : spectralTraceGraph (torusRate s)) :
    (mFourierBasis (d:=Fin 2)).repr.symm (spectralTerminalDensity s hR f)=ᵐ[volume]
      fun θ => -endPoissonField s f 1 (R,θ) := by
  let u := (mFourierBasis (d:=Fin 2)).repr.symm (spectralTerminalDensity s hR f)
  have hc (h : TorusModes) : mFourierCoeff u h=spectralTerminalDensity s hR f h := by
    rw [←mFourierBasis_repr]
    change (mFourierBasis (d:=Fin 2)).repr ((mFourierBasis (d:=Fin 2)).repr.symm _) h=_
    rw [LinearIsometryEquiv.apply_symm_apply]
  apply lp_hasSum_ae_unique (hasSum_mFourier_series_L2 u)
    (a:=fun h θ => -endPoissonModeField s h (f.val 0 h) 1 (R,θ))
  · intro h
    filter_upwards [Lp.coeFn_smul (mFourierCoeff u h) (mFourierLp 2 h),coeFn_mFourierLp 2 h]
      with θ h1 h2
    rw [h1]
    simp only [Pi.smul_apply,smul_eq_mul,h2,hc,spectralTerminalDensity_coeff]
    simp [endPoissonModeField,endModeCoefficient,mul_assoc,mul_left_comm,mul_comm]
  · exact Filter.Eventually.of_forall (fun θ => (endPoissonField_hasSum s hs f 1 hR).neg)

lemma smoothCollarTrace_mean_integral (s : Fin 3 → ℝ) (b : ℝ)
    {φ : Coord3 → ℝ} (hφ : ContDiff ℝ (↑(⊤:ℕ∞)) φ) :
    spectralGraphMean (torusRate s) (smoothCollarTrace s b hφ)=
      ∫ θ,φ (sourceAngularCollar b θ) := by
  change ((smoothCollarTrace s b hφ).val 0 0).re=_
  rw [smoothCollarTrace_fst]
  simp only [mFourierCoeff,neg_zero,mFourier_zero,ContinuousMap.one_apply,one_smul]
  have hc : Continuous (fun θ => (φ (sourceAngularCollar b θ):ℂ)) :=
    Complex.continuous_ofReal.comp (hφ.continuous.comp (continuous_sourceAngularCollar b))
  simpa using (Complex.reCLM.integral_comp_comm
    (hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))).symm

lemma spectralTerminalDensity_smooth_pair {s : Fin 3 → ℝ}
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    {R : ℝ} (hR : 0<R) (f : spectralTraceGraph (torusRate s)) (b : ℝ)
    {φ : Coord3 → ℝ} (hφ : ContDiff ℝ (↑(⊤:ℕ∞)) φ) :
    Integrable (fun θ => (endPoissonField s f 1 (R,θ)).re*φ (sourceAngularCollar b θ)) ∧
    (∫ θ,(endPoissonField s f 1 (R,θ)).re*φ (sourceAngularCollar b θ))=
      -(spectralWeightedPairL s (spectralEndWeight s R f) (smoothCollarTrace s b hφ)).re := by
  let u := (mFourierBasis (d:=Fin 2)).repr.symm (spectralTerminalDensity s hR f)
  let v := torusSpectralSynthesis s (smoothCollarTrace s b hφ)
  have hi := L2.integrable_inner (𝕜:=ℂ) u v
  have he : (fun θ => -(inner ℂ (u θ) (v θ)).re)=ᵐ[volume]
      (fun θ => (endPoissonField s f 1 (R,θ)).re*φ (sourceAngularCollar b θ)) := by
    filter_upwards [spectralTerminalDensity_synthesis_ae hs hR f,
      torusSpectralSynthesis_smoothCollar_ae s b hφ] with θ hu hv
    change -(inner ℂ (((mFourierBasis (d:=Fin 2)).repr.symm (spectralTerminalDensity s hR f)) θ)
      (torusSpectralSynthesis s (smoothCollarTrace s b hφ) θ)).re=_
    rw [hu,hv]
    simp [RCLike.inner_apply,Complex.mul_re,mul_comm]
  refine ⟨hi.re.neg.congr he,?_⟩
  rw [←integral_congr_ae he,integral_neg]
  have hinner : inner ℂ u v=inner ℂ (spectralTerminalDensity s hR f)
      ((smoothCollarTrace s b hφ).val 0) :=
    (mFourierBasis (d:=Fin 2)).repr.symm.inner_map_map _ _
  rw [←spectralTerminalDensity_pair s hR f (smoothCollarTrace s b hφ),←hinner,L2.inner_def]
  congr 1
  exact Complex.reCLM.integral_comp_comm hi

lemma fullEndFlatCovector_terminal_integral {s : Fin 3 → ℝ}
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    {R : ℝ} (hR : 0<R) (f : spectralTraceGraph (torusRate s)) (κ b : ℝ)
    {φ : Coord3 → ℝ} (hφ : ContDiff ℝ (↑(⊤:ℕ∞)) φ) :
    Integrable (fun θ => fullEndFlatCovector s f κ R θ 0*φ (sourceAngularCollar b θ)) ∧
    (∫ θ,fullEndFlatCovector s f κ R θ 0*φ (sourceAngularCollar b θ))=
      cylinderTerminalFlux s κ R f (smoothCollarTrace s b hφ) := by
  obtain ⟨hi,he⟩ := spectralTerminalDensity_smooth_pair hs hR f b hφ
  have hq : Integrable (fun θ => φ (sourceAngularCollar b θ)) :=
    (hφ.continuous.comp (continuous_sourceAngularCollar b)).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)
  have hp : (fun θ => fullEndFlatCovector s f κ R θ 0*φ (sourceAngularCollar b θ))=
      (fun θ => (endPoissonField s f 1 (R,θ)).re*φ (sourceAngularCollar b θ)+
        κ*φ (sourceAngularCollar b θ)) := by
    funext θ
    simp [fullEndFlatCovector,add_mul]
  rw [hp]
  refine ⟨hi.add (hq.const_mul κ),?_⟩
  rw [integral_add hi (hq.const_mul κ),integral_const_mul,he,cylinderTerminalFlux,
    smoothCollarTrace_mean_integral]
  ring

end ScalarConductivity

end
end

end OAI
