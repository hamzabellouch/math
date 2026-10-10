import Mathlib
import OAI.Analysis.Conductivity.Flux.TorusCylinderGreenComplex

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory UnitAddTorus Matrix
open scoped ENNReal
local instance sourceFluxCylinderMeasureSpace : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance sourceFluxCylinderIsProbabilityMeasure : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

lemma cylinderFluxPairL_integrable {F : Coord3 → Coord3} (hF : Continuous F)
    (hp : AngularPeriodic (2*Real.pi) F) (R : ℝ) (J : FiniteCylinderJets R) :
    Integrable (fun z => ∑ j : Fin 3,(torusPeriodicDescent F z j:ℂ)*J j.succ z)
      ((FiniteAxisMeasure R).prod volume) := by
  have hi := integrable_finsetSum (μ:=(FiniteAxisMeasure R).prod volume) Finset.univ
    (fun j _ => L2.integrable_inner (𝕜:=ℂ) (cylinderFluxLp hF hp R j) (J j.succ))
  apply hi.congr
  filter_upwards [ae_all_iff.mpr (cylinderFluxLp_ae hF hp R)] with z hz
  apply Finset.sum_congr rfl
  intro j _
  rw [hz j]
  simp [RCLike.inner_apply,mul_comm]

def sourceFluxDensity (F : Coord3 → Coord3) (a b : ℝ) (φ : Coord3 → ℝ)
    (z : ℝ × UnitAddTorus (Fin 2)) : ℝ :=
  torusPeriodicDescent F z ⬝ᵥ(fun j : Fin 3 => (sourceAngularJet φ a b j.succ z).re)

lemma sourceFluxDensity_cylinder {F : Coord3 → Coord3} (hF : Continuous F)
    (hp : AngularPeriodic (2*Real.pi) F) (a b R : ℝ)
    {φ : Coord3 → ℝ} (hφ : ContDiff ℝ (↑(⊤:ℕ∞)) φ) :
    Integrable (sourceFluxDensity F a b φ) ((FiniteAxisMeasure R).prod volume) ∧
    (∫ z,sourceFluxDensity F a b φ z ∂(FiniteAxisMeasure R).prod volume)=
      (cylinderFluxPairL hF hp R (sourceAngularLpJet hφ a b R)).re := by
  let G := fun z => ∑ j : Fin 3,(torusPeriodicDescent F z j:ℂ)*sourceAngularLpJet hφ a b R j.succ z
  have hi : Integrable G ((FiniteAxisMeasure R).prod volume) :=
    cylinderFluxPairL_integrable hF hp R (sourceAngularLpJet hφ a b R)
  have he : (fun z => (G z).re)=ᵐ[(FiniteAxisMeasure R).prod volume] sourceFluxDensity F a b φ := by
    filter_upwards [ae_all_iff.mpr (sourceAngularLpJet_ae hφ a b R)] with z hz
    simp only [G,Complex.re_sum,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
      zero_mul,sub_zero,hz,sourceFluxDensity,dotProduct]
  refine ⟨hi.re.congr he,?_⟩
  rw [cylinderFluxPairL_integral]
  exact (integral_congr_ae he).symm.trans (Complex.reCLM.integral_comp_comm hi)

lemma torusSpectralSynthesis_smoothCollar_ae (s : Fin 3 → ℝ) (b : ℝ)
    {φ : Coord3 → ℝ} (hφ : ContDiff ℝ (↑(⊤:ℕ∞)) φ) :
    torusSpectralSynthesis s (smoothCollarTrace s b hφ)=ᵐ[volume]
      fun θ => (φ (sourceAngularCollar b θ):ℂ) := by
  have he : (smoothCollarTrace s b hφ).val 0=smoothCollarTraceFourier b hφ := by
    apply lp.ext
    funext h
    rw [smoothCollarTrace_fst,smoothCollarTraceFourier_apply]
  change (mFourierBasis (d:=Fin 2)).repr.symm ((smoothCollarTrace s b hφ).val 0)=ᵐ[volume] _
  rw [he,smoothCollarTraceFourier,LinearIsometryEquiv.symm_apply_apply]
  exact ContinuousMap.coeFn_toLp volume _

lemma torusFluxPairL_smoothCollar {F : Coord3 → Coord3} (hF : Continuous F)
    (hp : AngularPeriodic (2*Real.pi) F) (s : Fin 3 → ℝ) (t b : ℝ)
    {φ : Coord3 → ℝ} (hφ : ContDiff ℝ (↑(⊤:ℕ∞)) φ) :
    (torusFluxPairL hF hp s t (smoothCollarTrace s b hφ)).re=
      ∫ θ,torusPeriodicDescent F (t,θ) 0*φ (sourceAngularCollar b θ) := by
  rw [torusFluxPairL_integral]
  have hc : Continuous (fun θ => (torusPeriodicDescent F (t,θ) 0:ℂ)*(φ (sourceAngularCollar b θ):ℂ)) :=
    ((continuous_torusFluxComponent hF hp 0).comp (continuous_const.prodMk continuous_id)).mul
      (Complex.continuous_ofReal.comp (hφ.continuous.comp (continuous_sourceAngularCollar b)))
  have he : (∫ θ,(torusPeriodicDescent F (t,θ) 0:ℂ)*torusSpectralSynthesis s (smoothCollarTrace s b hφ) θ)=
      ∫ θ,(torusPeriodicDescent F (t,θ) 0:ℂ)*(φ (sourceAngularCollar b θ):ℂ) := by
    apply integral_congr_ae
    filter_upwards [torusSpectralSynthesis_smoothCollar_ae s b hφ] with θ hθ
    rw [hθ]
  rw [he]
  simpa using (Complex.reCLM.integral_comp_comm (hc.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _))).symm

theorem sourceFluxDensity_green {F : Coord3 → Coord3} (hF : ContDiff ℝ 1 F)
    (hp : AngularPeriodic (2*Real.pi) F) {R : ℝ} (hR : 0≤R)
    (hd : ∀ x,x 0∈Icc 0 R → coordinateDivergence F x=0) (a b : ℝ)
    {φ : Coord3 → ℝ} (hφ : ContDiff ℝ (↑(⊤:ℕ∞)) φ) :
    (∫ z,sourceFluxDensity F a b φ z ∂(FiniteAxisMeasure R).prod volume)=
      (∫ θ,torusPeriodicDescent F (R,θ) 0*φ (sourceAngularCollar (a*R+b) θ))-
      (∫ θ,torusPeriodicDescent F (0,θ) 0*φ (sourceAngularCollar b θ)) := by
  let s : Fin 3 → ℝ := ![1,0,1]
  rw [(sourceFluxDensity_cylinder hF.continuous hp a b R hφ).2]
  have hh := torusFlux_completed_green hR s hF hp hd
    ⟨(_,(_,_)),sourceAngularLpJet_graph s hφ a b R⟩
  rw [hh,Complex.sub_re,torusFluxPairL_smoothCollar,torusFluxPairL_smoothCollar]

end ScalarConductivity

end
end

end OAI
