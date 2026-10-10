import Mathlib
import OAI.Analysis.Conductivity.Sources.AngularJet
import OAI.Analysis.Conductivity.Flux.WeakFluxClassicalC1
import OAI.Analysis.Conductivity.Fourier.TorusPeriodicDescent

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory UnitAddTorus
open scoped ENNReal
local instance torusCylinderGreenRealMeasureSpaceUnitAddCircle : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance torusCylinderGreenRealIsProbabilityMeasure :
    IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

lemma continuous_memLp_finiteCylinder_general {E : Type*} [NormedAddCommGroup E]
    {f : ℝ × UnitAddTorus (Fin 2) → E} (hf : Continuous f) (R : ℝ) :
    MemLp f 2 ((FiniteAxisMeasure R).prod volume) := by
  obtain ⟨C,hC⟩ := ((isCompact_Icc (a:=(0:ℝ)) (b:=R)).prod
    (isCompact_univ : IsCompact (univ : Set (UnitAddTorus (Fin 2))))).exists_bound_of_continuousOn hf.continuousOn
  apply MemLp.of_bound hf.aestronglyMeasurable C
  filter_upwards [finiteCylinder_ae_mem R] with z hz
  exact hC z ⟨hz,mem_univ _⟩

lemma torusPeriodicDescent_cylinderIntegral {f : Coord3 → ℝ}
    (hf : Continuous f) (hp : AngularPeriodic (2*Real.pi) f) {R : ℝ} (hR : 0≤R) :
    (∫ z,torusPeriodicDescent f z ∂(FiniteAxisMeasure R).prod volume)=
      (2*Real.pi)⁻¹^2*(∫ t in (0:ℝ)..R,torusCellIntegral (2*Real.pi) f t) := by
  rw [integral_prod _ ((continuous_memLp_finiteCylinder_general
    (continuous_torusPeriodicDescent hf hp) R).integrable (by norm_num))]
  simp_rw [torusPeriodicDescent_integral hf hp]
  rw [integral_const_mul,intervalIntegral.integral_of_le hR]

theorem torusCylinder_green_real {R : ℝ} (hR : 0≤R)
    {F : Coord3 → Coord3} {φ : Coord3 → ℝ}
    (hF : ContDiff ℝ 1 F) (hφ : ContDiff ℝ 1 φ)
    (hp : AngularPeriodic (2*Real.pi) F) (hφp : AngularPeriodic (2*Real.pi) φ)
    (hd : ∀ x,x 0∈Icc 0 R → coordinateDivergence F x=0) :
    (∫ z,torusPeriodicDescent (fun x => fderiv ℝ φ x (F x)) z
      ∂(FiniteAxisMeasure R).prod volume)=
      (∫ θ,torusPeriodicDescent (fun x => φ x*F x 0) (R,θ))-
        (∫ θ,torusPeriodicDescent (fun x => φ x*F x 0) (0,θ)) := by
  have hc := (hφ.continuous_fderiv (by norm_num)).clm_apply hF.continuous
  have hdp : AngularPeriodic (2*Real.pi) (fun x => fderiv ℝ φ x (F x)) := by
    intro n x
    dsimp only
    rw [hφp.fderiv n x,hp n x]
  have hpc : Continuous (fun x => φ x*F x 0) := hφ.continuous.mul ((continuous_apply 0).comp hF.continuous)
  have hpp : AngularPeriodic (2*Real.pi) (fun x => φ x*F x 0) := by
    intro n x
    dsimp only
    rw [hφp n x,hp n x]
  rw [torusPeriodicDescent_cylinderIntegral hc hdp hR,
    torusPeriodicDescent_integral hpc hpp,torusPeriodicDescent_integral hpc hpp,
    torus_band_green_C1 (by positivity) hR hF hφ hp hφp hd,mul_sub]

end ScalarConductivity

end
end

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory UnitAddTorus
open scoped ENNReal
local instance torusCylinderGreenRealFluxMeasureSpaceUnitAddCircle : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance torusCylinderGreenRealFluxIsProbabilityMeasure :
    IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

variable {F : Coord3 → Coord3}

lemma continuous_torusFluxComponent (hF : Continuous F) (hp : AngularPeriodic (2*Real.pi) F)
    (j : Fin 3) : Continuous (fun z => (torusPeriodicDescent F z j:ℂ)) :=
  Complex.continuous_ofReal.comp ((continuous_apply j).comp (continuous_torusPeriodicDescent hF hp))

def cylinderFluxLp (hF : Continuous F) (hp : AngularPeriodic (2*Real.pi) F)
    (R : ℝ) (j : Fin 3) : CylinderL2 (FiniteAxisMeasure R) :=
  (continuous_memLp_finiteCylinder (continuous_torusFluxComponent hF hp j) R).toLp _

lemma cylinderFluxLp_ae (hF : Continuous F) (hp : AngularPeriodic (2*Real.pi) F)
    (R : ℝ) (j : Fin 3) : cylinderFluxLp hF hp R j=ᵐ[(FiniteAxisMeasure R).prod volume]
      fun z => (torusPeriodicDescent F z j:ℂ) :=
  (continuous_memLp_finiteCylinder (continuous_torusFluxComponent hF hp j) R).coeFn_toLp

def cylinderFluxPairL (hF : Continuous F) (hp : AngularPeriodic (2*Real.pi) F)
    (R : ℝ) : FiniteCylinderJets R →L[ℂ] ℂ :=
  ∑ j : Fin 3,(innerSL ℂ (cylinderFluxLp hF hp R j)).comp
    (PiLp.proj 2 (fun _ : Fin 4 => CylinderL2 (FiniteAxisMeasure R)) j.succ)

lemma cylinderFluxPairL_apply (hF : Continuous F) (hp : AngularPeriodic (2*Real.pi) F)
    (R : ℝ) (J : FiniteCylinderJets R) :
    cylinderFluxPairL hF hp R J=∑ j : Fin 3,inner ℂ (cylinderFluxLp hF hp R j) (J j.succ) := by
  simp [cylinderFluxPairL]

lemma cylinderFluxPairL_integral (hF : Continuous F) (hp : AngularPeriodic (2*Real.pi) F)
    (R : ℝ) (J : FiniteCylinderJets R) :
    cylinderFluxPairL hF hp R J=
      ∫ z,∑ j : Fin 3,(torusPeriodicDescent F z j:ℂ)*J j.succ z ∂(FiniteAxisMeasure R).prod volume := by
  rw [cylinderFluxPairL_apply]
  simp_rw [L2.inner_def]
  rw [←integral_finsetSum _ (fun i _ => L2.integrable_inner (𝕜:=ℂ) _ _)]
  apply integral_congr_ae
  filter_upwards [ae_all_iff.mpr (cylinderFluxLp_ae hF hp R)] with z hz
  apply Finset.sum_congr rfl
  intro j _
  rw [hz j]
  simp [RCLike.inner_apply,mul_comm]

def torusFluxLp (hF : Continuous F) (hp : AngularPeriodic (2*Real.pi) F) (t : ℝ) : TorusL2 :=
  ContinuousMap.toLp 2 volume ℂ ⟨fun θ => (torusPeriodicDescent F (t,θ) 0:ℂ),
    (continuous_torusFluxComponent hF hp 0).comp (continuous_const.prodMk continuous_id)⟩

lemma torusFluxLp_ae (hF : Continuous F) (hp : AngularPeriodic (2*Real.pi) F) (t : ℝ) :
    torusFluxLp hF hp t=ᵐ[volume] fun θ => (torusPeriodicDescent F (t,θ) 0:ℂ) :=
  ContinuousMap.coeFn_toLp volume _

def torusSpectralSynthesis (s : Fin 3 → ℝ) : spectralTraceGraph (torusRate s) →L[ℂ] TorusL2 :=
  ((mFourierBasis (d:=Fin 2)).repr.symm.toContinuousLinearEquiv.toContinuousLinearMap).comp
    ((PiLp.proj 2 (fun _ : Fin 2 => SpectralL2 TorusModes) 0).comp (spectralTraceGraph (torusRate s)).subtypeL)

lemma torusSpectralSynthesis_single (s : Fin 3 → ℝ) (h : TorusModes) (a : ℂ) :
    torusSpectralSynthesis s (spectralTraceSingleL s h a)=a • mFourierLp 2 h := by
  change (mFourierBasis (d:=Fin 2)).repr.symm (lp.single 2 h a)=_
  rw [show (a:ℂ)=a • (1:ℂ) by simp,lp.single_smul,map_smul,HilbertBasis.repr_symm_single]
  simp only [coe_mFourierBasis,smul_eq_mul,mul_one]

def torusFluxPairL (hF : Continuous F) (hp : AngularPeriodic (2*Real.pi) F)
    (s : Fin 3 → ℝ) (t : ℝ) : spectralTraceGraph (torusRate s) →L[ℂ] ℂ :=
  (innerSL ℂ (torusFluxLp hF hp t)).comp (torusSpectralSynthesis s)

lemma torusFluxPairL_integral (hF : Continuous F) (hp : AngularPeriodic (2*Real.pi) F)
    (s : Fin 3 → ℝ) (t : ℝ) (f : spectralTraceGraph (torusRate s)) :
    torusFluxPairL hF hp s t f=
      ∫ θ,(torusPeriodicDescent F (t,θ) 0:ℂ)*torusSpectralSynthesis s f θ := by
  change inner ℂ (torusFluxLp hF hp t) (torusSpectralSynthesis s f)=_
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [torusFluxLp_ae hF hp t] with θ hθ
  rw [hθ]
  simp [RCLike.inner_apply,mul_comm]

lemma torusFluxPairL_single (hF : Continuous F) (hp : AngularPeriodic (2*Real.pi) F)
    (s : Fin 3 → ℝ) (t : ℝ) (h : TorusModes) (a : ℂ) :
    torusFluxPairL hF hp s t (spectralTraceSingleL s h a)=
      ∫ θ,(torusPeriodicDescent F (t,θ) 0:ℂ)*(a*mFourier h θ) := by
  rw [torusFluxPairL_integral,torusSpectralSynthesis_single]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_smul a (mFourierLp 2 h),coeFn_mFourierLp 2 h] with θ h1 h2
  rw [h1]
  simp only [Pi.smul_apply,smul_eq_mul,h2]

end ScalarConductivity

end
end

end OAI
