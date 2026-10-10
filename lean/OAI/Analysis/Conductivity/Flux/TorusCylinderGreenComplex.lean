import Mathlib
import OAI.Analysis.Conductivity.Flux.TorusCylinderGreenReal
import OAI.Analysis.Conductivity.Fourier.TorusSmoothModeJet

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory UnitAddTorus
open scoped ENNReal
local instance torusCylinderGreenComplexMeasureSpaceUnitAddCircle : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance torusCylinderGreenComplexIsProbabilityMeasure :
    IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem torusCylinder_green_complex {R : ℝ} (hR : 0≤R)
    {F : Coord3 → Coord3} {φ : Coord3 → ℂ}
    (hF : ContDiff ℝ 1 F) (hφ : ContDiff ℝ 1 φ)
    (hp : AngularPeriodic (2*Real.pi) F) (hφp : AngularPeriodic (2*Real.pi) φ)
    (hd : ∀ x,x 0∈Icc 0 R → coordinateDivergence F x=0) :
    (∫ z,torusPeriodicDescent (fun x => fderiv ℝ φ x (F x)) z
      ∂(FiniteAxisMeasure R).prod volume)=
      (∫ θ,torusPeriodicDescent (fun x => (F x 0) • φ x) (R,θ))-
        (∫ θ,torusPeriodicDescent (fun x => (F x 0) • φ x) (0,θ)) := by
  have hc := (hφ.continuous_fderiv (by norm_num)).clm_apply hF.continuous
  have hdp : AngularPeriodic (2*Real.pi) (fun x => fderiv ℝ φ x (F x)) := by
    intro n x
    dsimp only
    rw [hφp.fderiv n x,hp n x]
  have hpc : Continuous (fun x => (F x 0) • φ x) := ((continuous_apply 0).comp hF.continuous).smul hφ.continuous
  have hpp : AngularPeriodic (2*Real.pi) (fun x => (F x 0) • φ x) := by
    intro n x
    dsimp only
    rw [hφp n x,hp n x]
  have hi := (continuous_memLp_finiteCylinder_general
    (continuous_torusPeriodicDescent hc hdp) R).integrable (by norm_num : (1:ℝ≥0∞)≤2)
  have hib (t : ℝ) : Integrable (fun θ => torusPeriodicDescent (fun x => (F x 0) • φ x) (t,θ)) :=
    ((continuous_torusPeriodicDescent hpc hpp).comp (continuous_const.prodMk continuous_id)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hL (L : ℂ →L[ℝ] ℝ) :
      L (∫ z,torusPeriodicDescent (fun x => fderiv ℝ φ x (F x)) z
        ∂(FiniteAxisMeasure R).prod volume)=
      L ((∫ θ,torusPeriodicDescent (fun x => (F x 0) • φ x) (R,θ))-
        (∫ θ,torusPeriodicDescent (fun x => (F x 0) • φ x) (0,θ))) := by
    rw [map_sub,←L.integral_comp_comm hi,←L.integral_comp_comm (hib R),←L.integral_comp_comm (hib 0)]
    have hLp : AngularPeriodic (2*Real.pi) (fun x => L (φ x)) := by
      intro n x
      dsimp only
      rw [hφp n x]
    have he := torusCylinder_green_real hR hF (L.contDiff.comp hφ) hp hLp hd
    have hder (x : Coord3) : fderiv ℝ (fun y => L (φ y)) x=L.comp (fderiv ℝ φ x) :=
      (L.hasFDerivAt.comp x ((hφ.differentiable (by norm_num)) x).hasFDerivAt).fderiv
    simpa only [Function.comp_def,torusPeriodicDescent,hder,ContinuousLinearMap.comp_apply,map_smul,smul_eq_mul,mul_comm] using he
  exact Complex.ext (hL Complex.reCLM) (hL Complex.imCLM)

end ScalarConductivity

end
end

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory UnitAddTorus
open scoped ENNReal
local instance torusCylinderGreenComplexModeMeasureSpaceUnitAddCircle : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance torusCylinderGreenComplexModeIsProbabilityMeasure :
    IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

lemma complex_coordinate_fderiv_expansion (φ : Coord3 → ℂ) (x v : Coord3) :
    fderiv ℝ φ x v=∑ j : Fin 3,(v j:ℂ)*fderiv ℝ φ x (Pi.single j 1) := by
  have he : v=∑ j : Fin 3,(v j) • (Pi.single j 1 : Coord3) := by
    ext i
    fin_cases i <;> simp [Pi.smul_apply,Pi.single_apply]
  conv_lhs => rw [he,map_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp [Complex.real_smul]

lemma torusFlux_mode_green {R : ℝ} (hR : 0≤R) (s : Fin 3 → ℝ)
    {F : Coord3 → Coord3} (hF : ContDiff ℝ 1 F)
    (hp : AngularPeriodic (2*Real.pi) F)
    (hd : ∀ x,x 0∈Icc 0 R → coordinateDivergence F x=0)
    {q : ℝ → ℂ} (hq : ContDiff ℝ (↑(⊤:ℕ∞)) q) (h : TorusModes) :
    cylinderFluxPairL hF.continuous hp R (smoothCylinderModeJet hq R h)=
      torusFluxPairL hF.continuous hp s R (spectralTraceSingleL s h (q R))-
      torusFluxPairL hF.continuous hp s 0 (spectralTraceSingleL s h (q 0)) := by
  have hh := torusCylinder_green_complex hR hF ((flatSmoothMode_smooth hq h).of_le (by simp))
    hp (flatSmoothMode_periodic q h) hd
  rw [cylinderFluxPairL_integral,torusFluxPairL_single,torusFluxPairL_single]
  convert hh using 1
  · apply integral_congr_ae
    filter_upwards [ae_all_iff.mpr (smoothCylinderModeJet_ae hq R h)] with z hz
    simp_rw [hz]
    simp only [torusPeriodicDescent]
    rw [complex_coordinate_fderiv_expansion]
    apply Finset.sum_congr rfl
    intro j _
    rw [flatSmoothMode_derivative hq]
    simp only [torusAngles_scaled,torusRealProjection_representative,Matrix.cons_val_zero]
  · congr 1 <;> apply integral_congr_ae <;> exact Filter.Eventually.of_forall (fun θ => by
      simp only [torusPeriodicDescent,flatSmoothMode_eq,torusAngles_scaled,
        torusRealProjection_representative,Matrix.cons_val_zero,Complex.real_smul])

lemma torusFluxPairL_polynomial {F : Coord3 → Coord3} (hF : Continuous F)
    (hp : AngularPeriodic (2*Real.pi) F) (s : Fin 3 → ℝ) (t : ℝ)
    (p : TorusModes →₀ smoothComplexAxis) :
    torusFluxPairL hF hp s t (cylinderPolynomialTraceL s t p)=
      ∑ h∈p.support,torusFluxPairL hF hp s t (spectralTraceSingleL s h (p h t)) := by
  rw [cylinderPolynomialTraceL,Finsupp.lsum_apply,Finsupp.sum,map_sum]
  rfl

theorem torusFlux_completed_green {R : ℝ} (hR : 0≤R) (s : Fin 3 → ℝ)
    {F : Coord3 → Coord3} (hF : ContDiff ℝ 1 F)
    (hp : AngularPeriodic (2*Real.pi) F)
    (hd : ∀ x,x 0∈Icc 0 R → coordinateDivergence F x=0)
    (z : cylinderSobolevGraph s R) :
    cylinderFluxPairL hF.continuous hp R z.val.1=
      torusFluxPairL hF.continuous hp s R z.val.2.2-
      torusFluxPairL hF.continuous hp s 0 z.val.2.1 := by
  let J : CylinderTraceAmbient s R →L[ℂ] FiniteCylinderJets R := ContinuousLinearMap.fst ℂ _ _
  let T₀ : CylinderTraceAmbient s R →L[ℂ] spectralTraceGraph (torusRate s) :=
    (ContinuousLinearMap.fst ℂ _ _).comp (ContinuousLinearMap.snd ℂ _ _)
  let T₁ : CylinderTraceAmbient s R →L[ℂ] spectralTraceGraph (torusRate s) :=
    (ContinuousLinearMap.snd ℂ _ _).comp (ContinuousLinearMap.snd ℂ _ _)
  let L := (cylinderFluxPairL hF.continuous hp R).comp J-
    (((torusFluxPairL hF.continuous hp s R).comp T₁)-
      ((torusFluxPairL hF.continuous hp s 0).comp T₀))
  have hr : LinearMap.range (cylinderPolynomialGraphL s R)≤L.ker := by
    rintro _ ⟨p,rfl⟩
    change cylinderFluxPairL hF.continuous hp R (cylinderPolynomialJetL R p)-
      (torusFluxPairL hF.continuous hp s R (cylinderPolynomialTraceL s R p)-
        torusFluxPairL hF.continuous hp s 0 (cylinderPolynomialTraceL s 0 p))=0
    rw [cylinderPolynomialJetL_apply,map_sum,torusFluxPairL_polynomial,torusFluxPairL_polynomial]
    simp_rw [torusFlux_mode_green hR s hF hp hd,Finset.sum_sub_distrib,sub_self]
  have hz := Submodule.topologicalClosure_minimal _ hr L.isClosed_ker z.property
  exact sub_eq_zero.mp hz

end ScalarConductivity

end
end

end OAI
