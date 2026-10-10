import OAI.NumberTheory.Jacobsthal.Harmonic.WeightedAnomalyConvergence

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

open _root_.Set _root_.Erdos970.Set _root_.MeasureTheory _root_.Erdos970.MeasureTheory
namespace ErdosBoundaryIntegral
open ErdosContinuousBoundary ErdosContinuousAnomaly
open NumberTheoryLean.FinitePathGeometry NumberTheoryLean.ReferenceBenchmarkDecay
open NumberTheoryLean.LinearSieveFunctions NumberTheoryLean.BuchstabBridge

noncomputable def lowerReference (y : ℝ) : ℝ := 2*boundaryReference .even (2*y+2) 2
noncomputable def upperReference (y : ℝ) : ℝ := 2*boundaryReference .odd (2*y+2) 2

theorem lower_reference_deviation (y : ℝ) :
    lowerReference y-f sieveA (y+1)=2*shiftedAnomaly .even y := by
  unfold lowerReference shiftedAnomaly continuousAnomaly
  have he : (2*y+2)/2=y+1 := by ring
  rw [he,benchmark]
  ring

theorem upper_reference_deviation (y : ℝ) :
    upperReference y-F sieveA (y+1)=2*shiftedAnomaly .odd y := by
  unfold upperReference shiftedAnomaly continuousAnomaly
  have he : (2*y+2)/2=y+1 := by ring
  rw [he,benchmark]
  ring

theorem lower_coefficient_integrable :
    IntegrableOn (fun y : ℝ => (y^2-1)*(lowerReference y-f sieveA (y+1))) (Ioi 1) := by
  have h0 : IntegrableOn (shiftedAnomaly .even) (Ioi 0) := by
    simpa only [pow_zero,one_mul] using shifted_anomaly_moment_integrable .even 0
  have h2 := shifted_anomaly_moment_integrable .even 2
  have hh : IntegrableOn (fun y : ℝ => 2*(y^2*shiftedAnomaly .even y-shiftedAnomaly .even y)) (Ioi 1) volume :=
    ((h2.sub h0).mono_set (by intro y hy; change 0 < y; change 1 < y at hy; linarith)).const_mul (2:ℝ)
  apply hh.congr_fun _ measurableSet_Ioi
  intro y _hy
  dsimp only
  rw [lower_reference_deviation]
  ring

theorem upper_coefficient_integrable :
    IntegrableOn (fun y : ℝ => y^2*(upperReference y-F sieveA (y+1))) (Ioi 0) := by
  have hh : IntegrableOn (fun y : ℝ => 2*(y^2*shiftedAnomaly .odd y)) (Ioi 0) volume :=
    (shifted_anomaly_moment_integrable .odd 2).const_mul (2:ℝ)
  apply hh.congr_fun _ measurableSet_Ioi
  intro y _hy
  dsimp only
  rw [upper_reference_deviation]
  ring

noncomputable def signedCoefficientI : ℝ :=
  (∫ y in Ioi 1,(y^2-1)*(lowerReference y-f sieveA (y+1)))-
    ∫ y in Ioi 0,y^2*(upperReference y-F sieveA (y+1))

theorem signedCoefficient_eq_anomaly :
    signedCoefficientI =
      2*(∫ y in Ioi 1,(y^2-1)*shiftedAnomaly .even y)-
        2*(∫ y in Ioi 0,y^2*shiftedAnomaly .odd y) := by
  unfold signedCoefficientI
  simp_rw [lower_reference_deviation,upper_reference_deviation]
  have he (y : ℝ) : (y^2-1)*(2*shiftedAnomaly .even y)=2*((y^2-1)*shiftedAnomaly .even y) := by ring
  have ho (y : ℝ) : y^2*(2*shiftedAnomaly .odd y)=2*(y^2*shiftedAnomaly .odd y) := by ring
  simp_rw [he,ho,integral_const_mul]

end ErdosBoundaryIntegral

end

section

open _root_.Set _root_.Erdos970.Set _root_.MeasureTheory _root_.Erdos970.MeasureTheory
namespace ErdosBoundaryIntegral
open ErdosContinuousAnomaly

theorem boundary_affine_integral (a : ℝ) (g : ℝ → ℝ) :
    (∫ r in Ioi (2*a+2),g r) = ∫ y in Ioi a,2*g (2*y+2) := by
  have hd : ∀ x ∈ Ioi a,HasDerivWithinAt (fun y : ℝ => 2*y+2) 2 (Ioi a) x := by
    intro x _
    convert! (((hasDerivAt_id x).const_mul 2).add_const 2).hasDerivWithinAt using 1
    simp
  have hinj : InjOn (fun y : ℝ => 2*y+2) (Ioi a) := by
    intro x _ y _ h
    linarith
  have him : (fun y : ℝ => 2*y+2) '' Ioi a=Ioi (2*a+2) := by
    ext r
    constructor
    · rintro ⟨y,hy,rfl⟩
      change a < y at hy
      change 2*a+2 < 2*y+2
      linarith
    · intro hr
      refine ⟨(r-2)/2,?_,by ring⟩
      change a < (r-2)/2
      change 2*a+2 < r at hr
      linarith
  have h := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hd hinj g
  rw [him] at h
  simpa only [abs_of_pos (by norm_num : (0:ℝ)<2),smul_eq_mul] using! h

theorem radial_coefficient_eq_twice_I :
    ((∫ r in Ioi 4,r*(r/2-2)*continuousAnomaly .even r)-
      ∫ r in Ioi 2,(r^2/2-2*r+2)*continuousAnomaly .odd r)=2*signedCoefficientI := by
  have he := boundary_affine_integral 1 (fun r => r*(r/2-2)*continuousAnomaly .even r)
  have ho := boundary_affine_integral 0 (fun r => (r^2/2-2*r+2)*continuousAnomaly .odd r)
  norm_num only [mul_one,mul_zero,zero_add] at he ho
  rw [he,ho,signedCoefficient_eq_anomaly]
  have he' (y : ℝ) : 2*((2*y+2)*((2*y+2)/2-2)*continuousAnomaly .even (2*y+2))=
      4*((y^2-1)*shiftedAnomaly .even y) := by unfold shiftedAnomaly; ring
  have ho' (y : ℝ) : 2*(((2*y+2)^2/2-2*(2*y+2)+2)*continuousAnomaly .odd (2*y+2))=
      4*(y^2*shiftedAnomaly .odd y) := by unfold shiftedAnomaly; ring
  simp_rw [he',ho',integral_const_mul]
  ring

end ErdosBoundaryIntegral

end

end Erdos970

end OAI
