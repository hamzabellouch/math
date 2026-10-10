import OAI.Geometry.IsometricImmersion.Darboux.CurvaturePrincipalPart
import OAI.Geometry.IsometricImmersion.Pulses.PulseProfiles
import OAI.Geometry.IsometricImmersion.Curvature.AffineCurvature

namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology BigOperators Matrix

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry

def thetaPulseMetric (g : MetricField) (f : Coord → ℝ) : MetricField :=
  fun p => g p + !![0,0;0,f p]

def thetaPulseFirstJet (f : Coord → ℝ) (p : Coord) : MetricFirstJet :=
  fun d i j => if i=1 ∧ j=1 then coordPartial d f p else 0

def thetaPulseLowerDifference (g : MetricField) (f : Coord → ℝ) (p : Coord) : ℝ :=
  curvatureLowerJet (g p + !![0,0;0,f p])
    (metricFirstJet g p + thetaPulseFirstJet f p) -
      curvatureLowerJet (g p) (metricFirstJet g p)

theorem thetaPulseMetric_entry (g : MetricField) (f : Coord → ℝ) (p : Coord) (i j : Fin 2) :
    thetaPulseMetric g f p i j = g p i j + if i=1 ∧ j=1 then f p else 0 := by
  fin_cases i <;> fin_cases j <;> simp [thetaPulseMetric]

theorem metricFirstJet_thetaPulseMetric {g : MetricField} {f : Coord → ℝ} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hf : ContDiffOn ℝ ∞ f U) (hU : IsOpen U)
    {p : Coord} (hp : p ∈ U) :
    metricFirstJet (thetaPulseMetric g f) p = metricFirstJet g p + thetaPulseFirstJet f p := by
  funext d i j
  have hgD : DifferentiableAt ℝ (fun q => g q i j) p :=
    ((hg.1 i j).contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)
  have hfD : DifferentiableAt ℝ f p :=
    (hf.contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)
  by_cases hij : i=1 ∧ j=1
  · have he : (fun q => thetaPulseMetric g f q i j) = (fun q => g q i j+f q) := by
      funext q
      simp only [thetaPulseMetric_entry,ite_eq_left hij]
    change coordPartial d (fun q => thetaPulseMetric g f q i j) p = _
    rw [he,HessianCalculus.coordPartial_add_at hgD hfD d]
    simp only [Pi.add_apply,Matrix.add_apply,metricFirstJet,thetaPulseFirstJet,ite_eq_left hij]
  · have he : (fun q => thetaPulseMetric g f q i j) = (fun q => g q i j) := by
      funext q
      simp only [thetaPulseMetric_entry,ite_eq_right hij,add_zero]
    change coordPartial d (fun q => thetaPulseMetric g f q i j) p = _
    rw [he]
    simp only [Pi.add_apply,Matrix.add_apply,metricFirstJet,thetaPulseFirstJet,ite_eq_right hij,add_zero]

theorem secondCoordPartial_add {f h : Coord → ℝ} {U : Set Coord}
    (hf : ContDiffOn ℝ ∞ f U) (hh : ContDiffOn ℝ ∞ h U) (hU : IsOpen U)
    {p : Coord} (hp : p ∈ U) (i j : Fin 2) :
    coordPartial i (coordPartial j (fun q => f q+h q)) p =
      coordPartial i (coordPartial j f) p + coordPartial i (coordPartial j h) p := by
  have he : coordPartial j (fun q => f q+h q) =ᶠ[𝓝 p]
      (fun q => coordPartial j f q+coordPartial j h q) := by
    filter_upwards [hU.mem_nhds hp] with q hq
    exact HessianCalculus.coordPartial_add_at
      ((hf.contDiffAt (hU.mem_nhds hq)).differentiableAt (by simp))
      ((hh.contDiffAt (hU.mem_nhds hq)).differentiableAt (by simp)) j
  rw [coordPartial_eq_of_eventuallyEq he i]
  exact HessianCalculus.coordPartial_add_at
    (((partial_contDiffOn hf hU j).contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp))
    (((partial_contDiffOn hh hU j).contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)) i

theorem thetaPulseLowerDifference_eq {g : MetricField} {f : Coord → ℝ} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hf : ContDiffOn ℝ ∞ f U) (hU : IsOpen U)
    {p : Coord} (hp : p ∈ U) :
    thetaPulseLowerDifference g f p =
      curvatureLowerTerm (thetaPulseMetric g f) p-curvatureLowerTerm g p := by
  simp only [curvatureLowerTerm,metricFirstJet_thetaPulseMetric hg hf hU hp,
    thetaPulseMetric,thetaPulseLowerDifference]

theorem thetaPulse_curvature_density {g : MetricField} {f : Coord → ℝ} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hplus : SmoothPositiveOn (thetaPulseMetric g f) U)
    (hf : ContDiffOn ℝ ∞ f U) (hU : IsOpen U) {p : Coord} (hp : p ∈ U) :
    gaussianCurvature (thetaPulseMetric g f) p*(thetaPulseMetric g f p).det -
      gaussianCurvature g p*(g p).det =
        -(1/2 : ℝ)*coordPartial 0 (coordPartial 0 f) p + thetaPulseLowerDifference g f p := by
  have h00 : (fun q => thetaPulseMetric g f q 0 0) = (fun q => g q 0 0) := by
    funext q
    simp [thetaPulseMetric_entry]
  have h01 : (fun q => thetaPulseMetric g f q 0 1) = (fun q => g q 0 1) := by
    funext q
    simp [thetaPulseMetric_entry]
  have h11 : (fun q => thetaPulseMetric g f q 1 1) = (fun q => g q 1 1+f q) := by
    funext q
    simp [thetaPulseMetric_entry]
  have hnew := gaussianCurvature_density_principal_part hplus hU hp
  rw [h00,h01,h11,secondCoordPartial_add (hg.1 1 1) hf hU hp 0 0] at hnew
  have hold := gaussianCurvature_density_principal_part hg hU hp
  rw [hnew,hold,thetaPulseLowerDifference_eq hg hf hU hp]
  ring

theorem thetaPulseLowerDifference_contDiffOn
    {g : MetricField} {f : Coord → ℝ} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hplus : SmoothPositiveOn (thetaPulseMetric g f) U)
    (hf : ContDiffOn ℝ ∞ f U) (hU : IsOpen U) :
    ContDiffOn ℝ ∞ (thetaPulseLowerDifference g f) U := by
  apply ((curvatureLowerTerm_contDiffOn hplus hU).sub
    (curvatureLowerTerm_contDiffOn hg hU)).congr
  intro p hp
  exact thetaPulseLowerDifference_eq hg hf hU hp

@[simp] theorem inverseShearMatrix_det (q0 : ℝ) : (inverseShearMatrix q0).det = 1 := by
  simp [inverseShearMatrix,Matrix.det_fin_two]

theorem inverseShearMatrix_isUnit (q0 : ℝ) : IsUnit (inverseShearMatrix q0) := by
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  simp

def metricInShearCoordinates (g : MetricField) (q0 : ℝ) : MetricField :=
  affinePullbackMetric g 0 (inverseShearMatrix q0)

theorem metricInShearCoordinates_test (gStar : MetricField) (q0 a : ℝ) (N : ℕ)
    (delta tau : ℝ) :
    metricInShearCoordinates (testMetric gStar q0 a N delta tau) q0 =
      thetaPulseMetric (metricInShearCoordinates gStar q0) (pulseScalar a N delta tau) := by
  funext p
  exact testMetric_inverseShear gStar q0 a N delta tau p

theorem actual_pulse_curvature_density
    {gStar : MetricField} {U : Set Coord} (q0 a : ℝ) (N : ℕ) (delta tau : ℝ)
    (hg : SmoothPositiveOn gStar U)
    (htest : SmoothPositiveOn (testMetric gStar q0 a N delta tau) U)
    (hU : IsOpen U) {p : Coord} (hp : inverseShearCoordinates q0 p ∈ U) :
    gaussianCurvature (testMetric gStar q0 a N delta tau) (inverseShearCoordinates q0 p) *
        (testMetric gStar q0 a N delta tau (inverseShearCoordinates q0 p)).det -
      gaussianCurvature gStar (inverseShearCoordinates q0 p) *
        (gStar (inverseShearCoordinates q0 p)).det =
      -(1/2 : ℝ)*coordPartial 0 (coordPartial 0 (pulseScalar a N delta tau)) p +
        thetaPulseLowerDifference (metricInShearCoordinates gStar q0) (pulseScalar a N delta tau) p := by
  let R := inverseShearMatrix q0
  let V := affineCoordinates 0 R ⁻¹' U
  have hR : IsUnit R := inverseShearMatrix_isUnit q0
  have hV : IsOpen V := hU.preimage (affineCoordinates_contDiff 0 R).continuous
  have hpV : p ∈ V := by
    simpa only [V,R,Set.mem_preimage,←inverseShearCoordinates_eq_affine] using hp
  have hgV : SmoothPositiveOn (metricInShearCoordinates gStar q0) V :=
    affinePullbackMetric_smoothPositive hg 0 R (Matrix.mulVec_injective_of_isUnit hR)
  have htV : SmoothPositiveOn
      (metricInShearCoordinates (testMetric gStar q0 a N delta tau) q0) V :=
    affinePullbackMetric_smoothPositive htest 0 R (Matrix.mulVec_injective_of_isUnit hR)
  have htTheta : SmoothPositiveOn
      (thetaPulseMetric (metricInShearCoordinates gStar q0) (pulseScalar a N delta tau)) V := by
    rw [←metricInShearCoordinates_test]
    exact htV
  have hformula := thetaPulse_curvature_density hgV htTheta
    (pulseScalar_contDiff a N delta tau).contDiffOn hV hpV
  rw [←metricInShearCoordinates_test] at hformula
  have hpa : affineCoordinates 0 R p ∈ U := hpV
  have hKg := gaussianCurvature_affinePullback hg hU 0 R hR p hpa
  have hKt := gaussianCurvature_affinePullback htest hU 0 R hR p hpa
  change gaussianCurvature (affinePullbackMetric (testMetric gStar q0 a N delta tau) 0 R) p *
      (affinePullbackMetric (testMetric gStar q0 a N delta tau) 0 R p).det -
      gaussianCurvature (affinePullbackMetric gStar 0 R) p *
        (affinePullbackMetric gStar 0 R p).det = _ at hformula
  rw [hKt,hKg,det_affinePullbackMetric,det_affinePullbackMetric] at hformula
  simpa only [R,inverseShearMatrix_det,one_pow,one_mul,
    ←inverseShearCoordinates_eq_affine] using hformula

end SmoothLocal.Pulse

end

end OAI
