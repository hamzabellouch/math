import Mathlib
import OAI.Geometry.TamingCompatibility.Charts.ChartEnergyIntegral
import OAI.Geometry.TamingCompatibility.DifferentialForms.GeometricFrameTest

namespace OAI

section
section
section

section
noncomputable section
namespace TamingCompatibility.MetricForms
open MetricModel
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
lemma pairing_zero_right (g : Metric E) {k : ℕ} (a : Form E k) : pairing g a 0 = 0 := by
  simpa only [zero_smul,zero_mul] using pairing_smul_right g (0:ℝ) a (0 : Form E k)
end TamingCompatibility.MetricForms
namespace TamingCompatibility.AntiInvariantFrame
open ContinuousAlternatingMap MetricModel MetricForms
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
lemma pairing_combination_mixed (g : Metric E) (hdim : Module.finrank ℝ E = 4)
    (b : Fin 4 → E) (hb : ∀ i j, g.bilinear (b i) (b j) = if i=j then 1 else 0)
    (A B C D : ℝ) :
    pairing g (A • realPart g b + B • imagPart g b) (C • realPart g b + D • imagPart g b) =
      2 * (A*C+B*D) := by
  rw [pairing_two_eq_sum g hdim b hb]
  simp only [ContinuousAlternatingMap.add_apply,ContinuousAlternatingMap.smul_apply,smul_eq_mul,
    realPart_apply,imagPart_apply,hb]
  simp [Fin.sum_univ_succ,FormMetric.pairLeft,FormMetric.pairRight]
  ring
end TamingCompatibility.AntiInvariantFrame

namespace TamingCompatibility.GeometricChart
open ManifoldForms ManifoldHodge AntiInvariantFrame LocalMatrixOperator ManifoldLocalization ManifoldVolume
open Set MeasureTheory
open scoped Manifold ContDiff
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J) (p : X) (D : Data J α ht p)

lemma pullback_anti {a : TwoForm X} (ha : antiInvariantPart J a = a)
    {z : Space} (hz : z ∈ (extChartAt Model p).target) :
    (pullback a (extChartAt Model p).symm z).compContinuousLinearMap (coordinateJ J p z) =
      -pullback a (extChartAt Model p).symm z := by
  have hj : TamingCompatibility.jAction J a = -a := by
    calc TamingCompatibility.jAction J a = a - (2:ℝ) • antiInvariantPart J a := by
          unfold antiInvariantPart
          module
         _ = -a := by rw [ha]; module
  have hp := pullback_jAction_chart (⟨J.endomorphism,J.square,J.smooth⟩ :
    SmoothAlmostComplex.AlmostComplexStructure X) a p hz
  change pullback (TamingCompatibility.jAction J a) (extChartAt Model p).symm z = _ at hp
  rw [hj] at hp
  exact hp.symm

def rawScalar (a : TwoForm X) (j : Fin 4) (z : Space) : ℝ :=
  pullback a (extChartAt Model p).symm z ![D.frame 0 z,D.frame j z]

lemma rawScalar_expansion {a : TwoForm X} (ha : antiInvariantPart J a = a)
    {z : Space} (hz : z ∈ D.domain) :
    pullback a (extChartAt Model p).symm z =
      rawScalar J α ht p D a 2 z • realPart (coordinateMetric J α ht p z) (fun i => D.frame i z) +
      rawScalar J α ht p D a 3 z • imagPart (coordinateMetric J α ht p z) (fun i => D.frame i z) := by
  obtain ⟨h0,h1,h2,h3⟩ := D.frame_complex z hz
  exact expansion (coordinateMetric J α ht p z) (by simp [Space]) _ (D.frame_gram z hz)
    (coordinateJ J p z) h0 h1 h2 h3 _ (pullback_anti J p ha (D.domain_subset hz))

lemma pairing_coordinateTest {a : TwoForm X} (ha : antiInvariantPart J a = a)
    {q : Space → EuclideanEnergy.Pair} (hqD : tsupport q ⊆ D.domain) {z : Space}
    (_hz : z ∈ (extChartAt Model p).target) :
    MetricForms.pairing (coordinateMetric J α ht p z) (pullback a (extChartAt Model p).symm z)
      (coordinateTest J α ht p D q z) =
    2 * (rawScalar J α ht p D a 2 z * q z 0 + rawScalar J α ht p D a 3 z * q z 1) := by
  by_cases hzq : z ∈ tsupport q
  · rw [rawScalar_expansion J α ht p D ha (hqD hzq)]
    exact pairing_combination_mixed _ (by simp [Space]) _ (D.frame_gram z (hqD hzq)) _ _ _ _
  · have hq := image_eq_zero_of_notMem_tsupport hzq
    have htest : coordinateTest J α ht p D q z = 0 := frameTest_zero hq
    rw [htest,MetricForms.pairing_zero_right,hq]
    simp

lemma manifoldTest_zero_off (q : Space → EuclideanEnergy.Pair) {x : X}
    (hx : x ∉ (extChartAt Model p).symm '' tsupport q) : manifoldTest J α ht p D q x = 0 := by
  have hn : x ∉ liftSupport p (coordinateTest J α ht p D q) := by
    rintro ⟨z,hz,hzx⟩
    exact hx ⟨z,coordinateTest_support J α ht p D q hz,hzx⟩
  unfold manifoldTest antiInvariantPart
  have hz := chartLift_zero_off p (coordinateTest J α ht p D q) hn
  ext v
  simp only [Pi.smul_apply,Pi.sub_apply,ContinuousAlternatingMap.smul_apply,
    ContinuousAlternatingMap.sub_apply,TamingCompatibility.jAction]
  rw [hz]
  simp

variable [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (hs : IsSmooth α)
include hs in
lemma pairing_manifoldTest_integral {a : TwoForm X} (ha : IsSmooth a)
    (hanti : antiInvariantPart J a = a) {q : Space → EuclideanEnergy.Pair}
    (hq : ContDiff ℝ ∞ q) (hc : HasCompactSupport q) (hqD : tsupport q ⊆ D.domain) :
    (∫ x, GeometricAdjoint.pairing J α ht a (manifoldTest J α ht p D q) x ∂geometricVolume A J α) =
    ∫ z, chartDensity J α p z *
      (2 * (rawScalar J α ht p D a 2 z * q z 0 + rawScalar J α ht p D a 3 z * q z 1)) := by
  let f := GeometricAdjoint.pairing J α ht a (manifoldTest J α ht p D q)
  have hfc : Continuous f := (GeometricAdjoint.pairing_two_smooth J α hs ht ha
    (manifoldTest_smooth J α hs ht p D hq hc hqD)).continuous
  have hK : IsCompact ((extChartAt Model p).symm '' tsupport q) :=
    hc.image_of_continuousOn ((continuousOn_extChartAt_symm p).mono (hqD.trans D.domain_subset))
  have hfK : tsupport f ⊆ (extChartAt Model p).symm '' tsupport q := by
    apply closure_minimal _ hK.isClosed
    intro x hx
    by_contra hn
    apply hx
    change MetricForms.pairing (E := Space) (GeometricAdjoint.pointMetric J α ht x) (a x)
      (manifoldTest J α ht p D q x) = 0
    rw [manifoldTest_zero_off J α ht p D q hn]
    exact MetricForms.pairing_zero_right (E := Space) _ _
  have hfsource : tsupport f ⊆ (extChartAt Model p).source := by
    rintro x hx
    obtain ⟨z,hz,rfl⟩ := hfK hx
    exact (extChartAt Model p).map_target (D.domain_subset (hqD hz))
  change (∫ x, f x ∂geometricVolume A J α) = _
  rw [integral_geometricVolume_coordinate A J α hs ht p f hfc hfsource,
    ← integral_indicator (isOpen_extChartAt_target p).measurableSet]
  apply integral_congr_ae
  filter_upwards [] with z
  by_cases hz : z ∈ (extChartAt Model p).target
  · rw [indicator_of_mem hz]
    change chartDensity J α p z * GeometricAdjoint.pairing J α ht a (manifoldTest J α ht p D q)
      ((extChartAt Model p).symm z) = _
    rw [← pairing_chart J α ht p (Or.inr rfl) a (manifoldTest J α ht p D q) hz]
    change chartDensity J α p z * MetricForms.pairing (coordinateMetric J α ht p z)
      (TamingCompatibility.pullback a (extChartAt Model p).symm z)
      (TamingCompatibility.pullback (manifoldTest J α ht p D q) (extChartAt Model p).symm z) = _
    rw [pullback_manifoldTest J α ht p D hqD hz,pairing_coordinateTest J α ht p D hanti hqD hz]
  · rw [indicator_of_notMem hz]
    have hqz : q z = 0 := image_eq_zero_of_notMem_tsupport (fun h => hz (D.domain_subset (hqD h)))
    simp only [hqz,PiLp.zero_apply,mul_zero,add_zero]

end TamingCompatibility.GeometricChart

end
end

end
end
end

end OAI
