import Mathlib
import OAI.Geometry.TamingCompatibility.Hodge.HodgeFrameTest

namespace OAI

section
section

section
noncomputable section
namespace TamingCompatibility.HodgeNormalOperator
open scoped RealInnerProductSpace
open EuclideanEnergy
lemma join_inner (u v a b : V) : ⟪join u v,join a b⟫ = ⟪u,a⟫+⟪v,b⟫ := by
  simp [join,PiLp.inner_apply,Fin.sum_univ_succ]
  ring
lemma output_inner (g : MetricModel.Metric V) (b : Fin 4 → V)
    (hb : ∀ i j, g.bilinear (b i) (b j) = if i=j then 1 else 0)
    (a c d f : MetricForms.Form V 1) :
    ⟪left b a+right b c,left b d+right b f⟫ =
      MetricForms.pairing g a d+MetricForms.pairing g c f := by
  rw [left_add_right,left_add_right,join_inner,
    LocalMatrixOperator.frameVector_pairing g b hb,LocalMatrixOperator.frameVector_pairing g b hb]
end TamingCompatibility.HodgeNormalOperator

namespace TamingCompatibility.MetricHodge
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
lemma full_starTwo_zero (g : MetricModel.Metric E) (J : E →L[ℝ] E) (F : MetricForms.Form E 2) :
    starTwo g J F 0 = 0 := by
  simp only [starTwo,MetricForms.pairing_zero_left,zero_smul]
  ext v
  simp
end TamingCompatibility.MetricHodge

namespace TamingCompatibility.HodgeChart
open ManifoldForms ManifoldHodge HodgeFrame GeometricChart ManifoldLocalization ManifoldVolume
open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
  (p : X) (D : GeometricChart.Data J α ht p)
lemma rawVector_manifoldTest (q : Space → HodgeNormalSymbol.W) {z : Space} (hz : z ∈ D.domain) :
    rawVector J α ht p D (manifoldTest J α ht p D q) z = q z := by
  unfold rawVector
  rw [pullback_manifoldTest J α ht p D q (D.domain_subset hz)]
  exact coordinates_reconstruct _ _ (D.frame_gram z hz) _

variable [T2Space X]
lemma manifoldTest_delta_zero_off {q : Space → HodgeNormalSymbol.W}
    (hc : HasCompactSupport q) (hqD : tsupport q ⊆ D.domain)
    {x : X} (hx : x ∉ (extChartAt Model p).symm '' tsupport q) :
    codifferential J α ht (manifoldTest J α ht p D q) x = 0 := by
  have hK : IsCompact ((extChartAt Model p).symm '' tsupport q) :=
    hc.image_of_continuousOn ((continuousOn_extChartAt_symm p).mono (hqD.trans D.domain_subset))
  have he : exteriorDerivative (starTwo J α ht (manifoldTest J α ht p D q)) x = 0 := by
    apply exteriorDerivative_eq_zero_of_eventually
    filter_upwards [hK.isClosed.isOpen_compl.mem_nhds hx] with y hy
    have hh := manifoldTest_zero_off J α ht p D q hy
    change MetricHodge.starTwo (GeometricAdjoint.pointMetric J α ht y) (J.endomorphism y)
      (invariantPart J α y) (manifoldTest J α ht p D q y) = 0
    rw [hh]
    exact MetricHodge.full_starTwo_zero _ _ _
  change -MetricHodge.starThree (GeometricAdjoint.pointMetric J α ht x)
    (invariantPart J α x) (exteriorDerivative (starTwo J α ht (manifoldTest J α ht p D q)) x) = 0
  rw [he]
  change -MetricHodge.starThree (GeometricAdjoint.pointMetric J α ht x)
    (invariantPart J α x) (0 : MetricForms.Form Space 3) = 0
  exact (congrArg Neg.neg (MetricHodge.starThree_zero (E := Space) _ _)).trans (neg_zero)
lemma manifoldTest_delta_star_zero_off {q : Space → HodgeNormalSymbol.W}
    (hc : HasCompactSupport q) (hqD : tsupport q ⊆ D.domain)
    {x : X} (hx : x ∉ (extChartAt Model p).symm '' tsupport q) :
    codifferential J α ht (starTwo J α ht (manifoldTest J α ht p D q)) x = 0 := by
  have hK : IsCompact ((extChartAt Model p).symm '' tsupport q) :=
    hc.image_of_continuousOn ((continuousOn_extChartAt_symm p).mono (hqD.trans D.domain_subset))
  have he : exteriorDerivative (manifoldTest J α ht p D q) x = 0 := by
    apply exteriorDerivative_eq_zero_of_eventually
    filter_upwards [hK.isClosed.isOpen_compl.mem_nhds hx] with y hy
    exact manifoldTest_zero_off J α ht p D q hy
  unfold codifferential
  rw [starTwo_square]
  change -MetricHodge.starThree (GeometricAdjoint.pointMetric J α ht x)
    (invariantPart J α x) (exteriorDerivative (manifoldTest J α ht p D q) x) = 0
  rw [he]
  change -MetricHodge.starThree (GeometricAdjoint.pointMetric J α ht x)
    (invariantPart J α x) (0 : MetricForms.Form Space 3) = 0
  exact (congrArg Neg.neg (MetricHodge.starThree_zero (E := Space) _ _)).trans (neg_zero)

variable (hs : IsSmooth α)
include hs in
lemma normal_manifoldTest_delta {q : Space → HodgeNormalSymbol.W}
    (hq : ContDiff ℝ ∞ q) (hc : HasCompactSupport q) (hqD : tsupport q ⊆ D.domain)
    {z : Space} (hz : z ∈ D.domain) :
    HodgeNormalOperator.left (fun i => D.frame i z)
      (ManifoldForms.pullback (codifferential J α ht (manifoldTest J α ht p D q)) (extChartAt Model p).symm z) +
    HodgeNormalOperator.right (fun i => D.frame i z)
      (ManifoldForms.pullback (codifferential J α ht (starTwo J α ht (manifoldTest J α ht p D q)))
        (extChartAt Model p).symm z) = -normalOperator J α ht p D q z := by
  rw [normal_delta J α hs ht p D (manifoldTest_smooth J α hs ht p D hq hc hqD) hz]
  have he : rawVector J α ht p D (manifoldTest J α ht p D q) =ᶠ[𝓝 z] q := by
    filter_upwards [D.domain_open.mem_nhds hz] with y hy
    exact rawVector_manifoldTest J α ht p D q hy
  simp only [normalOperator,he.fderiv_eq,he.eq_of_nhds]

include hs in
lemma normal_energy_point {a : TwoForm X} (ha : IsSmooth a)
    {q : Space → HodgeNormalSymbol.W} (hq : ContDiff ℝ ∞ q) (hc : HasCompactSupport q)
    (hqD : tsupport q ⊆ D.domain) {z : Space} (hz : z ∈ D.domain) :
    MetricForms.pairing (coordinateMetric J α ht p z)
      (ManifoldForms.pullback (codifferential J α ht a) (extChartAt Model p).symm z)
      (ManifoldForms.pullback (codifferential J α ht (manifoldTest J α ht p D q)) (extChartAt Model p).symm z) +
    MetricForms.pairing (coordinateMetric J α ht p z)
      (ManifoldForms.pullback (codifferential J α ht (starTwo J α ht a)) (extChartAt Model p).symm z)
      (ManifoldForms.pullback (codifferential J α ht (starTwo J α ht (manifoldTest J α ht p D q)))
        (extChartAt Model p).symm z) =
      ⟪normalOperator J α ht p D (rawVector J α ht p D a) z,normalOperator J α ht p D q z⟫ := by
  rw [← HodgeNormalOperator.output_inner _ _ (D.frame_gram z hz),normal_delta J α hs ht p D ha hz,
    normal_manifoldTest_delta J α ht p D hs hq hc hqD hz,inner_neg_neg]
end TamingCompatibility.HodgeChart

end
end

section
noncomputable section
namespace TamingCompatibility.HodgeChart
open ManifoldForms ManifoldHodge HodgeFrame GeometricChart ManifoldLocalization ManifoldVolume
open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
def energyPairing (a b : TwoForm X) (x : X) : ℝ :=
  GeometricAdjoint.pairing J α ht (codifferential J α ht a) (codifferential J α ht b) x +
  GeometricAdjoint.pairing J α ht (codifferential J α ht (starTwo J α ht a))
    (codifferential J α ht (starTwo J α ht b)) x
variable (hs : IsSmooth α)
include hs in
lemma energyPairing_continuous {a b : TwoForm X} (ha : IsSmooth a) (hb : IsSmooth b) :
    Continuous (energyPairing J α ht a b) := by
  exact (GeometricAdjoint.pairing_one_smooth J α hs ht
    (GeometricAdjoint.codifferential_smooth J α hs ht ha)
    (GeometricAdjoint.codifferential_smooth J α hs ht hb)).continuous.add
    (GeometricAdjoint.pairing_one_smooth J α hs ht
      (GeometricAdjoint.codifferential_smooth J α hs ht (starTwo_smooth J α hs ht ha))
      (GeometricAdjoint.codifferential_smooth J α hs ht (starTwo_smooth J α hs ht hb))).continuous
variable (p : X) (D : GeometricChart.Data J α ht p) [T2Space X]
lemma energyPairing_zero_off (a : TwoForm X) {q : Space → HodgeNormalSymbol.W}
    (hc : HasCompactSupport q) (hqD : tsupport q ⊆ D.domain)
    {x : X} (hx : x ∉ (extChartAt Model p).symm '' tsupport q) :
    energyPairing J α ht a (manifoldTest J α ht p D q) x = 0 := by
  unfold energyPairing GeometricAdjoint.pairing
  rw [manifoldTest_delta_zero_off J α ht p D hc hqD hx,
    manifoldTest_delta_star_zero_off J α ht p D hc hqD hx]
  have h₁ := MetricForms.pairing_zero_right (E := Space)
    (GeometricAdjoint.pointMetric J α ht x) (codifferential J α ht a x)
  have h₂ := MetricForms.pairing_zero_right (E := Space)
    (GeometricAdjoint.pointMetric J α ht x) (codifferential J α ht (starTwo J α ht a) x)
  exact (congrArg₂ (fun s t : ℝ => s+t) h₁ h₂).trans (zero_add 0)
variable [CompactSpace X] [MeasurableSpace X] [BorelSpace X] (A : FiniteCharts X)
include hs in
lemma normal_energy_integral {a : TwoForm X} (ha : IsSmooth a)
    {q : Space → HodgeNormalSymbol.W} (hq : ContDiff ℝ ∞ q) (hc : HasCompactSupport q)
    (hqD : tsupport q ⊆ D.domain) :
    (∫ x, energyPairing J α ht a (manifoldTest J α ht p D q) x ∂geometricVolume A J α) =
    ∫ z, chartDensity J α p z *
      ⟪normalOperator J α ht p D (rawVector J α ht p D a) z,normalOperator J α ht p D q z⟫ := by
  let f := energyPairing J α ht a (manifoldTest J α ht p D q)
  have hfc : Continuous f := energyPairing_continuous J α ht hs ha (manifoldTest_smooth J α hs ht p D hq hc hqD)
  have hK : IsCompact ((extChartAt Model p).symm '' tsupport q) :=
    hc.image_of_continuousOn ((continuousOn_extChartAt_symm p).mono (hqD.trans D.domain_subset))
  have hfK : tsupport f ⊆ (extChartAt Model p).symm '' tsupport q := by
    apply closure_minimal _ hK.isClosed
    intro x hx
    by_contra hn
    exact hx (energyPairing_zero_off J α ht p D a hc hqD hn)
  have hfsource : tsupport f ⊆ (extChartAt Model p).source := by
    rintro x hx
    obtain ⟨z,hz,rfl⟩ := hfK hx
    exact (extChartAt Model p).map_target (D.domain_subset (hqD hz))
  change (∫ x, f x ∂geometricVolume A J α) = _
  rw [integral_geometricVolume_coordinate A J α hs ht p f hfc hfsource,
    ← integral_indicator (isOpen_extChartAt_target p).measurableSet]
  apply integral_congr_ae
  filter_upwards [] with z
  by_cases hzq : z ∈ tsupport q
  · have hz := D.domain_subset (hqD hzq)
    rw [indicator_of_mem hz]
    change chartDensity J α p z * energyPairing J α ht a (manifoldTest J α ht p D q)
      ((extChartAt Model p).symm z) = _
    unfold energyPairing
    rw [← pairing_chart J α ht p (Or.inl rfl) _ _ hz,
      ← pairing_chart J α ht p (Or.inl rfl) _ _ hz,
      normal_energy_point J α ht p D hs ha hq hc hqD (hqD hzq)]
  · rw [normalOperator_zero_off J α ht p D q hzq,inner_zero_right,mul_zero]
    by_cases hz : z ∈ (extChartAt Model p).target
    · rw [indicator_of_mem hz]
      have hn : (extChartAt Model p).symm z ∉ (extChartAt Model p).symm '' tsupport q := by
        rintro ⟨y,hy,he⟩
        apply hzq
        have hzy : y=z := (extChartAt Model p).symm.injOn (D.domain_subset (hqD hy)) hz he
        rwa [← hzy]
      change chartDensity J α p z * energyPairing J α ht a (manifoldTest J α ht p D q)
        ((extChartAt Model p).symm z) = 0
      rw [energyPairing_zero_off J α ht p D a hc hqD hn,mul_zero]
    · rw [indicator_of_notMem hz]
end TamingCompatibility.HodgeChart

end
end

end
end

end OAI
