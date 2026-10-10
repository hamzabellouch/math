import Mathlib
import OAI.Geometry.TamingCompatibility.DifferentialForms.AntiEnergy
import OAI.Geometry.TamingCompatibility.Charts.ChartTestPairing
import OAI.Geometry.TamingCompatibility.Functional.ChartNormalTest

namespace OAI

section
section
section

section
noncomputable section
namespace TamingCompatibility.GeometricChart
open ManifoldForms ManifoldHodge AntiInvariantFrame LocalMatrixOperator Set Filter
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (hs : IsSmooth α) (ht : Tames α J)
  (p : X) (D : Data J α ht p)

include hs in
lemma normal_coordinateTest_at {q : Space → EuclideanEnergy.Pair}
    {z : Space} (hd : DifferentiableAt ℝ q z) (hz : z ∈ D.domain) :
    frameVector (fun i => D.frame i z)
      (MetricHodge.starThree (coordinateMetric J α ht p z)
        (TamingCompatibility.pullback (invariantPart J α) (extChartAt Model p).symm z)
        (extDeriv (coordinateTest J α ht p D q) z)) =
      (∑ i, normalA J α ht p D i z (fderiv ℝ q z (EuclideanEnergy.e i))) +
        normalB J α ht p D z (q z) := by
  obtain ⟨h0,h1,h2,h3⟩ := D.frame_complex z hz
  have hψ := realPart_smooth ((coordinateMetric_smooth J α hs ht p).mono D.domain_subset) D.frame_smooth
  have hχ := imagPart_smooth ((coordinateMetric_smooth J α hs ht p).mono D.domain_subset) D.frame_smooth
  have h := normal_operator_expansion
    (A := fun y => q y 0) (B := fun y => q y 1)
    (ψ := fun y => realPart (coordinateMetric J α ht p y) (fun i => D.frame i y))
    (χ := fun y => imagPart (coordinateMetric J α ht p y) (fun i => D.frame i y))
    (coordinateMetric J α ht p z)
    (TamingCompatibility.pullback (invariantPart J α) (extChartAt Model p).symm z)
    (fun i => D.frame i z) (D.frame_gram z hz) (coordinateJ J p z) h0 h1 h2 h3
    (fun u v => ManifoldTop.coordinateFundamental J α ht p (D.domain_subset hz) u v)
    rfl rfl ((EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).differentiableAt.comp z hd)
    ((EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).differentiableAt.comp z hd)
    (((hψ z hz).contDiffAt (D.domain_open.mem_nhds hz)).differentiableAt (by norm_num))
    (((hχ z hz).contDiffAt (D.domain_open.mem_nhds hz)).differentiableAt (by norm_num))
  simp only [pair_fderiv hd] at h
  have hqz : EuclideanEnergy.pair (q z 0) (q z 1) = q z := by ext i; fin_cases i <;> rfl
  rw [hqz] at h
  exact h

lemma rawScalar_smooth {a : TwoForm X} (ha : IsSmooth a) (j : Fin 4) :
    ContDiffOn ℝ ∞ (rawScalar J α ht p D a j) D.domain := by
  exact FormSmooth.contDiffOn_apply_two ((smooth_chart a ha p).mono D.domain_subset)
    (D.frame_smooth 0) (D.frame_smooth j)

def rawPair (a : TwoForm X) (z : Space) : EuclideanEnergy.Pair :=
  EuclideanEnergy.pair (rawScalar J α ht p D a 2 z) (rawScalar J α ht p D a 3 z)

lemma rawPair_smooth {a : TwoForm X} (ha : IsSmooth a) :
    ContDiffOn ℝ ∞ (rawPair J α ht p D a) D.domain := by
  apply (contDiffOn_piLp 2).mpr
  intro i
  fin_cases i
  · exact rawScalar_smooth J α ht p D ha 2
  · exact rawScalar_smooth J α ht p D ha 3

include hs in
lemma normal_delta {a : TwoForm X} (ha : IsSmooth a) (hanti : antiInvariantPart J a = a)
    {z : Space} (hz : z ∈ D.domain) :
    frameVector (fun i => D.frame i z)
      (ManifoldForms.pullback (codifferential J α ht a) (extChartAt Model p).symm z) =
      -((∑ i, normalA J α ht p D i z
          (fderiv ℝ (rawPair J α ht p D a) z (EuclideanEnergy.e i))) +
        normalB J α ht p D z (rawPair J α ht p D a z)) := by
  rw [pullback_codifferential_antiInvariant J α ht ha hanti p (D.domain_subset hz),map_neg]
  have he : ManifoldForms.pullback a (extChartAt Model p).symm =ᶠ[𝓝 z]
      coordinateTest J α ht p D (rawPair J α ht p D a) := by
    filter_upwards [D.domain_open.mem_nhds hz] with y hy
    exact rawScalar_expansion J α ht p D hanti hy
  rw [he.extDeriv_eq]
  rw [normal_coordinateTest_at J α hs ht p D
    (((rawPair_smooth J α ht p D ha z hz).contDiffAt
      (D.domain_open.mem_nhds hz)).differentiableAt (by norm_num)) hz]
end TamingCompatibility.GeometricChart

end
end

section
noncomputable section
namespace TamingCompatibility.GeometricChart
open ManifoldForms ManifoldHodge AntiInvariantFrame LocalMatrixOperator ManifoldLocalization ManifoldVolume
open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J) (p : X) (D : Data J α ht p)

def normalOperator (q : Space → EuclideanEnergy.Pair) (z : Space) : Space :=
  (∑ i, normalA J α ht p D i z (fderiv ℝ q z (EuclideanEnergy.e i))) +
    normalB J α ht p D z (q z)

lemma normalOperator_zero_off (q : Space → EuclideanEnergy.Pair) {z : Space}
    (hz : z ∉ tsupport q) : normalOperator J α ht p D q z = 0 := by
  have he : q =ᶠ[𝓝 z] (fun _ => 0) := by
    filter_upwards [(isClosed_tsupport q).isOpen_compl.mem_nhds hz] with y hy
    exact image_eq_zero_of_notMem_tsupport hy
  simp only [normalOperator,he.fderiv_eq,fderiv_fun_const,
    image_eq_zero_of_notMem_tsupport hz,map_zero,add_zero]
  apply Finset.sum_eq_zero
  intro i _
  change (normalA J α ht p D i z) (0 : EuclideanEnergy.Pair) = 0
  exact map_zero _

variable [T2Space X]
lemma manifoldTest_delta_zero_off {q : Space → EuclideanEnergy.Pair}
    (hc : HasCompactSupport q) (hqD : tsupport q ⊆ D.domain)
    {x : X} (hx : x ∉ (extChartAt Model p).symm '' tsupport q) :
    codifferential J α ht (manifoldTest J α ht p D q) x = 0 := by
  have hK : IsCompact ((extChartAt Model p).symm '' tsupport q) :=
    hc.image_of_continuousOn ((continuousOn_extChartAt_symm p).mono (hqD.trans D.domain_subset))
  rw [codifferential_anti J α ht (manifoldTest_anti J α ht p D q)]
  have he : exteriorDerivative (manifoldTest J α ht p D q) x = 0 := by
    apply exteriorDerivative_eq_zero_of_eventually
    filter_upwards [hK.isClosed.isOpen_compl.mem_nhds hx] with y hy
    exact manifoldTest_zero_off J α ht p D q hy
  change -MetricHodge.starThree (GeometricAdjoint.pointMetric J α ht x)
    (invariantPart J α x) (exteriorDerivative (manifoldTest J α ht p D q) x) = 0
  rw [he]
  change -MetricHodge.starThree (GeometricAdjoint.pointMetric J α ht x)
    (invariantPart J α x) (0 : MetricForms.Form Space 3) = 0
  exact (congrArg Neg.neg (MetricHodge.starThree_zero (E := Space)
    (GeometricAdjoint.pointMetric J α ht x) (invariantPart J α x))).trans (neg_zero)

variable (hs : IsSmooth α)
include hs in
lemma normal_energy_point {a : TwoForm X} (ha : IsSmooth a) (hanti : antiInvariantPart J a = a)
    {q : Space → EuclideanEnergy.Pair} (hq : ContDiff ℝ ∞ q) (hc : HasCompactSupport q)
    (hqD : tsupport q ⊆ D.domain) {z : Space} (hz : z ∈ D.domain) :
    MetricForms.pairing (coordinateMetric J α ht p z)
      (ManifoldForms.pullback (codifferential J α ht a) (extChartAt Model p).symm z)
      (ManifoldForms.pullback (codifferential J α ht (manifoldTest J α ht p D q))
        (extChartAt Model p).symm z) =
      ⟪normalOperator J α ht p D (rawPair J α ht p D a) z,normalOperator J α ht p D q z⟫ := by
  rw [← frameVector_pairing _ _ (D.frame_gram z hz),normal_delta J α hs ht p D ha hanti hz,
    normal_manifoldTest_delta J α hs ht p D hq hc hqD hz,inner_neg_neg]
  rfl

variable [CompactSpace X] [MeasurableSpace X] [BorelSpace X] (A : FiniteCharts X)
include hs in
lemma normal_energy_integral {a : TwoForm X} (ha : IsSmooth a) (hanti : antiInvariantPart J a = a)
    {q : Space → EuclideanEnergy.Pair} (hq : ContDiff ℝ ∞ q) (hc : HasCompactSupport q)
    (hqD : tsupport q ⊆ D.domain) :
    (∫ x, GeometricAdjoint.pairing J α ht (codifferential J α ht a)
      (codifferential J α ht (manifoldTest J α ht p D q)) x ∂geometricVolume A J α) =
    ∫ z, chartDensity J α p z *
      ⟪normalOperator J α ht p D (rawPair J α ht p D a) z,normalOperator J α ht p D q z⟫ := by
  let f := GeometricAdjoint.pairing J α ht (codifferential J α ht a)
    (codifferential J α ht (manifoldTest J α ht p D q))
  have hfc : Continuous f := (GeometricAdjoint.pairing_one_smooth J α hs ht
    (GeometricAdjoint.codifferential_smooth J α hs ht ha)
    (GeometricAdjoint.codifferential_smooth J α hs ht (manifoldTest_smooth J α hs ht p D hq hc hqD))).continuous
  have hK : IsCompact ((extChartAt Model p).symm '' tsupport q) :=
    hc.image_of_continuousOn ((continuousOn_extChartAt_symm p).mono (hqD.trans D.domain_subset))
  have hfK : tsupport f ⊆ (extChartAt Model p).symm '' tsupport q := by
    apply closure_minimal _ hK.isClosed
    intro x hx
    by_contra hn
    apply hx
    change MetricForms.pairing (E := Space) (GeometricAdjoint.pointMetric J α ht x)
      (codifferential J α ht a x) (codifferential J α ht (manifoldTest J α ht p D q) x) = 0
    rw [manifoldTest_delta_zero_off J α ht p D hc hqD hn]
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
  by_cases hzq : z ∈ tsupport q
  · have hz := D.domain_subset (hqD hzq)
    rw [indicator_of_mem hz]
    change chartDensity J α p z * GeometricAdjoint.pairing J α ht _ _
      ((extChartAt Model p).symm z) = _
    rw [← pairing_chart J α ht p (Or.inl rfl) _ _ hz]
    rw [normal_energy_point J α ht p D hs ha hanti hq hc hqD (hqD hzq)]
  · rw [normalOperator_zero_off J α ht p D q hzq,inner_zero_right,mul_zero]
    by_cases hz : z ∈ (extChartAt Model p).target
    · rw [indicator_of_mem hz]
      have hn : (extChartAt Model p).symm z ∉ (extChartAt Model p).symm '' tsupport q := by
        rintro ⟨y,hy,he⟩
        apply hzq
        have hzy : y=z := (extChartAt Model p).symm.injOn (D.domain_subset (hqD hy)) hz he
        rwa [← hzy]
      change chartDensity J α p z * MetricForms.pairing (E := Space)
        (GeometricAdjoint.pointMetric J α ht ((extChartAt Model p).symm z))
        (codifferential J α ht a ((extChartAt Model p).symm z))
        (codifferential J α ht (manifoldTest J α ht p D q) ((extChartAt Model p).symm z)) = 0
      rw [manifoldTest_delta_zero_off J α ht p D hc hqD hn]
      exact (congrArg (fun t : ℝ => chartDensity J α p z * t)
        (MetricForms.pairing_zero_right (E := Space) _ _)).trans (mul_zero _)
    · rw [indicator_of_notMem hz]
end TamingCompatibility.GeometricChart

end
end

end
end
end

end OAI
