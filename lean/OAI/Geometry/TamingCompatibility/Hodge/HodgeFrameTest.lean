import Mathlib
import OAI.Geometry.TamingCompatibility.Functional.RawNormal
import OAI.Geometry.TamingCompatibility.Hodge.HodgeLocalCodifferential

namespace OAI

section
section

section
noncomputable section
namespace TamingCompatibility.HodgeChart
open ManifoldForms ManifoldHodge HodgeFrame HodgeGeometricCoefficients GeometricChart
open Set Filter
open scoped Manifold ContDiff Topology
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (hs : IsSmooth α)
  (ht : Tames α J) (p : X) (D : GeometricChart.Data J α ht p)

def coordinateTest (q : Space → HodgeNormalSymbol.W) (z : Space) : MetricForms.Form Space 2 :=
  reconstruct (coordinateMetric J α ht p z) (fun i => D.frame i z) (q z)
omit [T2Space X] in
lemma coordinateTest_zero {q : Space → HodgeNormalSymbol.W} {z : Space} (hz : q z = 0) :
    coordinateTest J α ht p D q z = 0 := by
  simp only [coordinateTest,hz,map_zero]
omit [T2Space X] in
lemma coordinateTest_support (q : Space → HodgeNormalSymbol.W) :
    tsupport (coordinateTest J α ht p D q) ⊆ tsupport q := by
  apply closure_mono
  intro z hz
  by_contra hn
  apply hz
  exact coordinateTest_zero J α ht p D (by simpa only [Function.mem_support, not_not] using hn)
include hs in
omit [T2Space X] in
lemma coordinateTest_smooth {q : Space → HodgeNormalSymbol.W} (hq : ContDiff ℝ ∞ q)
    (hqD : tsupport q ⊆ D.domain) : ContDiff ℝ ∞ (coordinateTest J α ht p D q) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hz : z ∈ tsupport q
  · have hψ := HodgeFrame.basisForm_smooth
      ((coordinateMetric_smooth J α hs ht p).mono D.domain_subset) D.frame_smooth
    change ContDiffAt ℝ ∞ (fun y => ∑ j, q y j • basisForm (coordinateMetric J α ht p y)
      (fun i => D.frame i y) j) z
    apply ContDiffAt.sum
    intro j _
    exact (((EuclideanSpace.proj (𝕜 := ℝ) j).contDiff.comp hq).contDiffAt).smul
      ((hψ j z (hqD hz)).contDiffAt (D.domain_open.mem_nhds (hqD hz)))
  · apply contDiffAt_const.congr_of_eventuallyEq
    filter_upwards [(isClosed_tsupport q).isOpen_compl.mem_nhds hz] with y hy
    exact coordinateTest_zero J α ht p D (image_eq_zero_of_notMem_tsupport hy)
omit [T2Space X] in
lemma coordinateTest_compact {q : Space → HodgeNormalSymbol.W} (hc : HasCompactSupport q) :
    HasCompactSupport (coordinateTest J α ht p D q) :=
  hc.of_isClosed_subset (isClosed_tsupport _) (coordinateTest_support J α ht p D q)

def manifoldTest (q : Space → HodgeNormalSymbol.W) : TwoForm X :=
  chartLift p (coordinateTest J α ht p D q)
include hs in
lemma manifoldTest_smooth {q : Space → HodgeNormalSymbol.W} (hq : ContDiff ℝ ∞ q)
    (hc : HasCompactSupport q) (hqD : tsupport q ⊆ D.domain) :
    IsSmooth (manifoldTest J α ht p D q) :=
  chartLift_smooth p (coordinateTest_smooth J α hs ht p D hq hqD)
    (coordinateTest_compact J α ht p D hc)
    ((coordinateTest_support J α ht p D q).trans (hqD.trans D.domain_subset))
omit [T2Space X] in
lemma pullback_manifoldTest (q : Space → HodgeNormalSymbol.W)
    {z : Space} (hz : z ∈ (extChartAt Model p).target) :
    ManifoldForms.pullback (manifoldTest J α ht p D q) (extChartAt Model p).symm z =
      coordinateTest J α ht p D q z := pullback_chartLift p _ hz
omit [T2Space X] in
lemma manifoldTest_zero_off (q : Space → HodgeNormalSymbol.W) {x : X}
    (hx : x ∉ (extChartAt Model p).symm '' tsupport q) : manifoldTest J α ht p D q x = 0 := by
  apply chartLift_zero_off
  rintro ⟨z,hz,rfl⟩
  exact hx ⟨z,coordinateTest_support J α ht p D q hz,rfl⟩

def rawVector (a : TwoForm X) (z : Space) : HodgeNormalSymbol.W :=
  coordinates (fun i => D.frame i z) (ManifoldForms.pullback a (extChartAt Model p).symm z)
omit [T2Space X] in
lemma rawVector_smooth {a : TwoForm X} (ha : IsSmooth a) :
    ContDiffOn ℝ ∞ (rawVector J α ht p D a) D.domain := by
  apply (contDiffOn_piLp 2).mpr
  intro j
  exact FormSmooth.contDiffOn_apply_two ((smooth_chart a ha p).mono D.domain_subset)
    (D.frame_smooth (FormMetric.pairLeft j)) (D.frame_smooth (FormMetric.pairRight j))
omit [T2Space X] in
lemma rawVector_expansion (a : TwoForm X) {z : Space} (hz : z ∈ D.domain) :
    coordinateTest J α ht p D (rawVector J α ht p D a) z =
      ManifoldForms.pullback a (extChartAt Model p).symm z :=
  reconstruct_coordinates (coordinateMetric J α ht p z) (by simp [Space])
    (fun i => D.frame i z) (D.frame_gram z hz) _
end TamingCompatibility.HodgeChart

end
end

section
noncomputable section
namespace TamingCompatibility.HodgeNormalOperator
open MetricModel MetricForms MetricHodge HodgeFrame EuclideanEnergy
open HodgeNormalSymbol (W Q)
lemma vector_fderiv {q : V → W} {z : V} (hd : DifferentiableAt ℝ q z) (i : Fin 4) :
    WithLp.toLp 2 (fun j => fderiv ℝ (fun y => q y j) z (e i)) = fderiv ℝ q z (e i) := by
  ext j
  have hh := (EuclideanSpace.proj (𝕜 := ℝ) j).hasFDerivAt.comp z hd.hasFDerivAt
  change HasFDerivAt (fun y => q y j) _ z at hh
  change fderiv ℝ (fun y => q y j) z (e i) = fderiv ℝ q z (e i) j
  rw [hh.fderiv]
  rfl
lemma star_reconstruct_function (g : V → Metric V) (J : V → V →L[ℝ] V)
    (F : V → MetricForms.Form V 2) (b : Fin 4 → V → V) (q : V → W) :
    (fun y => ∑ j, q y j • HodgeGeometricCoefficients.starFrame g J F b j y) =
    (fun y => starTwo (g y) (J y) (F y) (reconstruct (g y) (fun i => b i y) (q y))) := by
  funext y
  exact combine_star_basis _ _ _ _ _
lemma reconstruct_function (g : V → Metric V) (b : Fin 4 → V → V) (q : V → W) :
    (fun y => ∑ j, q y j • HodgeGeometricCoefficients.frame g b j y) =
    fun y => reconstruct (g y) (fun i => b i y) (q y) := rfl
lemma reconstruct_expansion (g : V → Metric V) (J : V → V →L[ℝ] V)
    (F : V → MetricForms.Form V 2) (b : Fin 4 → V → V) (q : V → W) (z : V)
    (hd : DifferentiableAt ℝ q z)
    (hψ : ∀ j, DifferentiableAt ℝ (HodgeGeometricCoefficients.frame g b j) z)
    (hφ : ∀ j, DifferentiableAt ℝ (HodgeGeometricCoefficients.starFrame g J F b j) z) :
    left (fun i => b i z) (starThree (g z) (F z)
      (extDeriv (fun y => starTwo (g y) (J y) (F y) (reconstruct (g y) (fun i => b i y) (q y))) z)) +
    right (fun i => b i z) (starThree (g z) (F z)
      (extDeriv (fun y => reconstruct (g y) (fun i => b i y) (q y)) z)) =
    (∑ i, rawPrincipal (g z) (F z) (fun k => b k z) (basisForm (g z) (fun k => b k z))
      (fun j => starTwo (g z) (J z) (F z) (basisForm (g z) (fun k => b k z) j)) i
        (fderiv ℝ q z (e i))) + HodgeGeometricCoefficients.lower g J F b z (q z) := by
  have h := operator_expansion (g z) (F z) (fun i => b i z)
    (HodgeGeometricCoefficients.frame g b) (HodgeGeometricCoefficients.starFrame g J F b)
    (fun j y => q y j) (fun j => (EuclideanSpace.proj (𝕜 := ℝ) j).differentiableAt.comp z hd) hψ hφ
  rw [star_reconstruct_function,reconstruct_function] at h
  simp only [vector_fderiv hd] at h
  have hv : WithLp.toLp 2 (fun j => q z j) = q z := by ext j; rfl
  rw [hv] at h
  exact h
end TamingCompatibility.HodgeNormalOperator

end
end

section
noncomputable section
namespace TamingCompatibility.HodgeChart
open ManifoldForms ManifoldHodge HodgeFrame HodgeGeometricCoefficients GeometricChart
open Set Filter
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (hs : IsSmooth α)
  (ht : Tames α J) (p : X) (D : GeometricChart.Data J α ht p)

def normalA (i : Fin 4) (z : Space) : HodgeNormalSymbol.W →L[ℝ] HodgeNormalSymbol.Q :=
  HodgeGeometricCoefficients.principal D.frame i z
def normalB (z : Space) : HodgeNormalSymbol.W →L[ℝ] HodgeNormalSymbol.Q :=
  HodgeGeometricCoefficients.lower (coordinateMetric J α ht p) (coordinateJ J p)
    (ManifoldForms.pullback (invariantPart J α) (extChartAt Model p).symm) D.frame z
def normalOperator (q : Space → HodgeNormalSymbol.W) (z : Space) : HodgeNormalSymbol.Q :=
  (∑ i, normalA J α ht p D i z (fderiv ℝ q z (EuclideanEnergy.e i))) +
    normalB J α ht p D z (q z)

include hs in
lemma starFrame_smooth (j : Fin 6) : ContDiffOn ℝ ∞
    (HodgeGeometricCoefficients.starFrame (coordinateMetric J α ht p) (coordinateJ J p)
      (ManifoldForms.pullback (invariantPart J α) (extChartAt Model p).symm) D.frame j) D.domain :=
  HodgeGeometricCoefficients.starFrame_smooth _ _ _ _ D.domain_open
    ((coordinateMetric_smooth J α hs ht p).mono D.domain_subset)
    ((coordinateJ_smooth J p).mono D.domain_subset)
    (fun _x hx => coordinateJ_square J p (D.domain_subset hx))
    (fun _x hx => coordinateMetric_hermitian J α ht p (D.domain_subset hx))
    ((smooth_chart _ (hs.invariantPart J) p).mono D.domain_subset) D.frame_smooth j

lemma normalA_smooth (i : Fin 4) : ContDiffOn ℝ ∞ (normalA J α ht p D i) D.domain :=
  HodgeGeometricCoefficients.principal_smooth D.frame_smooth i
include hs in
lemma normalB_smooth : ContDiffOn ℝ ∞ (normalB J α ht p D) D.domain :=
  HodgeGeometricCoefficients.lower_smooth _ _ _ _ D.domain_open
    ((coordinateMetric_smooth J α hs ht p).mono D.domain_subset)
    ((coordinateJ_smooth J p).mono D.domain_subset)
    (fun _x hx => coordinateJ_square J p (D.domain_subset hx))
    (fun _x hx => coordinateMetric_hermitian J α ht p (D.domain_subset hx))
    ((smooth_chart _ (hs.invariantPart J) p).mono D.domain_subset) D.frame_smooth

include hs in
lemma normal_coordinateTest_at {q : Space → HodgeNormalSymbol.W}
    {z : Space} (hd : DifferentiableAt ℝ q z) (hz : z ∈ D.domain) :
    HodgeNormalOperator.left (fun i => D.frame i z)
      (MetricHodge.starThree (coordinateMetric J α ht p z)
        (ManifoldForms.pullback (invariantPart J α) (extChartAt Model p).symm z)
        (extDeriv (fun y => MetricHodge.starTwo (coordinateMetric J α ht p y)
          (coordinateJ J p y) (ManifoldForms.pullback (invariantPart J α) (extChartAt Model p).symm y)
          (coordinateTest J α ht p D q y)) z)) +
    HodgeNormalOperator.right (fun i => D.frame i z)
      (MetricHodge.starThree (coordinateMetric J α ht p z)
        (ManifoldForms.pullback (invariantPart J α) (extChartAt Model p).symm z)
        (extDeriv (coordinateTest J α ht p D q) z)) = normalOperator J α ht p D q z := by
  have hψ := HodgeGeometricCoefficients.frame_smooth
    ((coordinateMetric_smooth J α hs ht p).mono D.domain_subset) D.frame_smooth
  have hφ := starFrame_smooth J α hs ht p D
  have h := HodgeNormalOperator.reconstruct_expansion (coordinateMetric J α ht p) (coordinateJ J p)
    (ManifoldForms.pullback (invariantPart J α) (extChartAt Model p).symm) D.frame q z hd
    (fun j => ((hψ j z hz).contDiffAt (D.domain_open.mem_nhds hz)).differentiableAt (by norm_num))
    (fun j => ((hφ j z hz).contDiffAt (D.domain_open.mem_nhds hz)).differentiableAt (by norm_num))
  obtain ⟨h0,h1,h2,h3⟩ := D.frame_complex z hz
  have hA (i : Fin 4) : HodgeNormalOperator.rawPrincipal (coordinateMetric J α ht p z)
      (ManifoldForms.pullback (invariantPart J α) (extChartAt Model p).symm z) (fun k => D.frame k z)
      (basisForm (coordinateMetric J α ht p z) (fun k => D.frame k z))
      (fun j => MetricHodge.starTwo (coordinateMetric J α ht p z) (coordinateJ J p z)
        (ManifoldForms.pullback (invariantPart J α) (extChartAt Model p).symm z)
        (basisForm (coordinateMetric J α ht p z) (fun k => D.frame k z) j)) i = normalA J α ht p D i z :=
    HodgeNormalOperator.rawPrincipal_eq _ _ _ (D.frame_gram z hz) (coordinateJ J p z)
      (coordinateMetric_hermitian J α ht p (D.domain_subset hz)) h0 h1 h2 h3
      (ManifoldTop.coordinateFundamental J α ht p (D.domain_subset hz)) i
  simp only [hA] at h
  exact h

include hs in
lemma normal_delta {a : TwoForm X} (ha : IsSmooth a) {z : Space} (hz : z ∈ D.domain) :
    HodgeNormalOperator.left (fun i => D.frame i z)
      (ManifoldForms.pullback (codifferential J α ht a) (extChartAt Model p).symm z) +
    HodgeNormalOperator.right (fun i => D.frame i z)
      (ManifoldForms.pullback (codifferential J α ht (ManifoldHodge.starTwo J α ht a))
        (extChartAt Model p).symm z) = -normalOperator J α ht p D (rawVector J α ht p D a) z := by
  rw [pullback_codifferential J α hs ht ha p (D.domain_subset hz),
    pullback_codifferential_star J α hs ht ha p (D.domain_subset hz),map_neg,map_neg,← neg_add]
  congr 1
  have he : ManifoldForms.pullback a (extChartAt Model p).symm =ᶠ[𝓝 z]
      coordinateTest J α ht p D (rawVector J α ht p D a) := by
    filter_upwards [D.domain_open.mem_nhds hz] with y hy
    exact (rawVector_expansion J α ht p D a hy).symm
  have heStar : ManifoldForms.pullback (ManifoldHodge.starTwo J α ht a) (extChartAt Model p).symm =ᶠ[𝓝 z]
      (fun y => MetricHodge.starTwo (coordinateMetric J α ht p y) (coordinateJ J p y)
        (ManifoldForms.pullback (invariantPart J α) (extChartAt Model p).symm y)
        (coordinateTest J α ht p D (rawVector J α ht p D a) y)) := by
    filter_upwards [D.domain_open.mem_nhds hz,he] with y hy hye
    rw [pullback_starTwo J α ht a p (D.domain_subset hy),hye]
  rw [he.extDeriv_eq,heStar.extDeriv_eq]
  exact normal_coordinateTest_at J α hs ht p D
    (((rawVector_smooth J α ht p D ha z hz).contDiffAt
      (D.domain_open.mem_nhds hz)).differentiableAt (by norm_num)) hz

lemma normalOperator_zero_off (q : Space → HodgeNormalSymbol.W) {z : Space} (hz : z ∉ tsupport q) :
    normalOperator J α ht p D q z = 0 := by
  have he : q =ᶠ[𝓝 z] fun _ => 0 := by
    filter_upwards [(isClosed_tsupport q).isOpen_compl.mem_nhds hz] with y hy
    exact image_eq_zero_of_notMem_tsupport hy
  simp [normalOperator,he.fderiv_eq,image_eq_zero_of_notMem_tsupport hz]
end TamingCompatibility.HodgeChart

end
end

end
end

end OAI
