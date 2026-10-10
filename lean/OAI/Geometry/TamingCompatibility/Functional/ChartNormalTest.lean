import Mathlib
import OAI.Geometry.TamingCompatibility.DifferentialForms.GeometricFrameTest
import OAI.Geometry.TamingCompatibility.Elliptic.NormalSystem

namespace OAI

section
section
section

section
noncomputable section
namespace TamingCompatibility.LocalMatrixOperator
open EuclideanEnergy
lemma pair_fderiv {q : V → Pair} {x v : V} (hq : DifferentiableAt ℝ q x) :
    pair (fderiv ℝ (fun y => q y 0) x v) (fderiv ℝ (fun y => q y 1) x v) =
      fderiv ℝ q x v := by
  have h0 := (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).hasFDerivAt.comp x hq.hasFDerivAt
  have h1 := (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).hasFDerivAt.comp x hq.hasFDerivAt
  change HasFDerivAt (fun y => q y 0) _ x at h0
  change HasFDerivAt (fun y => q y 1) _ x at h1
  rw [h0.fderiv,h1.fderiv]
  ext i
  fin_cases i <;> rfl
end TamingCompatibility.LocalMatrixOperator

namespace TamingCompatibility.GeometricChart
open ManifoldForms ManifoldHodge AntiInvariantFrame LocalMatrixOperator Set Filter
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (hs : IsSmooth α) (ht : Tames α J)
  (p : X) (D : Data J α ht p)

def normalA (i : Fin 4) (z : Space) : EuclideanEnergy.Pair →L[ℝ] Space :=
  normalPrincipal (fun j => D.frame j z) i

def normalB (z : Space) : EuclideanEnergy.Pair →L[ℝ] Space :=
  normalLower (coordinateMetric J α ht p z)
    (TamingCompatibility.pullback (invariantPart J α) (extChartAt Model p).symm z)
    (fun y => realPart (coordinateMetric J α ht p y) (fun i => D.frame i y))
    (fun y => imagPart (coordinateMetric J α ht p y) (fun i => D.frame i y))
    (fun i => D.frame i z) z

include hs in
lemma normal_coordinateTest {q : Space → EuclideanEnergy.Pair}
    (hq : ContDiff ℝ ∞ q) {z : Space} (hz : z ∈ D.domain) :
    frameVector (fun i => D.frame i z)
      (MetricHodge.starThree (coordinateMetric J α ht p z)
        (TamingCompatibility.pullback (invariantPart J α) (extChartAt Model p).symm z)
        (extDeriv (coordinateTest J α ht p D q) z)) =
      (∑ i, normalA J α ht p D i z (fderiv ℝ q z (EuclideanEnergy.e i))) +
        normalB J α ht p D z (q z) := by
  obtain ⟨h0,h1,h2,h3⟩ := D.frame_complex z hz
  have hψ := realPart_smooth ((coordinateMetric_smooth J α hs ht p).mono D.domain_subset) D.frame_smooth
  have hχ := imagPart_smooth ((coordinateMetric_smooth J α hs ht p).mono D.domain_subset) D.frame_smooth
  have hd : DifferentiableAt ℝ q z := hq.differentiable (by norm_num) z
  have h := normal_operator_expansion
    (A := fun y => q y 0) (B := fun y => q y 1)
    (ψ := fun y => realPart (coordinateMetric J α ht p y) (fun i => D.frame i y))
    (χ := fun y => imagPart (coordinateMetric J α ht p y) (fun i => D.frame i y))
    (coordinateMetric J α ht p z)
    (TamingCompatibility.pullback (invariantPart J α) (extChartAt Model p).symm z)
    (fun i => D.frame i z) (D.frame_gram z hz) (coordinateJ J p z) h0 h1 h2 h3
    (fun u v => ManifoldTop.coordinateFundamental J α ht p (D.domain_subset hz) u v)
    rfl rfl (((EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).contDiff.comp hq).differentiable (by norm_num) z)
    (((EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).contDiff.comp hq).differentiable (by norm_num) z)
    (((hψ z hz).contDiffAt (D.domain_open.mem_nhds hz)).differentiableAt (by norm_num))
    (((hχ z hz).contDiffAt (D.domain_open.mem_nhds hz)).differentiableAt (by norm_num))
  simp only [pair_fderiv hd] at h
  have hqz : EuclideanEnergy.pair (q z 0) (q z 1) = q z := by ext i; fin_cases i <;> rfl
  rw [hqz] at h
  exact h

variable [T2Space X]
include hs in
lemma normal_manifoldTest_delta {q : Space → EuclideanEnergy.Pair}
    (hq : ContDiff ℝ ∞ q) (hc : HasCompactSupport q) (hqD : tsupport q ⊆ D.domain)
    {z : Space} (hz : z ∈ D.domain) :
    frameVector (fun i => D.frame i z)
      (ManifoldForms.pullback (codifferential J α ht (manifoldTest J α ht p D q))
        (extChartAt Model p).symm z) =
      -((∑ i, normalA J α ht p D i z (fderiv ℝ q z (EuclideanEnergy.e i))) +
        normalB J α ht p D z (q z)) := by
  rw [pullback_codifferential_antiInvariant J α ht
    (manifoldTest_smooth J α hs ht p D hq hc hqD) (manifoldTest_anti J α ht p D q)
    p (D.domain_subset hz),map_neg]
  have he : ManifoldForms.pullback (manifoldTest J α ht p D q) (extChartAt Model p).symm =ᶠ[𝓝 z]
      coordinateTest J α ht p D q := by
    filter_upwards [(isOpen_extChartAt_target p).mem_nhds (D.domain_subset hz)] with y hy
    exact pullback_manifoldTest J α ht p D hqD hy
  rw [he.extDeriv_eq,normal_coordinateTest J α hs ht p D hq hz]
end TamingCompatibility.GeometricChart

end
end

section
noncomputable section
namespace TamingCompatibility.LocalMatrixOperator
open MetricModel MetricForms EuclideanEnergy
open scoped RealInnerProductSpace

def normalizeFrame (g : Metric V) (b : Fin 4 → V)
    (hb : ∀ i j, g.bilinear (b i) (b j) = if i=j then 1 else 0) : V ≃L[ℝ] V :=
  (MetricModel.equiv g).symm.trans
    (basisOfFrame g (by simp [V]) b hb).repr.toContinuousLinearEquiv

lemma normalizeFrame_apply (g : Metric V) (b : Fin 4 → V)
    (hb : ∀ i j, g.bilinear (b i) (b j) = if i=j then 1 else 0) (i : Fin 4) :
    normalizeFrame g b hb (b i) = e i := by
  change (basisOfFrame g (by simp [V]) b hb).repr (ofOriginal g (b i)) = _
  rw [← basisOfFrame_apply g (by simp [V]) b hb i]
  rw [OrthonormalBasis.repr_self]
  rfl

lemma normalized_frameCovector (g : Metric V) (b : Fin 4 → V)
    (hb : ∀ i j, g.bilinear (b i) (b j) = if i=j then 1 else 0) (i : Fin 4) :
    frameCovector (fun j => normalizeFrame g b hb (b j)) i = e i := by
  ext j
  simp [frameCovector,normalizeFrame_apply,e,eq_comm]
end TamingCompatibility.LocalMatrixOperator

namespace TamingCompatibility.GeometricChart
open ManifoldForms ManifoldHodge AntiInvariantFrame LocalMatrixOperator EuclideanEnergy
open scoped Manifold ContDiff RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (hs : IsSmooth α) (ht : Tames α J)
  (p : X) (D : Data J α ht p)

lemma normalA_smooth (i : Fin 4) : ContDiffOn ℝ ∞ (normalA J α ht p D i) D.domain := by
  apply contDiffOn_clm_apply.mpr
  intro q
  apply (contDiffOn_piLp 2).mpr
  intro j
  have hc (k : Fin 4) : ContDiffOn ℝ ∞ (fun z => D.frame k z i) D.domain :=
    (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp_contDiffOn (D.frame_smooth k)
  fin_cases j
  · exact (contDiffOn_const.mul (hc 2).neg).add (contDiffOn_const.mul (hc 3).neg)
  · exact (contDiffOn_const.mul (hc 3)).add (contDiffOn_const.mul (hc 2).neg)
  · exact (contDiffOn_const.mul (hc 0)).add (contDiffOn_const.mul (hc 1))
  · exact (contDiffOn_const.mul (hc 1).neg).add (contDiffOn_const.mul (hc 0))

include hs in
lemma realDeriv_smooth : ContDiffOn ℝ ∞ (fun z => extDeriv
    (fun y => realPart (coordinateMetric J α ht p y) (fun i => D.frame i y)) z) D.domain := by
  have hψ := realPart_smooth ((coordinateMetric_smooth J α hs ht p).mono D.domain_subset) D.frame_smooth
  exact (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ Space ℝ).contDiff.comp_contDiffOn
    (hψ.fderiv_of_isOpen (m := ∞) D.domain_open (by simp))

include hs in
lemma imagDeriv_smooth : ContDiffOn ℝ ∞ (fun z => extDeriv
    (fun y => imagPart (coordinateMetric J α ht p y) (fun i => D.frame i y)) z) D.domain := by
  have hχ := imagPart_smooth ((coordinateMetric_smooth J α hs ht p).mono D.domain_subset) D.frame_smooth
  exact (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ Space ℝ).contDiff.comp_contDiffOn
    (hχ.fderiv_of_isOpen (m := ∞) D.domain_open (by simp))

include hs in
lemma normalStar_smooth : ContDiffOn ℝ ∞ (fun z => MetricHodge.starThreeCLM
    (coordinateMetric J α ht p z)
    (TamingCompatibility.pullback (invariantPart J α) (extChartAt Model p).symm z)) D.domain := by
  exact SmoothHodge.starThreeCLM_contDiffOn (coordinateMetric J α ht p)
    (coordinateJ J p) (by simp [Space]) D.domain_open
    ((coordinateMetric_smooth J α hs ht p).mono D.domain_subset)
    ((coordinateJ_smooth J p).mono D.domain_subset)
    (fun z hz => coordinateJ_square J p (D.domain_subset hz))
    (fun z hz => coordinateMetric_hermitian J α ht p (D.domain_subset hz))
    ((smooth_chart _ (hs.invariantPart J) p).mono D.domain_subset)

include hs in
lemma normalB_smooth : ContDiffOn ℝ ∞ (normalB J α ht p D) D.domain := by
  apply contDiffOn_clm_apply.mpr
  intro q
  apply (contDiffOn_piLp 2).mpr
  intro i
  change ContDiffOn ℝ ∞ (fun z => (MetricHodge.starThreeCLM
    (coordinateMetric J α ht p z)
    (TamingCompatibility.pullback (invariantPart J α) (extChartAt Model p).symm z)
    ((q 0) • extDeriv (fun y => realPart (coordinateMetric J α ht p y) (fun j => D.frame j y)) z +
     (q 1) • extDeriv (fun y => imagPart (coordinateMetric J α ht p y) (fun j => D.frame j y)) z))
      (fun _ : Fin 1 => D.frame i z)) D.domain
  exact FormSmooth.contDiffOn_apply
    ((normalStar_smooth J α hs ht p D).clm_apply
      (((realDeriv_smooth J α hs ht p D).const_smul (q 0)).add
       ((imagDeriv_smooth J α hs ht p D).const_smul (q 1))))
    (fun _ => D.frame_smooth i)

def normalMetric (i j : Fin 4) (z : Space) : ℝ :=
  ⟪frameCovector (fun k => D.frame k z) i,frameCovector (fun k => D.frame k z) j⟫

lemma normalMetric_smooth (i j : Fin 4) :
    ContDiffOn ℝ ∞ (normalMetric J α ht p D i j) D.domain := by
  have hc (i : Fin 4) : ContDiffOn ℝ ∞ (fun z => frameCovector (fun k => D.frame k z) i) D.domain := by
    apply (contDiffOn_piLp 2).mpr
    intro k
    exact (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp_contDiffOn (D.frame_smooth k)
  exact ContDiffOn.inner ℝ (hc i) (hc j)
end TamingCompatibility.GeometricChart

end
end

end
end
end

end OAI
