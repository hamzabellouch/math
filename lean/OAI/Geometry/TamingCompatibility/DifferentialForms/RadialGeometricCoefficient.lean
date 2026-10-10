import Mathlib
import OAI.Geometry.TamingCompatibility.Functional.NormalPatch
import OAI.Geometry.TamingCompatibility.Functional.WeakNormalEquation
import OAI.Geometry.TamingCompatibility.Charts.ChartReconstruction
import OAI.Geometry.TamingCompatibility.Charts.ScalarChartLift
import OAI.Geometry.TamingCompatibility.DifferentialForms.RadialCoefficientProfiles

namespace OAI

section
section

section

noncomputable section
namespace TamingCompatibility.GeometricChart
open ManifoldForms ManifoldHodge Set Filter
open scoped Manifold ContDiff Topology
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
variable (J : AlmostComplexStructure X) (p : X)

def antiDdcVector (u v : Space → Space) (z : Space) : Space :=
  (1/2:ℝ) • ((fderiv ℝ (coordinateJ J p) z (v z)) (u z) -
    (fderiv ℝ (coordinateJ J p) z (u z)) (v z) +
    (fderiv ℝ (coordinateJ J p) z (coordinateJ J p z (u z))) (coordinateJ J p z (v z)) -
    (fderiv ℝ (coordinateJ J p) z (coordinateJ J p z (v z))) (coordinateJ J p z (u z)))

lemma antiDdcVector_smooth {U : Set Space} (hU : IsOpen U)
    (hUt : U ⊆ (extChartAt Model p).target) {u v : Space → Space}
    (hu : ContDiffOn ℝ ∞ u U) (hv : ContDiffOn ℝ ∞ v U) :
    ContDiffOn ℝ ∞ (antiDdcVector J p u v) U := by
  have hj := (coordinateJ_smooth J p).mono hUt
  have hd := hj.fderiv_of_isOpen hU (m := ∞) (by simp)
  exact ContDiffOn.const_smul (1/2:ℝ) ((((hd.clm_apply hv).clm_apply hu).sub
    ((hd.clm_apply hu).clm_apply hv)).add
      ((hd.clm_apply (hj.clm_apply hu)).clm_apply (hj.clm_apply hv)) |>.sub
      ((hd.clm_apply (hj.clm_apply hv)).clm_apply (hj.clm_apply hu)))

lemma anti_ddc_apply_vector {f : X → ℝ} (hf : ContMDiff Model 𝓘(ℝ,ℝ) ∞ f)
    (u v : Space → Space) {z : Space} (hz : z ∈ (extChartAt Model p).target) :
    ManifoldForms.pullback (antiInvariantPart J (exteriorDerivative (complexDifferential J f)))
      (extChartAt Model p).symm z ![u z,v z] =
      fderiv ℝ (f ∘ (extChartAt Model p).symm) z (antiDdcVector J p u v z) := by
  rw [anti_ddc_chart_first_order J hf p hz]
  simp only [antiDdcVector,map_smul,smul_eq_mul]

variable {α : TwoForm X} {ht : Tames α J} (D : Data J α ht p)

def radialSourceVector (j : Fin 2) : Space → Space :=
  antiDdcVector J p (D.frame 0) (D.frame (if j = 0 then 2 else 3))

lemma radialSourceVector_smooth (j : Fin 2) :
    ContDiffOn ℝ ∞ (radialSourceVector J p D j) D.domain :=
  antiDdcVector_smooth J p D.domain_open D.domain_subset
    (D.frame_smooth 0) (D.frame_smooth _)

def radialSourceExtension {φ : Space → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) (hφD : tsupport φ ⊆ D.domain) (j : Fin 2) :
    SchwartzMap Space Space :=
  SchwartzCutoff.schwartz D.domain_open (radialSourceVector_smooth J p D j) hφ hc hφD

lemma anti_ddc_radialSourceExtension [T2Space X]
    {φ : Space → ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (hφD : tsupport φ ⊆ D.domain) {f : Space → ℝ} (hf : ContDiff ℝ ∞ f)
    (hfc : HasCompactSupport f) (hft : tsupport f ⊆ (extChartAt Model p).target)
    {z : Space} (hz : z ∈ D.domain) (hφz : φ z = 1) (j : Fin 2) :
    ManifoldForms.pullback (antiInvariantPart J (exteriorDerivative
        (complexDifferential J (scalarChartLift p f)))) (extChartAt Model p).symm z
        ![D.frame 0 z,D.frame (if j = 0 then 2 else 3) z] =
      RadialPotential.firstOrderSource (radialSourceExtension J p D hφ hc hφD j) f z := by
  rw [anti_ddc_apply_vector J p (scalarChartLift_smooth p hf hfc hft) _ _ (D.domain_subset hz),scalarChartLift_fderiv p f (D.domain_subset hz)]
  simp only [RadialPotential.firstOrderSource,radialSourceExtension,
    SchwartzCutoff.schwartz_apply,hφz,one_smul,radialSourceVector]

end TamingCompatibility.GeometricChart

end
end

section

noncomputable section
namespace TamingCompatibility.ManifoldForms
open Set Filter
open scoped Manifold ContDiff Topology
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]

lemma complexDifferential_zero_of_eventually (J : AlmostComplexStructure X)
    {f : X → ℝ} {x : X} (hf : f =ᶠ[𝓝 x] fun _ => 0) : complexDifferential J f x = 0 := by
  have he := hf.mfderiv_eq (I := Model) (I' := 𝓘(ℝ,ℝ))
  rw [mfderiv_const] at he
  ext v
  change -(mfderiv Model 𝓘(ℝ,ℝ) f x) (J.endomorphism x (v 0)) = 0
  rw [he]
  change -(0:ℝ) = 0
  exact neg_zero

lemma anti_ddc_zero_off (J : AlmostComplexStructure X) (f : X → ℝ)
    {x : X} (hx : x ∉ tsupport f) :
    antiInvariantPart J (exteriorDerivative (complexDifferential J f)) x = 0 := by
  have hd : exteriorDerivative (complexDifferential J f) x = 0 := by
    apply exteriorDerivative_eq_zero_of_eventually
    filter_upwards [(isClosed_tsupport f).isOpen_compl.mem_nhds hx] with y hy
    apply complexDifferential_zero_of_eventually J
    filter_upwards [(isClosed_tsupport f).isOpen_compl.mem_nhds hy] with z hz
    exact image_eq_zero_of_notMem_tsupport hz
  ext v
  simp [antiInvariantPart,TamingCompatibility.jAction,hd]

end TamingCompatibility.ManifoldForms

namespace TamingCompatibility.GeometricChart
open ManifoldForms ManifoldHodge Set Filter ComplexMatrix
open scoped Manifold ContDiff Topology SchwartzMap
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
variable (J : AlmostComplexStructure X) (p : X) {α : TwoForm X} {ht : Tames α J}
  (D : Data J α ht p)
variable {φ : Space → ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
  (hφD : tsupport φ ⊆ D.domain)
variable {f : Space → ℝ} (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)

def radialScalarSource (j : Fin 2) : 𝓢(Space,ℝ) := by
  have hc' : HasCompactSupport
      (RadialPotential.firstOrderSource (radialSourceExtension J p D hφ hc hφD j) f) :=
    hfc.of_isClosed_subset (isClosed_tsupport _) (RadialPotential.firstOrderSource_tsupport _ _)
  exact hc'.toSchwartzMap (RadialPotential.firstOrderSource_smooth _
    ((radialSourceExtension J p D hφ hc hφD j).smooth ⊤) f hf)

lemma radialScalarSource_support (j : Fin 2) :
    tsupport (radialScalarSource J p D hφ hc hφD hf hfc j) ⊆ tsupport f :=
  RadialPotential.firstOrderSource_tsupport _ _

def radialPairSource : 𝓢(Space,EuclideanEnergy.Pair) :=
  componentTest 0 (radialScalarSource J p D hφ hc hφD hf hfc 0) +
  componentTest 1 (radialScalarSource J p D hφ hc hφD hf hfc 1)

lemma radialPairSource_apply (z : Space) (j : Fin 2) :
    radialPairSource J p D hφ hc hφD hf hfc z j =
      RadialPotential.firstOrderSource (radialSourceExtension J p D hφ hc hφD j) f z := by
  fin_cases j <;> simp [radialPairSource,componentTest_apply,radialScalarSource,EuclideanSpace.single] <;> rfl

lemma radialPairSource_support :
    tsupport (radialPairSource J p D hφ hc hφD hf hfc) ⊆ tsupport f := by
  apply (tsupport_add _ _).trans
  apply union_subset
  · exact (GeometricHilbert.componentTest_support _ _).trans (radialScalarSource_support J p D hφ hc hφD hf hfc 0)
  · exact (GeometricHilbert.componentTest_support _ _).trans (radialScalarSource_support J p D hφ hc hφD hf hfc 1)

lemma radialPairSource_compact :
    HasCompactSupport (radialPairSource J p D hφ hc hφD hf hfc : Space → _) :=
  hfc.of_isClosed_subset (isClosed_tsupport _) (radialPairSource_support J p D hφ hc hφD hf hfc)

lemma anti_ddc_eq_manifoldTest [T2Space X] (hfD : tsupport f ⊆ D.domain)
    (hφone : ∀ z ∈ tsupport f, φ z = 1) :
    antiInvariantPart J (exteriorDerivative (complexDifferential J (scalarChartLift p f))) =
      manifoldTest J α ht p D (radialPairSource J p D hφ hc hφD hf hfc) := by
  let a := antiInvariantPart J (exteriorDerivative (complexDifferential J (scalarChartLift p f)))
  let q := radialPairSource J p D hφ hc hφD hf hfc
  have hqs : tsupport q ⊆ tsupport f := radialPairSource_support J p D hφ hc hφD hf hfc
  have hqt : tsupport q ⊆ D.domain := hqs.trans hfD
  have hft := hfD.trans D.domain_subset
  have has : ContMDiff Model 𝓘(ℝ,ℝ) ∞ (scalarChartLift p f) := scalarChartLift_smooth p hf hfc hft
  have hchart {z : Space} (hz : z ∈ (extChartAt Model p).target) :
      ManifoldForms.pullback a (extChartAt Model p).symm z = coordinateTest J α ht p D q z := by
    by_cases hzf : z ∈ tsupport f
    · have hex := rawScalar_expansion J α ht p D (a := a) (antiInvariantPart_idempotent J _) (hfD hzf)
      change ManifoldForms.pullback a (extChartAt Model p).symm z = _ at hex
      rw [hex]
      have hc0 := anti_ddc_radialSourceExtension J p D hφ hc hφD hf hfc hft (hfD hzf) (hφone z hzf) 0
      have hc1 := anti_ddc_radialSourceExtension J p D hφ hc hφD hf hfc hft (hfD hzf) (hφone z hzf) 1
      change rawScalar J α ht p D a 2 z = _ at hc0
      change rawScalar J α ht p D a 3 z = _ at hc1
      simp only [coordinateTest,LocalMatrixOperator.frameTest,q,
        radialPairSource_apply,hc0,hc1]
    · have hd : fderiv ℝ f z = 0 := image_eq_zero_of_notMem_tsupport
        (fun h => hzf (tsupport_fderiv_subset ℝ h))
      have hqz : q z = 0 := image_eq_zero_of_notMem_tsupport (fun h => hzf (hqs h))
      rw [show coordinateTest J α ht p D q z = 0 from LocalMatrixOperator.frameTest_zero hqz]
      ext v
      have hv : v = ![v 0,v 1] := by ext i; fin_cases i <;> rfl
      rw [hv]
      change ManifoldForms.pullback (antiInvariantPart J (exteriorDerivative
        (complexDifferential J (scalarChartLift p f)))) (extChartAt Model p).symm z ![v 0,v 1] = 0
      rw [anti_ddc_chart_first_order J has p hz,scalarChartLift_fderiv p f hz,hd]
      simp
  ext x v
  by_cases hxs : x ∈ (extChartAt Model p).source
  · have h := form_eq_of_chart_pullback p a (manifoldTest J α ht p D q) hxs (by
      exact (hchart ((extChartAt Model p).map_source hxs)).trans
        (pullback_manifoldTest J α ht p D hqt ((extChartAt Model p).map_source hxs)).symm)
    exact congrArg (fun b : Space [⋀^Fin 2]→L[ℝ] ℝ => b v) h
  · have hxf : x ∉ tsupport (scalarChartLift p f) := fun h =>
      hxs (scalarLiftSupport_subset p hft (scalarChartLift_tsupport p hfc hft h))
    have hz := anti_ddc_zero_off J (scalarChartLift p f) hxf
    have hm : manifoldTest J α ht p D q x = 0 := by
      have hh : chartLift p (coordinateTest J α ht p D q) x = 0 := by
        simp only [chartLift,ite_eq_right hxs]
      ext w
      simp [manifoldTest,antiInvariantPart,TamingCompatibility.jAction,hh]
    exact congrArg (fun b : Space [⋀^Fin 2]→L[ℝ] ℝ => b v) (hz.trans hm.symm)

end TamingCompatibility.GeometricChart

end
end

end
end

end OAI
