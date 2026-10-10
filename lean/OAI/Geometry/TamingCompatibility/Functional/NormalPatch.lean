import Mathlib
import OAI.Geometry.TamingCompatibility.Charts.LocalFormalAdjoint
import OAI.Geometry.TamingCompatibility.Functional.RawNormal

namespace OAI


noncomputable section
namespace TamingCompatibility.SchwartzCutoff
open Set Filter
open scoped ContDiff Topology SchwartzMap
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
lemma smooth {U : Set E} (hU : IsOpen U) {f : E → F} (hf : ContDiffOn ℝ ∞ f U)
    {φ : E → ℝ} (hφ : ContDiff ℝ ∞ φ) (hs : tsupport φ ⊆ U) :
    ContDiff ℝ ∞ (fun x => φ x • f x) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ tsupport φ
  · exact hφ.contDiffAt.smul ((hf x (hs hx)).contDiffAt (hU.mem_nhds (hs hx)))
  · apply contDiffAt_const.congr_of_eventuallyEq
    filter_upwards [(isClosed_tsupport φ).isOpen_compl.mem_nhds hx] with y hy
    rw [image_eq_zero_of_notMem_tsupport hy,zero_smul]

omit [NormedSpace ℝ E] in
lemma compact {f : E → F} {φ : E → ℝ} (hc : HasCompactSupport φ) :
    HasCompactSupport (fun x => φ x • f x) :=
  hc.of_isClosed_subset (isClosed_tsupport _) (tsupport_smul_subset_left _ _)

def schwartz [FiniteDimensional ℝ E] {U : Set E} (hU : IsOpen U) {f : E → F}
    (hf : ContDiffOn ℝ ∞ f U) {φ : E → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ U) : 𝓢(E,F) :=
  (compact hc).toSchwartzMap (smooth hU hf hφ hs)

@[simp] lemma schwartz_apply [FiniteDimensional ℝ E] {U : Set E} (hU : IsOpen U) {f : E → F}
    (hf : ContDiffOn ℝ ∞ f U) {φ : E → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ U) (x : E) :
    schwartz hU hf hφ hc hs x = φ x • f x := rfl
end TamingCompatibility.SchwartzCutoff

namespace TamingCompatibility.GeometricChart
open ManifoldForms ManifoldHodge LocalMatrixOperator Set Filter LocalFormalAdjoint LineDeriv
open scoped Manifold ContDiff Topology SchwartzMap RealInnerProductSpace LineDeriv
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (hs : IsSmooth α) (ht : Tames α J)
  (p : X) (D : Data J α ht p)
variable {φ : Space → ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
  (hφD : tsupport φ ⊆ D.domain)

def patchA (i : Fin 4) : 𝓢(Space,EuclideanEnergy.Pair →L[ℝ] Space) :=
  SchwartzCutoff.schwartz D.domain_open (normalA_smooth J α ht p D i) hφ hc hφD

def patchB : 𝓢(Space,EuclideanEnergy.Pair →L[ℝ] Space) :=
  SchwartzCutoff.schwartz D.domain_open (normalB_smooth J α hs ht p D) hφ hc hφD

lemma patch_normal (q : 𝓢(Space,EuclideanEnergy.Pair))
    (hq : ∀ z ∈ tsupport q, φ z = 1) (z : Space) :
    firstOrder EuclideanEnergy.e (patchA J α ht p D hφ hc hφD)
      (patchB J α hs ht p D hφ hc hφD) q z = normalOperator J α ht p D q z := by
  by_cases hz : z ∈ tsupport q
  · simp only [firstOrder,_root_.add_apply,_root_.sum_apply,ContinuousLinearMap.comp_apply,
      multiply_apply,patchA,patchB,SchwartzCutoff.schwartz_apply,hq z hz,one_smul,
      lineDerivOpCLM_apply,SchwartzMap.lineDerivOp_apply_eq_fderiv,normalOperator]
  · rw [normalOperator_zero_off J α ht p D q hz]
    have hd (i : Fin 4) : (∂_{EuclideanEnergy.e i} q : 𝓢(Space,EuclideanEnergy.Pair)) z = 0 :=
      image_eq_zero_of_notMem_tsupport (fun h => hz (SchwartzMap.tsupport_lineDerivOp_subset _ _ h))
    simp only [firstOrder,_root_.add_apply,_root_.sum_apply,ContinuousLinearMap.comp_apply,
      multiply_apply,lineDerivOpCLM_apply,hd,image_eq_zero_of_notMem_tsupport hz,map_zero,
      Finset.sum_const_zero,add_zero]
end TamingCompatibility.GeometricChart

end

end OAI
