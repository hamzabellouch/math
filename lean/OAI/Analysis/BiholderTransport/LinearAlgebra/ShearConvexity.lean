import Mathlib
import OAI.Analysis.BiholderTransport.LinearAlgebra.ActualRadial

namespace OAI

section
section
noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
section ShearConvexity
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

def radialHessianDefectBilinear (x : M) (p : TangentSpace 𝓘(ℝ,Model n) x) (δ : ℝ) :
    TangentSpace 𝓘(ℝ,Model n) x →L[ℝ] TangentSpace 𝓘(ℝ,Model n) x →L[ℝ] ℝ :=
  (-δ) • (normalHessian x ((1-δ) • p) -
    (innerSL ℝ (E := TangentSpace 𝓘(ℝ,Model n) x)).restrictScalars ℝ)

omit [CompactSpace M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)] [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma radialHessianDefect_apply (x : M) (p : TangentSpace 𝓘(ℝ,Model n) x)
    (δ : ℝ) (u v : TangentSpace 𝓘(ℝ,Model n) x) :
    radialHessianDefectBilinear x p δ u v =
      -δ*(normalHessian x ((1-δ) • p) u v-inner ℝ u v) := rfl

lemma radialHessianDefect_symm {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x} {δ : ℝ}
    (hp : (1-δ) • p∈injectivityDomain x) (u v : TangentSpace 𝓘(ℝ,Model n) x) :
    radialHessianDefectBilinear x p δ u v=radialHessianDefectBilinear x p δ v u := by
  simp only [radialHessianDefect_apply,normalHessian_symm hp u v,real_inner_comm u v]

lemma radialHessianDefect_radial {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x} {δ : ℝ}
    (hδ : δ≠1) (hp : (1-δ) • p∈injectivityDomain x)
    (v : TangentSpace 𝓘(ℝ,Model n) x) : radialHessianDefectBilinear x p δ p v=0 := by
  rw [radialHessianDefect_apply,normalHessian_contracted_radial (sub_ne_zero.mpr hδ.symm) hp]
  ring

lemma radialHessianDefect_add_radial {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x} {δ : ℝ}
    (hδ : δ≠1) (hp : (1-δ) • p∈injectivityDomain x)
    (z : TangentSpace 𝓘(ℝ,Model n) x) (a : ℝ) :
    radialHessianDefectBilinear x p δ (z+a • p) (z+a • p)=radialHessianDefectBilinear x p δ z z := by
  simp only [map_add,map_smul,add_apply,smul_apply,
    smul_eq_mul,radialHessianDefect_radial hδ hp]
  rw [radialHessianDefect_symm hp z p,radialHessianDefect_radial hδ hp]
  ring

def spectralShear {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (p q : E) (t : ℝ) : E →L[ℝ] E :=
  ContinuousLinearMap.id ℝ E + (t / inner ℝ p q) • (innerSL ℝ q).smulRight q

lemma spectralShear_apply {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (p q z : E) (t : ℝ) : spectralShear p q t z=z+(t*(inner ℝ z q/inner ℝ p q)) • q := by
  simp only [spectralShear,add_apply,ContinuousLinearMap.id_apply,
    smul_apply,ContinuousLinearMap.smulRight_apply,innerSL_apply_apply,
    smul_smul,real_inner_comm q z]
  congr 2
  ring

lemma spectralShear_transverse_representative {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (p q z : E) (t : ℝ) :
    z-(inner ℝ z q/inner ℝ p q) • p=
      spectralShear p q t z+(-(inner ℝ z q/inner ℝ p q)) • (p+t • q) := by
  rw [spectralShear_apply,smul_add,smul_smul]
  module

lemma spectralShear_transverse {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (p q z : E) (hpq : inner ℝ p q≠0) :
    inner ℝ (z-(inner ℝ z q/inner ℝ p q) • p) q=0 := by
  simp only [inner_sub_left,real_inner_smul_left,div_mul_cancel₀ _ hpq,sub_self]

lemma radialHessianDefect_shear {x : M} {p q : TangentSpace 𝓘(ℝ,Model n) x} {δ t : ℝ}
    (hδ : δ≠1) (hp : (1-δ) • (p+t • q)∈injectivityDomain x)
    (z : TangentSpace 𝓘(ℝ,Model n) x) :
    radialHessianDefectBilinear x (p+t • q) δ (spectralShear p q t z) (spectralShear p q t z)=
    radialHessianDefectBilinear x (p+t • q) δ
      (z-(inner ℝ z q/inner ℝ p q) • p) (z-(inner ℝ z q/inner ℝ p q) • p) := by
  rw [spectralShear_transverse_representative p q z t]
  exact (radialHessianDefect_add_radial hδ hp _ _).symm

lemma WeakMTW.spectralShear_convexOn (hmtw : WeakMTW (n := n) (M := M))
    (x : M) (p q : TangentSpace 𝓘(ℝ,Model n) x) (hpq : inner ℝ p q≠0)
    {δ : ℝ} (hδ0 : 0≤δ) (hδ1 : δ≠1) {D : Set ℝ} (hD : Convex ℝ D)
    (hline : ∀ t∈D, (1-δ) • (p+t • q)∈injectivityDomain x)
    (z : TangentSpace 𝓘(ℝ,Model n) x) :
    ConvexOn ℝ D (fun t => radialHessianDefectBilinear x (p+t • q) δ
      (spectralShear p q t z) (spectralShear p q t z)) := by
  let ξ := z-(inner ℝ z q/inner ℝ p q) • p
  have hξ : inner ℝ ξ ((1-δ) • q)=0 := by
    rw [real_inner_smul_right,spectralShear_transverse p q z hpq,mul_zero]
  have hlin : ∀ t∈D, (1-δ) • p+t • ((1-δ) • q)∈injectivityDomain x := by
    intro t ht
    convert hline t ht using 1
    module
  have H := hmtw.transverse_concaveOn_injectivityDomain x ((1-δ) • p) ξ
    ((1-δ) • q) hD hlin hξ
  refine ⟨hD,?_⟩
  intro a ha b hb u v hu hv huv
  have hc := hD ha hb hu hv huv
  have HA := H.2 ha hb hu hv huv
  simp only [smul_eq_mul] at HA
  have heq (t : ℝ) (ht : t∈D) :
      radialHessianDefectBilinear x (p+t • q) δ (spectralShear p q t z) (spectralShear p q t z)=
      -δ*(hessianValue x ((1-δ) • p+t • ((1-δ) • q)) ξ-inner ℝ ξ ξ) := by
    rw [radialHessianDefect_shear hδ1 (hline t ht),radialHessianDefect_apply]
    rw [hessianValue_eq_normalHessian (hlin t ht)]
    have hr : (1-δ) • (p+t • q)=(1-δ) • p+t • ((1-δ) • q) := by module
    rw [hr]
  dsimp only
  rw [heq _ hc,heq a ha,heq b hb]
  simp only [smul_eq_mul]
  have hcst := congrArg (fun r : ℝ => r*(δ*inner ℝ ξ ξ)) huv
  nlinarith [mul_le_mul_of_nonneg_left HA hδ0]

end ShearConvexity
end WeakMTWTransport

end

end

end

end OAI
