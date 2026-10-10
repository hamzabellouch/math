import Mathlib
import OAI.Analysis.SymmetricDomains.ModelRotationWeight
import OAI.Analysis.SymmetricDomains.InnerExp
import OAI.Analysis.SymmetricDomains.Geometry

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open Set Filter Topology
open Filter Topology
open Filter Topology
open Filter Topology
open Filter Topology
open Polynomial
open Filter Topology
open scoped TensorProduct
open Set Filter Topology
open scoped TensorProduct
open scoped TensorProduct
open Filter Topology
open Filter Topology
open scoped TensorProduct
namespace Release061.Biholomorph

structure WeightedLieModel (r k : ℕ) (G : Type*) [LieRing G] [LieAlgebra ℝ G] where
  field : (ℂ ⊗[ℝ] G) →ₗ[ℂ] (Affine (r+k) → Affine (r+k))
  normal : Fin k → ℝ
  euler : G
  translation : G
  rotation : G
  analytic : ∀ X, AnalyticAt ℂ (field X) (Complex.I • flatNormalVector r k normal)
  jet_injective : ∀ X, ZeroSecondJet (field X) (Complex.I • flatNormalVector r k normal) → X=0
  lie : ∀ X Y, field ⁅X,Y⁆=VectorField.lieBracket ℂ (field X) (field Y)
  euler_germ : field (Complexification.ofReal euler) =ᶠ[𝓝 (Complex.I • flatNormalVector r k normal)]
    fun x => flatWeightedEuler r k x
  translation_germ : field (Complexification.ofReal translation) =ᶠ[𝓝 (Complex.I • flatNormalVector r k normal)]
    fun _ => flatNormalVector r k normal
  rotation_germ : field (Complexification.ofReal rotation) =ᶠ[𝓝 (Complex.I • flatNormalVector r k normal)]
    fun x => flatTangentialInfinitesimal r k x
  nilpotent : IsNilpotent (LieAlgebra.ad ℝ G translation)
  isotropy_real : ∀ X Y : G,
    field (Complexification.ofReal X) (Complex.I • flatNormalVector r k normal)=0 →
    field (Complexification.ofReal Y) (Complex.I • flatNormalVector r k normal)=0 →
    fderiv ℂ (field (Complexification.ofReal Y)) (Complex.I • flatNormalVector r k normal)=
      Complex.I • fderiv ℂ (field (Complexification.ofReal X)) (Complex.I • flatNormalVector r k normal) → X=0

namespace WeightedLieModel
variable {r k : ℕ} {G : Type*} [LieRing G] [LieAlgebra ℝ G]
    (M : WeightedLieModel r k G)

local instance complexificationRatLieAlgebra : LieAlgebra ℚ (ℂ ⊗[ℝ] G) where
  lie_smul scalar left right := by
    rw [←IsScalarTower.algebraMap_smul ℂ scalar right]
    exact (LieAlgebra.lie_smul (R := ℂ) ((algebraMap ℚ ℂ) scalar) left right).trans
      (IsScalarTower.algebraMap_smul ℂ scalar ⁅left,right⁆)

abbrev point : Affine (r+k) := Complex.I • flatNormalVector r k M.normal
abbrev u : Affine (r+k) := flatNormalVector r k M.normal
abbrev E : ℂ ⊗[ℝ] G := Complexification.ofReal M.euler
abbrev T : ℂ ⊗[ℝ] G := Complexification.ofReal M.translation
abbrev H : ℂ ⊗[ℝ] G := Complexification.ofReal M.rotation

theorem eq_of_germ {X Y : ℂ ⊗[ℝ] G} (h : M.field X =ᶠ[𝓝 M.point] M.field Y) : X=Y := by
  apply sub_eq_zero.mp
  apply M.jet_injective
  have he : M.field (X-Y) =ᶠ[𝓝 M.point] (0 : Affine (r+k) → Affine (r+k)) := by
    filter_upwards [h] with x hx
    simp only [map_sub,Pi.sub_apply,hx,sub_self,Pi.zero_apply]
  apply ZeroSecondJet.congr he.symm
  simp [ZeroSecondJet]

theorem lie_germ {X Y : ℂ ⊗[ℝ] G} {f g : Affine (r+k) → Affine (r+k)}
    (hf : M.field X =ᶠ[𝓝 M.point] f) (hg : M.field Y =ᶠ[𝓝 M.point] g) :
    M.field ⁅X,Y⁆ =ᶠ[𝓝 M.point] VectorField.lieBracket ℂ f g := by
  rw [M.lie]
  filter_upwards [hf.eventually_nhds,hg.eventually_nhds] with x hx hy
  have hx' : M.field X =ᶠ[𝓝 x] f := hx
  have hy' : M.field Y =ᶠ[𝓝 x] g := hy
  simp only [VectorField.lieBracket,hx'.eq_of_nhds,hy'.eq_of_nhds,hx'.fderiv_eq,hy'.fderiv_eq]

theorem translation_euler : ⁅M.T,M.E⁆=M.T := by
  apply M.eq_of_germ
  apply (M.lie_germ M.translation_germ M.euler_germ).trans
  filter_upwards [M.translation_germ] with x hx
  rw [hx,VectorField.lieBracket,(flatWeightedEuler r k).fderiv,fderiv_const_apply]
  simp only [zero_apply,sub_zero,flatWeightedEuler_normal]

theorem translation_rotation : ⁅M.T,M.H⁆=0 := by
  apply M.eq_of_germ
  apply (M.lie_germ M.translation_germ M.rotation_germ).trans
  filter_upwards [] with x
  rw [VectorField.lieBracket,(flatTangentialInfinitesimal r k).fderiv,fderiv_const_apply]
  simp only [zero_apply,sub_zero,flatTangentialInfinitesimal_normal,map_zero,Pi.zero_apply]

def center : (ℂ ⊗[ℝ] G) ≃ₗ⁅ℂ⁆ (ℂ ⊗[ℝ] G) :=
  LieAlgebra.innerExp M.T (Complexification.ad_ofReal_nilpotent M.translation M.nilpotent) (-Complex.I)

theorem center_euler : M.center M.E=M.E-Complex.I • M.T := by
  rw [center,LieAlgebra.innerExp_euler _ _ _ M.translation_euler]
  simp [sub_eq_add_neg]

theorem center_rotation : M.center M.H=M.H :=
  LieAlgebra.innerExp_fixed _ _ _ _ M.translation_rotation

theorem center_translation : M.center M.T=M.T :=
  LieAlgebra.innerExp_fixed _ _ _ _ (lie_self _)

theorem centered_euler_germ : M.field (M.center M.E) =ᶠ[𝓝 M.point]
    fun x => flatWeightedEuler r k (x-M.point) := by
  rw [M.center_euler,map_sub,map_smul]
  filter_upwards [M.euler_germ,M.translation_germ] with x hx hy
  simp only [Pi.sub_apply,Pi.smul_apply,hx,hy,map_sub,map_smul,point,flatWeightedEuler_normal]

theorem centered_rotation_germ : M.field (M.center M.H) =ᶠ[𝓝 M.point]
    fun x => flatTangentialInfinitesimal r k (x-M.point) := by
  rw [M.center_rotation]
  filter_upwards [M.rotation_germ] with x hx
  simp only [hx,map_sub,map_smul,point,flatTangentialInfinitesimal_normal,smul_zero,sub_zero]

theorem euler_semisimple : (LieAlgebra.ad ℂ (ℂ ⊗[ℝ] G) M.E).IsSemisimple := by
  exact LieFieldJets.conjugated_ad_semisimple M.field M.point M.analytic M.jet_injective M.lie
    (modelBasis r k) M.center M.E (flatWeightedEuler r k) M.centered_euler_germ modelEulerWeight
    (flatWeightedEuler_basis r k) _ secondJet_modelEulerWeight_mem

theorem euler_extreme_rotation (X : ℂ ⊗[ℝ] G) (hX : ⁅M.E,X⁆=(3/2 : ℂ) • X) :
    ⁅M.H,X⁆= -Complex.I • X := by
  exact LieFieldJets.conjugated_second_ad_relation M.field M.point M.analytic M.jet_injective M.lie
    (modelBasis r k) M.center M.E M.H (flatWeightedEuler r k) (flatTangentialInfinitesimal r k)
    M.centered_euler_germ M.centered_rotation_germ modelEulerWeight modelRotationWeight
    (flatWeightedEuler_basis r k) (flatTangentialInfinitesimal_basis r k) (3/2) (-Complex.I)
    modelEuler_extreme_rotation X hX

theorem euler_extreme_zero (X : ℂ ⊗[ℝ] G) (hX : ⁅M.E,X⁆=(3/2 : ℂ) • X) : X=0 := by
  apply Complexification.eigen_eq_zero_of_imaginary_bracket M.euler (-M.rotation) (3/2)
  · intro Z hZ
    have hz := M.euler_extreme_rotation Z (by simpa using hZ)
    change ⁅Complexification.ofReal (-M.rotation),Z⁆=_
    rw [map_neg,neg_lie]
    change -⁅M.H,Z⁆=_
    rw [hz,neg_smul,neg_neg]
  · simpa using hX

theorem euler_spectrum (μ : ℂ) (hμ : (LieAlgebra.ad ℂ (ℂ ⊗[ℝ] G) M.E).HasEigenvalue μ) :
    μ∈({-1,-(1/2),0,1/2,1} : Finset ℂ) := by
  obtain ⟨j,hj⟩ := LieFieldJets.conjugated_ad_eigenvalue M.field M.point M.analytic
    M.jet_injective M.lie (modelBasis r k) M.center M.E (flatWeightedEuler r k)
    M.centered_euler_germ modelEulerWeight (flatWeightedEuler_basis r k) hμ
  have hm := secondJet_modelEulerWeight_mem j
  rw [hj] at hm
  have hne : μ≠(3/2 : ℂ) := by
    intro he
    obtain ⟨X,hX,hne⟩ := Module.End.HasEigenvalue.exists_hasEigenvector hμ
    have hx := M.euler_extreme_zero X (by simpa [he] using (Module.End.mem_eigenspace_iff.mp hX))
    exact hne hx
  simpa only [Finset.mem_insert,Finset.mem_singleton] using
    (by simpa only [Finset.mem_insert,Finset.mem_singleton,hne,or_false] using hm :
      μ=-1 ∨ μ= -(1/2 : ℂ) ∨ μ=0 ∨ μ=1/2 ∨ μ=1)

end WeightedLieModel
end Release061.Biholomorph

open Filter Topology
open scoped TensorProduct

end

end OAI
