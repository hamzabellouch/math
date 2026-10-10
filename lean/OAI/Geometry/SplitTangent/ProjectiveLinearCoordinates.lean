import Mathlib
import OAI.Geometry.SplitTangent.TensorVanishing
import OAI.Geometry.SplitTangent.Basic

namespace OAI

/-! Projective Linear Coordinates. -/

noncomputable section
open Set Filter Topology
open scoped Manifold ContDiff BigOperators
universe u
namespace ProjectiveLinearCoordinates
open _root_.MvPolynomial _root_.OAI.MvPolynomial
variable {σ : Type*} [Fintype σ]

 
def form (l : (σ → ℂ) →ₗ[ℂ] ℂ) : homogeneousSubmodule σ ℂ 1 := by
  classical
  exact ∑i,l (Pi.single i 1) • ⟨X i,isHomogeneous_X ℂ i⟩

lemma eval_form (l : (σ → ℂ) →ₗ[ℂ] ℂ) (x : σ → ℂ) : eval x (form l).val=l x := by
  classical
  have he : (∑i,x i • Pi.single i (1 : ℂ))=x := by
    ext j
    simp [Pi.single_apply]
  calc
    _ = ∑i,x i*l (Pi.single i 1) := by
      simp only [form,Submodule.coe_sum,Submodule.coe_smul,map_sum,MvPolynomial.smul_eval,eval_X]
      apply Finset.sum_congr rfl
      intro i hi
      exact mul_comm _ _
    _ = l (∑i,x i • Pi.single i 1) := by simp only [map_sum,map_smul,smul_eq_mul]
    _ = l x := congrArg l he

lemma eval_form_ratio (l : (σ → ℂ) →ₗ[ℂ] ℂ) (x : σ → ℂ) (i : σ) :
    eval x (form l).val / x i=l ((x i)⁻¹ • x) := by
  rw [eval_form,map_smul]
  simp only [smul_eq_mul,div_eq_mul_inv,mul_comm]

end ProjectiveLinearCoordinates
namespace SplitTangent.ProjectiveEmbedding
variable {X : ComplexManifold.{u}} (e : ProjectiveEmbedding X)
  {S : TangentSplitting X} {A B : Type*}
  [NormedAddCommGroup A] [NormedSpace ℂ A] [FiniteDimensional ℂ A]
  [NormedAddCommGroup B] [NormedSpace ℂ B] [FiniteDimensional ℂ B]

omit [FiniteDimensional ℂ A] [FiniteDimensional ℂ B] in
lemma plaque_coordinates_analytic (P : AlignedProductChart S A B)
    {z : A × B} (hz : z∈P.chart.target) (i : Fin (e.N+1))
    (hi : (e.map (P.chart.symm z)).rep i≠0) :
    AnalyticAt ℂ (fun t => projectiveCoordinates i (e.map (P.chart.symm t))) z :=
  (((e.holomorphic i).contMDiffAt ((e.open_patch i).mem_nhds hi)).comp z
    (P.inverse_holomorphicAt hz)).contDiffAt.analyticAt

omit [FiniteDimensional ℂ A] [FiniteDimensional ℂ B] in
lemma plaque_coordinates_first_injective (P : AlignedProductChart S A B)
    {z : A × B} (hz : z∈P.chart.target) (i : Fin (e.N+1))
    (hi : (e.map (P.chart.symm z)).rep i≠0) :
    Function.Injective ((fderiv ℂ (fun t => projectiveCoordinates i (e.map (P.chart.symm t))) z).comp
      (ContinuousLinearMap.inl ℂ A B)) := by
  have hd := mfderiv_comp z
    (((e.holomorphic i).contMDiffAt ((e.open_patch i).mem_nhds hi)).mdifferentiableAt (by simp))
    ((P.inverse_holomorphicAt hz).mdifferentiableAt (by simp))
  rw [mfderiv_eq_fderiv] at hd
  change Function.Injective ((fderiv ℂ ((fun x => projectiveCoordinates i (e.map x)) ∘ P.chart.symm) z).comp
    (ContinuousLinearMap.inl ℂ A B))
  rw [hd]
  exact (e.immersion _ i hi).comp ((P.mdifferentiable.symm.mfderiv_injective hz).comp
    (fun _ _ h => congrArg Prod.fst h))

lemma coordinates_injOn (i : Fin (e.N+1)) :
    Set.InjOn (fun x => projectiveCoordinates i (e.map x)) {x | (e.map x).rep i≠0} := by
  intro x hx y hy h
  apply e.injective
  rw [←Projectivization.mk_rep (e.map x),←Projectivization.mk_rep (e.map y),
    Projectivization.mk_eq_mk_iff']
  refine ⟨(e.map x).rep i*((e.map y).rep i)⁻¹,?_⟩
  ext j
  have hh := congrFun h j
  change ((e.map x).rep i)⁻¹*(e.map x).rep j=
    ((e.map y).rep i)⁻¹*(e.map y).rep j at hh
  change ((e.map x).rep i*((e.map y).rep i)⁻¹)*(e.map y).rep j=(e.map x).rep j
  calc
    _ = (e.map x).rep i*(((e.map y).rep i)⁻¹*(e.map y).rep j) := by ring
    _ = (e.map x).rep i*(((e.map x).rep i)⁻¹*(e.map x).rep j) := by rw [hh]
    _ = _ := by rw [←mul_assoc,mul_inv_cancel₀ hx,one_mul]

 

theorem exists_linear_plaque_coordinates (P : AlignedProductChart S A B)
    {z : A × B} (hz : z∈P.chart.target) (i : Fin (e.N+1))
    (hi : (e.map (P.chart.symm z)).rep i≠0) :
    ∃(p : (Fin (e.N+1) → ℂ) →L[ℂ] A)
      (Q : OpenPartialHomeomorph (A × B) (A × B)), z∈Q.source ∧
      (∀t,Q t=(p (projectiveCoordinates i (e.map (P.chart.symm t))),t.2)) ∧
      AnalyticAt ℂ Q z ∧ AnalyticAt ℂ Q.symm (Q z) :=
  RectangularInverse.exists_chart (e.plaque_coordinates_analytic P hz i hi)
    (e.plaque_coordinates_first_injective P hz i hi)

end SplitTangent.ProjectiveEmbedding

end

end OAI
