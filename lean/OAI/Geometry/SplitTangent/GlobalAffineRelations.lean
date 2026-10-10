import Mathlib
import OAI.Geometry.SplitTangent.LeafJetAtlas
import OAI.Geometry.SplitTangent.Basic
import OAI.Geometry.SplitTangent.ProjectiveLinearCoordinates
import OAI.Geometry.SplitTangent.GlobalLeafRelations

namespace OAI

/-! Global Affine Relations. -/

noncomputable section
open Set Filter Topology
open scoped Manifold ContDiff BigOperators
universe u
namespace SplitTangent.LeafJetAtlas
variable {X : ComplexManifold.{u}} {S : TangentSplitting X}
  [CompactSpace X.Carrier] [ConnectedSpace X.Carrier]
  (L : LeafJetAtlas S) (e : ProjectiveEmbedding X)

 
theorem all_leaf_closure_affine_relation (hRC : RationallyConnected e) (hdim : 0<X.dim)
    (x₀ : X.Carrier)
    (p : (Fin (e.N+1) → ℂ) →ₗ[ℂ] (Fin (Module.finrank ℂ (S.first x₀)) → ℂ))
    (i j : Fin (e.N+1)) :
    ∃q : MvPolynomial (Option (Fin (Module.finrank ℂ (S.first x₀)))) ℂ,
      q≠0 ∧ ∀x∈closure (L.leaf x₀),(e.map x).rep i≠0 →
        MvPolynomial.eval (fun t => Option.elim t (projectiveCoordinates i (e.map x) j)
          (p (projectiveCoordinates i (e.map x)))) q=0 := by
  classical
  let r := Module.finrank ℂ (S.first x₀)
  let D : MvPolynomial.homogeneousSubmodule (Fin (e.N+1)) ℂ 1 :=
    ⟨MvPolynomial.X i,MvPolynomial.isHomogeneous_X ℂ i⟩
  let H : Option (Fin r) → MvPolynomial.homogeneousSubmodule (Fin (e.N+1)) ℂ 1 :=
    fun t => Option.elim t ⟨MvPolynomial.X j,MvPolynomial.isHomogeneous_X ℂ j⟩
      (fun a => ProjectiveLinearCoordinates.form ((LinearMap.proj a).comp p))
  obtain ⟨q,hq,hrel⟩ := L.all_leaf_closure_relation e hRC hdim x₀ D (H ∘ finSuccEquiv r)
  refine ⟨MvPolynomial.rename (finSuccEquiv r) q,?_,?_⟩
  · exact fun he => hq ((MvPolynomial.rename_injective _ (finSuccEquiv r).injective)
      (he.trans (map_zero _).symm))
  · intro x hx hi
    have hd : MvPolynomial.eval (e.map x).rep D.val≠0 := by
      simpa only [D,MvPolynomial.eval_X] using hi
    have he := hrel x hx hd
    have hv : ∀t : Option (Fin r),
        MvPolynomial.eval (e.map x).rep (H t).val/MvPolynomial.eval (e.map x).rep D.val =
          Option.elim t (projectiveCoordinates i (e.map x) j) (p (projectiveCoordinates i (e.map x))) := by
      intro t
      cases t with
      | none => simp only [H,D,Option.elim_none,MvPolynomial.eval_X,projectiveCoordinates,div_eq_mul_inv,mul_comm]
      | some a =>
          simp only [H,D,Option.elim_some,MvPolynomial.eval_X]
          rw [ProjectiveLinearCoordinates.eval_form_ratio]
          rfl
    rw [MvPolynomial.eval_rename]
    convert he using 1
    congr 1
    apply congrArg MvPolynomial.eval
    funext t
    exact (hv (finSuccEquiv r t)).symm

end SplitTangent.LeafJetAtlas

end

end OAI
