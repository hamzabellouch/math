import Mathlib
import OAI.Geometry.SplitTangent.TensorVanishing
import OAI.Geometry.SplitTangent.LeafJetAtlas
import OAI.Geometry.SplitTangent.Basic
import OAI.Geometry.SplitTangent.PositiveTangentCurves
import OAI.Geometry.SplitTangent.ProjectiveLinearCoordinates
import OAI.Geometry.SplitTangent.RationalCurveFrames
import OAI.Geometry.SplitTangent.LeafClosureRelations

namespace OAI

/-! Leaf Affine Relations. -/

noncomputable section
open Set Filter Topology
open scoped Manifold ContDiff BigOperators
universe u
namespace SplitTangent.RationalCurveFrames
variable {X : ComplexManifold.{u}} {S : TangentSplitting X}
  {e : ProjectiveEmbedding X} {g : RationalCurve X} (F : RationalCurveFrames e g)
  (L : LeafJetAtlas S)
  {A B : Type*}
  [NormedAddCommGroup A] [NormedSpace ℂ A] [CompleteSpace A]
  [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B]
  (P : AlignedProductChart S A B)

include F in
 

theorem leaf_closure_affine_relation
    (hy : g.finite 1∈P.chart.source) (ht : g.TangentTo S.first)
    (hg : PointedGenerated g S.first)
    (p : (Fin (e.N+1) → ℂ) →ₗ[ℂ] (Fin (Module.finrank ℂ (S.first (g.finite 1))) → ℂ))
    (i j : Fin (e.N+1)) :
    ∃q : MvPolynomial (Option (Fin (Module.finrank ℂ (S.first (g.finite 1))))) ℂ,
      q≠0 ∧ ∀x∈closure (L.leaf (g.finite 1)),(e.map x).rep i≠0 →
        MvPolynomial.eval (fun t => Option.elim t (projectiveCoordinates i (e.map x) j)
          (p (projectiveCoordinates i (e.map x)))) q=0 := by
  classical
  let r := Module.finrank ℂ (S.first (g.finite 1))
  let D : MvPolynomial.homogeneousSubmodule (Fin (e.N+1)) ℂ 1 :=
    ⟨MvPolynomial.X i,MvPolynomial.isHomogeneous_X ℂ i⟩
  let H : Option (Fin r) → MvPolynomial.homogeneousSubmodule (Fin (e.N+1)) ℂ 1 :=
    fun t => Option.elim t ⟨MvPolynomial.X j,MvPolynomial.isHomogeneous_X ℂ j⟩
      (fun a => ProjectiveLinearCoordinates.form ((LinearMap.proj a).comp p))
  obtain ⟨q,hq,hrel⟩ := F.leaf_closure_relation L P hy ht hg D (H ∘ finSuccEquiv r)
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

end SplitTangent.RationalCurveFrames

end

end OAI
