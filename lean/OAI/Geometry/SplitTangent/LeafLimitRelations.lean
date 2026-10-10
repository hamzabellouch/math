import Mathlib
import OAI.Geometry.SplitTangent.BoxRelationLocus
import OAI.Geometry.SplitTangent.CompactPolynomialRelations
import OAI.Geometry.SplitTangent.LeafJetAtlas
import OAI.Geometry.SplitTangent.Basic
import OAI.Geometry.SplitTangent.PolynomialRelationLocus
import OAI.Geometry.SplitTangent.ProjectiveLinearCoordinates
import OAI.Geometry.SplitTangent.LeafCompactLimits

namespace OAI

/-! Leaf Limit Relations. -/

noncomputable section
open Set Filter Topology TopologicalSpace
open scoped Manifold ContDiff BigOperators
universe u
namespace SplitTangent.LeafJetAtlas
variable {X : ComplexManifold.{u}} {S : TangentSplitting X}
  [CompactSpace X.Carrier] [ConnectedSpace X.Carrier]
  (L : LeafJetAtlas S) (e : ProjectiveEmbedding X)
  (hRC : RationallyConnected e) (hdim : 0<X.dim)

lemma leafLimits_relation {K : Compacts X.Carrier} (hK : K∈L.leafLimits e hRC hdim)
    (x₀ : X.Carrier)
    (D : MvPolynomial.homogeneousSubmodule (Fin (e.N+1)) ℂ 1)
    (H : Fin (Module.finrank ℂ (S.first x₀)+1) →
      MvPolynomial.homogeneousSubmodule (Fin (e.N+1)) ℂ 1) :
    ∃p : MvPolynomial (Fin (Module.finrank ℂ (S.first x₀)+1)) ℂ,p≠0 ∧
      ∀z∈(K : Set X.Carrier),MvPolynomial.eval (e.map z).rep D.val≠0 →
        MvPolynomial.eval (fun i => MvPolynomial.eval (e.map z).rep (H i).val /
          MvPolynomial.eval (e.map z).rep D.val) p=0 := by
  classical
  obtain ⟨t,ht⟩ := L.exists_uniform_boxRelationLocus e hRC hdim x₀ D H
  have hmem : K∈compactRelationLocus e (BoxMonomials.indexedForms D H t) := by
    apply (closure_minimal ?_ (compactRelationLocus_isClosed e _)) hK
    rintro _ ⟨y,rfl⟩
    obtain ⟨c,hc,hzero⟩ := show y∈L.boxRelationLocus e D H t from ht ▸ mem_univ y
    exact ⟨c,hc,fun z hz => hzero (subset_closure hz)⟩
  obtain ⟨c,hc,hzero⟩ := hmem
  let r := Module.finrank ℂ (S.first x₀)
  let p : MvPolynomial (Fin (r+1)) ℂ := ∑j,c j • BoxMonomials.indexedAffine j
  refine ⟨p,?_,?_⟩
  · intro he
    apply hc
    funext j
    exact Fintype.linearIndependent_iff.mp (BoxMonomials.indexedAffine_independent (r+1) t) c he j
  · intro z hz hD
    have hh : MvPolynomial.eval (e.map z).rep
        (relationPolynomial e (BoxMonomials.indexedForms D H t) c).val=0 := hzero hz
    rw [relation_eval] at hh
    simp only [BoxMonomials.indexedForms_eval D H _ _ hD,mul_assoc,←Finset.mul_sum] at hh
    apply (mul_eq_zero_iff_left (pow_ne_zero _ hD)).mp
    convert hh using 1
    simp only [p,map_sum,MvPolynomial.smul_eval]
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    ring

lemma leafLimits_affine_relation {K : Compacts X.Carrier} (hK : K∈L.leafLimits e hRC hdim)
    (x₀ : X.Carrier)
    (p : (Fin (e.N+1) → ℂ) →ₗ[ℂ] (Fin (Module.finrank ℂ (S.first x₀)) → ℂ))
    (i j : Fin (e.N+1)) :
    ∃q : MvPolynomial (Option (Fin (Module.finrank ℂ (S.first x₀)))) ℂ,
      q≠0 ∧ ∀x∈(K : Set X.Carrier),(e.map x).rep i≠0 →
        MvPolynomial.eval (fun t => Option.elim t (projectiveCoordinates i (e.map x) j)
          (p (projectiveCoordinates i (e.map x)))) q=0 := by
  classical
  let r := Module.finrank ℂ (S.first x₀)
  let D : MvPolynomial.homogeneousSubmodule (Fin (e.N+1)) ℂ 1 :=
    ⟨MvPolynomial.X i,MvPolynomial.isHomogeneous_X ℂ i⟩
  let H : Option (Fin r) → MvPolynomial.homogeneousSubmodule (Fin (e.N+1)) ℂ 1 :=
    fun t => Option.elim t ⟨MvPolynomial.X j,MvPolynomial.isHomogeneous_X ℂ j⟩
      (fun a => ProjectiveLinearCoordinates.form ((LinearMap.proj a).comp p))
  obtain ⟨q,hq,hrel⟩ := L.leafLimits_relation e hRC hdim hK x₀ D (H ∘ finSuccEquiv r)
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
