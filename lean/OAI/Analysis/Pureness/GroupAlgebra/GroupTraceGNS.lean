import OAI.Analysis.Pureness.GroupAlgebra.GroupRegularRepresentation
import OAI.Analysis.Pureness.Operators.SimpleStateGNS
import OAI.Analysis.Pureness.Traces.TracialStates

namespace OAI
noncomputable section
namespace CuntzPureness
local instance groupTraceGNSDecidableEq {α : Type*} : DecidableEq α := Classical.decEq α
open scoped lp InnerProductSpace CStarAlgebra
variable {G B : Type*} [Group G] [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
variable (τ : TracialState B) (u : G →* unitary B)

def groupTraceVector (g : G) : τ.functional.GNS :=
  τ.functional.gnsStarAlgHom (u g) (stateGNSVector τ.functional)

lemma groupTraceVector_inner (g h : G) :
    ⟪groupTraceVector τ u g, groupTraceVector τ u h⟫_ℂ = τ.functional (u (g⁻¹*h)) := by
  simp only [groupTraceVector, stateGNS_apply_vector, UniformSpace.Completion.inner_coe,
    PositiveLinearMap.preGNS_inner_def, PositiveLinearMap.ofPreGNS_toPreGNS]
  rw [u.map_mul, u.map_inv]
  rfl

variable (hδ : ∀ g : G, τ.functional (u g) = if g=1 then 1 else 0)

include hδ in
lemma groupTraceVector_orthonormal : Orthonormal ℂ (groupTraceVector τ u) := by
  rw [orthonormal_iff_ite]
  intro g h
  rw [groupTraceVector_inner, hδ]
  simp [inv_mul_eq_one]

lemma groupTraceVector_total
    (hgen : (Submodule.span ℂ (Set.range (fun g : G => (u g : B)))).topologicalClosure = ⊤) :
    ⊤ ≤ (Submodule.span ℂ (Set.range (groupTraceVector τ u))).topologicalClosure := by
  let S := (Submodule.span ℂ (Set.range (groupTraceVector τ u))).topologicalClosure
  have hf : Continuous (fun a : B => τ.functional.gnsStarAlgHom a (stateGNSVector τ.functional)) :=
    (map_continuous τ.functional.gnsStarAlgHom).clm_apply continuous_const
  have hall (a : B) : τ.functional.gnsStarAlgHom a (stateGNSVector τ.functional) ∈ S := by
    have ha : a ∈ (Submodule.span ℂ (Set.range (fun g : G => (u g : B)))).topologicalClosure := by
      rw [hgen]; trivial
    apply closure_minimal (t := (fun a : B => τ.functional.gnsStarAlgHom a
      (stateGNSVector τ.functional)) ⁻¹' (S : Set τ.functional.GNS)) ?_
      ((Submodule.isClosed_topologicalClosure _).preimage hf) ha
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g,rfl⟩ := hx
      exact Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨g,rfl⟩)
    | zero => simp
    | add x y _ _ hx hy => simpa using S.add_mem hx hy
    | smul c x _ hx => simpa using S.smul_mem c hx
  intro x _
  have hx := stateGNS_cyclic τ.functional x
  exact closure_minimal (Set.range_subset_iff.mpr hall) (Submodule.isClosed_topologicalClosure _) hx

def groupTraceHilbertEquiv
    (hgen : (Submodule.span ℂ (Set.range (fun g : G => (u g : B)))).topologicalClosure = ⊤) :
    GroupL2 G ≃ₗᵢ[ℂ] τ.functional.GNS :=
  ((groupTraceVector_orthonormal τ u hδ).isHilbertSum
    (groupTraceVector_total τ u hgen)).linearIsometryEquiv.symm

lemma groupTraceHilbertEquiv_single
    (hgen : (Submodule.span ℂ (Set.range (fun g : G => (u g : B)))).topologicalClosure = ⊤)
    (g : G) : groupTraceHilbertEquiv τ u hδ hgen (lp.single 2 g 1) = groupTraceVector τ u g :=
  Orthonormal.linearIsometryEquiv_symm_apply_single_one
    (groupTraceVector_orthonormal τ u hδ) (groupTraceVector_total τ u hgen) g

lemma groupTraceVector_mul (g h : G) :
    τ.functional.gnsStarAlgHom (u g) (groupTraceVector τ u h) = groupTraceVector τ u (g*h) := by
  simp [groupTraceVector, map_mul, mul_apply_eq_comp]

theorem groupTraceHilbertEquiv_intertwines
    (hgen : (Submodule.span ℂ (Set.range (fun g : G => (u g : B)))).topologicalClosure = ⊤)
    (g : G) :
    (groupTraceHilbertEquiv τ u hδ hgen).toContinuousLinearEquiv.toContinuousLinearMap.comp
      (groupLeft g) =
    (τ.functional.gnsStarAlgHom (u g)).comp
      (groupTraceHilbertEquiv τ u hδ hgen).toContinuousLinearEquiv.toContinuousLinearMap := by
  apply lp.ext_continuousLinearMap (by norm_num : (2 : ENNReal) ≠ ⊤)
  intro h
  apply ContinuousLinearMap.ext
  intro c
  have hs : lp.single (E := fun _ : G => ℂ) 2 h c = c • lp.single 2 h 1 := by
    simpa using lp.single_smul (E := fun _ : G => ℂ) 2 h c (1 : ℂ)
  have hl : groupLeft g (lp.single 2 h 1) = lp.single 2 (g*h) 1 := by
    rw [← groupLeft_vacuum, ← mul_apply_eq_comp, ← groupLeft_mul, groupLeft_vacuum]
  change groupTraceHilbertEquiv τ u hδ hgen (groupLeft g (lp.single 2 h c)) =
    τ.functional.gnsStarAlgHom (u g) (groupTraceHilbertEquiv τ u hδ hgen (lp.single 2 h c))
  rw [hs, map_smul, map_smul, map_smul, map_smul, hl,
    groupTraceHilbertEquiv_single, groupTraceHilbertEquiv_single, groupTraceVector_mul]
end CuntzPureness

end

end OAI
