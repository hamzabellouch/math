import OAI.Analysis.Pureness.GroupAlgebra.GroupTraceGNS
import OAI.Analysis.Pureness.GroupAlgebra.ReducedGroupTrace
import OAI.Analysis.Pureness.Comparison.FaithfulGNS

namespace OAI
noncomputable section
namespace CuntzPureness
local instance groupTraceReconstructionDecidableEq {X : Type*} : DecidableEq X :=
  Classical.decEq X
open scoped lp InnerProductSpace CStarAlgebra
variable {G B : Type*} [Group G] [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
variable (τ : TracialState B) (u : G →* unitary B)
variable (hδ : ∀ g : G, τ.functional (u g) = if g=1 then 1 else 0)
variable (hgen : (Submodule.span ℂ (Set.range (fun g : G => (u g : B)))).topologicalClosure = ⊤)

def groupTraceRegularHom : B →⋆ₐ[ℂ] GroupOperator G :=
  ((groupTraceHilbertEquiv τ u hδ hgen).symm.conjStarAlgEquiv).toStarAlgHom.comp
    τ.functional.gnsStarAlgHom

lemma groupTraceRegularHom_generator (g : G) : groupTraceRegularHom τ u hδ hgen (u g) = groupLeft g := by
  apply ContinuousLinearMap.ext
  intro x
  apply (groupTraceHilbertEquiv τ u hδ hgen).injective
  have h := congrArg (fun T : GroupL2 G →L[ℂ] τ.functional.GNS => T x)
    (groupTraceHilbertEquiv_intertwines τ u hδ hgen g)
  simpa [groupTraceRegularHom, LinearIsometryEquiv.conjStarAlgEquiv_apply_apply] using h.symm

lemma groupTraceRegularHom_mem (a : B) : groupTraceRegularHom τ u hδ hgen a ∈ reducedGroupAlgebra G := by
  have ha : a ∈ (Submodule.span ℂ (Set.range (fun g : G => (u g : B)))).topologicalClosure := by
    rw [hgen]; trivial
  apply closure_minimal (t := (groupTraceRegularHom τ u hδ hgen) ⁻¹' (reducedGroupAlgebra G : Set _)) ?_
    ((reducedGroupAlgebra_closed G).preimage (map_continuous (groupTraceRegularHom τ u hδ hgen))) ha
  intro x hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨g,rfl⟩ := hx
    change groupTraceRegularHom τ u hδ hgen (u g) ∈ reducedGroupAlgebra G
    rw [groupTraceRegularHom_generator]
    exact groupLeft_mem_reduced G g
  | zero => simp
  | add x y _ _ hx hy => simpa using (reducedGroupAlgebra G).add_mem hx hy
  | smul c x _ hx => simpa using (reducedGroupAlgebra G).smul_mem hx c

def groupTraceReducedHom : B →⋆ₐ[ℂ] reducedGroupAlgebra G :=
  (groupTraceRegularHom τ u hδ hgen).codRestrict _ (groupTraceRegularHom_mem τ u hδ hgen)

variable (hfaith : ∀ a : B, τ.functional (star a*a)=0 → a=0)

include hfaith in
lemma groupTraceRegularHom_injective : Function.Injective (groupTraceRegularHom τ u hδ hgen) :=
  (groupTraceHilbertEquiv τ u hδ hgen).symm.conjStarAlgEquiv.injective.comp
    (CuntzComparison.faithful_gns_injective τ.functional hfaith)

include hfaith in
lemma groupTraceReducedHom_bijective : Function.Bijective (groupTraceReducedHom τ u hδ hgen) := by
  have hi := groupTraceRegularHom_injective τ u hδ hgen hfaith
  constructor
  · intro a b h
    exact hi (congrArg Subtype.val h)
  · intro a
    have hc : IsClosed (Set.range (groupTraceRegularHom τ u hδ hgen)) :=
      (NonUnitalStarAlgHom.isometry (groupTraceRegularHom τ u hδ hgen).toNonUnitalStarAlgHom hi).isClosedEmbedding.isClosed_range
    have ha : (a : GroupOperator G) ∈ Set.range (groupTraceRegularHom τ u hδ hgen) := by
      apply closure_minimal (t := Set.range (groupTraceRegularHom τ u hδ hgen)) ?_ hc a.property
      intro x hx
      change x ∈ Submodule.span ℂ (Set.range (groupLeft (G := G))) at hx
      change x ∈ (groupTraceRegularHom τ u hδ hgen).range
      induction hx using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨g,rfl⟩ := hx
        exact ⟨u g,groupTraceRegularHom_generator τ u hδ hgen g⟩
      | zero => exact (groupTraceRegularHom τ u hδ hgen).range.zero_mem
      | add x y _ _ hx hy => exact (groupTraceRegularHom τ u hδ hgen).range.add_mem hx hy
      | smul c x _ hx => exact (groupTraceRegularHom τ u hδ hgen).range.smul_mem hx c
    obtain ⟨b,hb⟩ := ha
    exact ⟨b,Subtype.ext hb⟩

def groupTraceReducedEquiv : B ≃⋆ₐ[ℂ] reducedGroupAlgebra G :=
  StarAlgEquiv.ofBijective (groupTraceReducedHom τ u hδ hgen)
    (groupTraceReducedHom_bijective τ u hδ hgen hfaith)

lemma groupTraceReducedEquiv_generator (g : G) :
    groupTraceReducedEquiv τ u hδ hgen hfaith (u g) = reducedGroupUnitary G g :=
  Subtype.ext (groupTraceRegularHom_generator τ u hδ hgen g)

lemma groupTraceReducedEquiv_trace (a : B) :
    (reducedGroupTracialState G).functional (groupTraceReducedEquiv τ u hδ hgen hfaith a) = τ.functional a := by
  let e := groupTraceHilbertEquiv τ u hδ hgen
  have hv : e groupVacuum = stateGNSVector τ.functional := by
    change groupTraceHilbertEquiv τ u hδ hgen (lp.single 2 1 1) = _
    rw [groupTraceHilbertEquiv_single]
    simp [groupTraceVector]
  change ⟪groupVacuum, e.symm (τ.functional.gnsStarAlgHom a (e groupVacuum))⟫_ℂ = _
  rw [← e.inner_map_map, e.apply_symm_apply, hv, stateGNS_vector_value]

lemma groupTraceReducedEquiv_norm (a : B) :
    ‖groupTraceReducedEquiv τ u hδ hgen hfaith a‖ = ‖a‖ :=
  NonUnitalStarAlgHom.norm_map (groupTraceReducedEquiv τ u hδ hgen hfaith).toStarAlgHom.toNonUnitalStarAlgHom
    (groupTraceReducedEquiv τ u hδ hgen hfaith).injective a
end CuntzPureness

end

end OAI
