import Mathlib
import OAI.Geometry.HyperbolicGroups.RelativePartition
import OAI.Geometry.HyperbolicGroups.PictureVertexCut
import OAI.Geometry.HyperbolicGroups.SeparatorCutoff

namespace OAI

universe u

section
section


noncomputable section
namespace HyperbolicObstruction.PlanarRecursion
open Finset
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace CutPartition
variable {G : SimpleGraph V} {U : Finset V} {K : ℕ} (P : CutPartition G U K)

abbrev Label := ↑(Finset.univ.image P.label)
def finiteLabel (v : V) : P.Label :=
  ⟨P.label v,Finset.mem_image.mpr ⟨v,Finset.mem_univ _,rfl⟩⟩

omit [DecidableEq V] in
lemma finiteLabel_small (i : P.Label) :
    (U.filter (fun x => P.finiteLabel x = i)).card ≤ K := by
  have he : U.filter (fun x => P.finiteLabel x = i) = U.filter (fun x => P.label x = i.val) := by
    ext x
    simp only [Finset.mem_filter]
    exact and_congr_right (fun _ => Subtype.ext_iff)
  rw [he]
  exact P.small _

end CutPartition
end HyperbolicObstruction.PlanarRecursion

namespace HyperbolicObstruction.PictureSwitch
open Equiv Equiv.Perm PlanarRecursion
attribute [local instance] Classical.propDecidable

/-- Full uniform partition-to-multigraph-cut bridge. The required planar
separator producer remains EXPLICIT in the hypothesis; this theorem proves
all its downstream recursion, finite labeling and parallel-edge accounting.
The cutoff is chosen before the graph, its dart type, and its active carrier. -/
theorem uniform_relative_cut_partition (c : ℝ) (d : ℕ) (eta : ℝ)
    (hc : 0 ≤ c) (heta : 0 < eta) :
    ∃ K : ℕ, 0 < K ∧ ∀ (D : Type u) [Fintype D] [DecidableEq D] (M : PictureMap D),
      HasBalancedSeparators M.underlyingGraph c → ∀ U : Finset M.GraphVertex,
      (∀ v ∈ U, Nat.card {x : D // M.vertexClass x = v} ≤ d) →
      ∃ (I : Type) (_ : Fintype I) (part : M.GraphVertex → I),
        (∀ i, (U.filter (fun x => part x = i)).card ≤ K) ∧
        (Fintype.card (RelativeCutContact M (fun x => M.vertexClass x ∈ U)
          (part ∘ M.vertexClass)) : ℝ) ≤ eta * U.card := by
  obtain ⟨K,hK,huniform⟩ := uniform_bounded_partition c d eta hc (by positivity) heta
  refine ⟨K,hK,?_⟩
  intro D _ _ M hsep U hdegree
  classical
  obtain ⟨P,hP⟩ := huniform M.GraphVertex M.underlyingGraph hsep U
  refine ⟨P.Label,inferInstance,P.finiteLabel,?_,?_⟩
  · intro i
    convert P.finiteLabel_small i using 1
    congr 1
    ext x
    simp only [Finset.mem_filter]
  ·
    have hcut := M.relative_cuts_le_separator (fun x => M.vertexClass x ∈ U)
      P.finiteLabel P.removed d (fun v hv => hdegree v (P.removed_subset hv)) ?_
    · have hcR : (Fintype.card (RelativeCutContact M (fun x => M.vertexClass x ∈ U)
          (P.finiteLabel ∘ M.vertexClass)) : ℝ) ≤ d * (P.removed.card : ℝ) := by
        exact_mod_cast hcut
      exact hcR.trans hP
    · intro x hx he hne
      by_contra h
      push Not at h
      have hlabels := P.edge_const (M.vertexClass x) hx (M.vertexClass (M.edge x)) he
        (show M.underlyingGraph.Adj (M.vertexClass x) (M.vertexClass (M.edge x)) from
          ⟨fun hh => hne (congrArg P.finiteLabel hh),x,rfl,rfl⟩) h.1 h.2
      exact hne (Subtype.ext hlabels)

end HyperbolicObstruction.PictureSwitch
end
end

section

end
end

end OAI
