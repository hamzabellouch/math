import Mathlib
import OAI.Geometry.HyperbolicGroups.PlanarPartitionBridge
import OAI.Geometry.HyperbolicGroups.SeparatorGrouping
import OAI.Geometry.HyperbolicGroups.SeparatorComponents
import OAI.Geometry.HyperbolicGroups.PictureComponentGraph

namespace OAI

universe u

section
section


noncomputable section
namespace HyperbolicObstruction.PictureSwitch.PictureMap
open Equiv Equiv.Perm PlanarRecursion
attribute [local instance] Classical.propDecidable
variable {D : Type*} [DecidableEq D] [Fintype D]
variable (M : PictureMap D)

/-- Uniform planar separator for an arbitrary (possibly empty or
 disconnected) literal genus-zero rotation system and every vertex carrier.
 All genus, component, radius, triangulation and tree obligations are proved. -/
theorem genusZero_component_separator (hG : M.GenusZero) (U : Finset M.GraphVertex) :
    ∃ S : Finset M.GraphVertex, S ⊆ U ∧ S.card ≤ 11*Nat.sqrt U.card ∧
      ∀ W : Finset M.GraphVertex, W ⊆ U → Disjoint W S →
        (M.underlyingGraph.induce (W : Set M.GraphVertex)).Preconnected →
        2*W.card ≤ U.card :=
  component_separators_union M.underlyingGraph 11 (fun C => M.graph_component_separator C hG) U

/-- The actual Lipton--Tarjan-style input required by the manuscript's
recursive partition proof, proved from its finite genus-zero maps. -/
theorem genusZero_balanced_separators (hG : M.GenusZero) :
    HasBalancedSeparators M.underlyingGraph 11 :=
  balanced_separators_of_component_separators M.underlyingGraph 11
    (M.genusZero_component_separator hG)

end HyperbolicObstruction.PictureSwitch.PictureMap
namespace HyperbolicObstruction.PictureSwitch
open Equiv Equiv.Perm PlanarRecursion
attribute [local instance] Classical.propDecidable

/-- The planar-multigraph partition producer. K is chosen
before EVERY finite dart type, genus-zero map and active carrier. The exact
multigraph cut cost is retained, including loops/parallel copies and an
arbitrary-degree protected exterior. -/
theorem uniform_genusZero_cut_partition (d : ℕ) (eta : ℝ) (heta : 0 < eta) :
    ∃ K : ℕ, 0 < K ∧ ∀ (D : Type u) [Fintype D] [DecidableEq D] (M : PictureMap D),
      M.GenusZero → ∀ U : Finset M.GraphVertex,
      (∀ v ∈ U, Nat.card {x : D // M.vertexClass x = v} ≤ d) →
      ∃ (I : Type) (_ : Fintype I) (part : M.GraphVertex → I),
        (∀ i, (U.filter (fun x => part x = i)).card ≤ K) ∧
        (Fintype.card (RelativeCutContact M (fun x => M.vertexClass x ∈ U)
          (part ∘ M.vertexClass)) : ℝ) ≤ eta * U.card := by
  obtain ⟨K,hK,hh⟩ := uniform_relative_cut_partition 11 d eta (by norm_num) heta
  exact ⟨K,hK,fun D _ _ M hM U hd => hh D M (M.genusZero_balanced_separators hM) U hd⟩

end HyperbolicObstruction.PictureSwitch
end
end

section

end
end

end OAI
