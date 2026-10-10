import OAI.Probability.FreeIsing.Trees.ClusterColorMarginal
import OAI.Probability.FreeIsing.Trees.ClusterComponentCount
import OAI.Probability.FreeIsing.Trees.FiniteClusterLaw

namespace OAI

noncomputable section

open MeasureTheory
open scoped Classical

namespace Problem367.FiniteCluster

variable {d : ℕ}

theorem clusterColor_cylinder_eq_colorWeight
    {R : TreeVertex d → TreeVertex d → Prop}
    (hR : ∀ {u v}, R u v → treeAdj u v)
    (hsymm : ∀ {u v}, R u v → R v u)
    (marker : TreeVertex d → ℝ)
    (hfinite : ∀ v, {a | Relation.ReflTransGen R v a}.Finite)
    (hinj : Function.Injective marker)
    {D : Finset (TreeVertex d)} (hD : ConnectedFinset D)
    (eta : TreeVertex d → IsingSpin) :
    (labelMeasure d)
      {U | ∀ v ∈ D,
        color (Relation.ReflTransGen R) marker (fairSpin ∘ U) v = eta v} =
      ENNReal.ofReal (colorWeight (inducedEdges D)
        ((inducedEdges D).filter (fun e => R e.1 e.2)) eta) := by
  classical
  have hEq : Equivalence (Relation.ReflTransGen R) := by
    refine ⟨fun _ => .refl, ?_, fun h₁ h₂ => h₁.trans h₂⟩
    intro u v huv
    induction huv with
    | refl => exact .refl
    | tail h hlast ih => exact (Relation.ReflTransGen.single (hsymm hlast)).trans ih
  have hcompat : ClusterCompatible (Relation.ReflTransGen R) D eta ↔
      Compatible ((inducedEdges D).filter (fun e => R e.1 e.2)) eta := by
    change (∀ u ∈ D, ∀ v ∈ D, Relation.ReflTransGen R u v → eta u = eta v) ↔ _
    rw [hD.cluster_constant_iff_inducedEdges hR hsymm eta]
    simp only [Compatible, Finset.mem_filter, and_imp]
  let : DecidableEq (TreeVertex d) := fun a b => Classical.propDecidable (a = b)
  have hcard := ClusterComponentCount.card_image_of_relation hR hsymm
    (selector (Relation.ReflTransGen R) marker)
    (fun u v => selector_eq_iff_related hEq (hfinite u) (hfinite v) hinj) hD
  change (Measure.infinitePi (fun _ : TreeVertex d => uniform01)) _ = _
  rw [clusterColor_cylinder D eta hEq (fun v _ => hfinite v) hinj,
    hcompat, colorWeight_eq_vertices_sub_edges hD (Finset.filter_subset _ _) eta]
  rw [hcard]
  split_ifs <;> simp [ENNReal.ofReal_pow, ENNReal.inv_pow]

end Problem367.FiniteCluster

end

end OAI
