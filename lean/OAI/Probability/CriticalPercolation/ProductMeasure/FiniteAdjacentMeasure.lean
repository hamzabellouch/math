import Mathlib
import OAI.Probability.CriticalPercolation.GraphGeometry.VertexBall
import OAI.Probability.CriticalPercolation.ProductMeasure.BitMeasure
import OAI.Probability.CriticalPercolation.GraphGeometry.FiniteAdjacent
import OAI.Probability.CriticalPercolation.GraphGeometry.FiniteInduced
import OAI.Probability.CriticalPercolation.Modular.FiniteClusterTransport

namespace OAI

section
section
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped Classical

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma finite_averaged_adjacent_measure [Fintype V] [Fintype E]
    (p : unitInterval) (hp : (p : ℝ) ∈ Set.Ioo 0 1)
    (D : ℕ) (hDpos : 1≤D) (hD : ∀ v, (G.incidentEdges {v}).ncard ≤ D)
    (x y : E → V) (he : ∀ e, G.ends e = s(x e,y e)) (K : ℕ) :
    (∑ e, (G.law p).real (G.twoClusterEvent (x e) (y e) (4^K))) ≤
      (Fintype.card V : ℝ)*((D:ℝ)/(p:ℝ)*(6/(2:ℝ)^K)) := by
  have h := G.finite_averaged_adjacent p hp (fun _ : E => BernoulliProduct.bitWeight p)
    (fun _ => BernoulliProduct.bitWeight_sum p) (fun _ => BernoulliProduct.bitWeight_nonneg p)
    (fun _ => by simp [BernoulliProduct.bitWeight])
    (fun _ => by simp [BernoulliProduct.bitWeight]) D hDpos
    (fun v => by simpa only [← Set.ncard_eq_toFinset_card'] using hD v) x y he K
  simpa only [G.finite_endpoint_prob] using h

lemma induce_incident_image_subset (S : Set V) (v : S) :
    Subtype.val '' ((G.induce S).incidentEdges {v}) ⊆ G.incidentEdges {v.val} := by
  rintro e ⟨a,ha,rfl⟩
  simp only [incidentEdges,Set.mem_ofPred_eq,Set.mem_singleton_iff,exists_eq_left] at ha ⊢
  rw [← G.induce_ends_map S a]
  exact Sym2.mem_map.mpr ⟨v,ha,rfl⟩

lemma induce_incident_bound (hlocal : G.LocallyFinite) (D : ℕ)
    (hD : ∀ v, (G.incidentEdges {v}).ncard ≤ D) (S : Set V) (v : S) :
    ((G.induce S).incidentEdges {v}).ncard ≤ D := by
  calc
    _ = (Subtype.val '' ((G.induce S).incidentEdges {v})).ncard :=
      (Set.ncard_image_of_injective _ Subtype.val_injective).symm
    _ ≤ (G.incidentEdges {v.val}).ncard := Set.ncard_le_ncard
      (G.induce_incident_image_subset S v) (G.finite_incident hlocal (Set.finite_singleton _))
    _ ≤ D := hD v.val

lemma induced_averaged_adjacent (hlocal : G.LocallyFinite)
    (p : unitInterval) (hp : (p : ℝ) ∈ Set.Ioo 0 1)
    (D : ℕ) (hDpos : 1≤D) (hD : ∀ v, (G.incidentEdges {v}).ncard ≤ D)
    (S : Set V) (hS : S.Finite) (K : ℕ) :
    ∑ e ∈ (G.finite_inducedEdges hlocal hS).toFinset,
      (G.law p).real {ω | G.inducedEdges S ∩ ω ∈
        G.twoClusterEvent (G.ends e).out.1 (G.ends e).out.2 (4^K)} ≤
      (S.ncard : ℝ)*((D:ℝ)/(p:ℝ)*(6/(2:ℝ)^K)) := by
  let := hS.fintype
  let := (G.finite_inducedEdges hlocal hS).fintype
  let x (e : G.inducedEdges S) : S := ⟨(G.ends e.val).out.1,e.property _ (Sym2.out_fst_mem _)⟩
  let y (e : G.inducedEdges S) : S := ⟨(G.ends e.val).out.2,e.property _ (Sym2.out_snd_mem _)⟩
  have he (e : G.inducedEdges S) : (G.induce S).ends e = s(x e,y e) := by
    apply (G.induce_ends_eq S e (x e) (y e)).mpr
    exact (G.ends e.val).out_eq.symm
  have hh := (G.induce S).finite_averaged_adjacent_measure p hp D hDpos
    (G.induce_incident_bound hlocal D hD S) x y he K
  simp_rw [G.induce_twoCluster_real S (G.finite_inducedEdges hlocal hS)] at hh
  rw [Finset.sum_subtype (G.finite_inducedEdges hlocal hS).toFinset
    (fun e => (G.finite_inducedEdges hlocal hS).mem_toFinset)]
  simpa only [x,y,Set.ncard_eq_toFinset_card',Set.toFinset_card] using hh

end CriticalPercolation.BondGraph
end
end
end

end OAI
