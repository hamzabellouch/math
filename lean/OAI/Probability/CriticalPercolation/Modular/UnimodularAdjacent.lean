import Mathlib
import OAI.Probability.CriticalPercolation.Criticality.WitnessEvents
import OAI.Probability.CriticalPercolation.Modular.UnimodularAverages

namespace OAI

section
noncomputable section
open Set MeasureTheory Filter
open scoped Classical BigOperators Topology

namespace CriticalPercolation.BondGraph
variable {V E : Type*} [Countable V] [Countable E] (G : BondGraph V E)

omit [Countable V] [Countable E] in
lemma Aut.twoClusterEvent_preimage (φ : G.Aut) (u v : V) (s : ℕ) :
    (fun ω : Set E => φ.edge '' ω) ⁻¹' G.twoClusterEvent (φ.vertex u) (φ.vertex v) s =
      G.twoClusterEvent u v s := by
  ext ω
  simp only [twoClusterEvent,Set.mem_preimage,Set.mem_inter_iff,Set.mem_ofPred_eq]
  rw [Aut.reachable_map,Aut.clusterTail_map,Aut.clusterTail_map]

lemma Aut.twoClusterEvent_real (φ : G.Aut) (p : unitInterval) (u v : V) (s : ℕ) :
    (G.law p).real (G.twoClusterEvent (φ.vertex u) (φ.vertex v) s) =
      (G.law p).real (G.twoClusterEvent u v s) := by
  simp only [measureReal_def]
  congr 1
  conv_lhs => rw [← G.law_map_aut p φ]
  rw [Measure.map_apply (BernoulliProduct.measurable_image_equiv φ.edge)
    (G.measurableSet_twoClusterEvent _ _ _),Aut.twoClusterEvent_preimage]

lemma Aut.edgeTwoCluster_real (φ : G.Aut) (p : unitInterval) (e : E) (s : ℕ) :
    (G.law p).real (G.twoClusterEvent (G.ends (φ.edge e)).out.1 (G.ends (φ.edge e)).out.2 s) =
      (G.law p).real (G.twoClusterEvent (G.ends e).out.1 (G.ends e).out.2 s) := by
  have hend : s(φ.vertex (G.ends e).out.1,φ.vertex (G.ends e).out.2) =
      s((G.ends (φ.edge e)).out.1,(G.ends (φ.edge e)).out.2) := by
    calc
      _ = Sym2.map φ.vertex (G.ends e) := by
        conv_rhs => rw [← (G.ends e).out_eq]
        rfl
      _ = G.ends (φ.edge e) := (φ.preserves e).symm
      _ = _ := (G.ends (φ.edge e)).out_eq.symm
  rw [← G.twoClusterEvent_sym2 hend s]
  exact Aut.twoClusterEvent_real G φ p _ _ _

theorem UnimodularRoot.subcritical_adjacent_bound (R : G.UnimodularRoot)
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (e : E) :
    ∃ A : ℝ, 0 < A ∧ ∀ (p : unitInterval), (p:ℝ) ∈ Ioo 0 1 → p < G.criticalProbability →
      ∀ k : ℕ, (G.law p).real (G.twoClusterEvent (G.ends e).out.1 (G.ends e).out.2 (4^k)) ≤
        A/((p:ℝ)*(2:ℝ)^k) := by
  obtain ⟨D,hDpos,hD⟩ := G.uniform_incident_bound (UnimodularRoot.quasiTransitive G R)
  obtain ⟨u,hu,φ,hφ⟩ := R.cover (G.ends e).out.1
  let f := φ.edge.symm e
  have hf : φ.edge f = e := φ.edge.apply_symm_apply e
  have huf : u ∈ G.ends f := by
    apply (Aut.incident_iff G φ u f).mp
    rw [hf,hφ]
    exact Sym2.out_fst_mem _
  let w := R.weight u * G.bondShare f
  have hw : 0 < w := mul_pos (R.positive u hu) (G.bondShare_pos f)
  have hDreal : (0:ℝ) < D := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hDpos)
  refine ⟨6*(D:ℝ)/w,by positivity,?_⟩
  intro p hp hpc k
  have hb := UnimodularRoot.incident_bound G R hc hl D hDpos hD k p hp hpc hu huf
  have heq := Aut.edgeTwoCluster_real G φ p f (4^k)
  rw [hf] at heq
  rw [heq]
  calc
    _ ≤ ((D:ℝ)/p*(6/(2:ℝ)^k))/w := by
      apply (le_div_iff₀ hw).mpr
      simpa only [w,mul_comm] using hb
    _ = _ := by simp only [div_eq_mul_inv,mul_inv_rev]; ring

end CriticalPercolation.BondGraph
end
end

end OAI
