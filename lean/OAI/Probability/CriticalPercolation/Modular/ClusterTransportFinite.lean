import Mathlib
import OAI.Probability.CriticalPercolation.Modular.ClusterTransportSums

namespace OAI

section
noncomputable section
open Set MeasureTheory Filter
open scoped Classical BigOperators Topology

namespace CriticalPercolation.FiniteClusters
variable {V E : Type*} (G : BondGraph V E)

lemma transport_row_zero (r s : ℕ) (p : ℝ) (ω : Set E) (u : V) (e : E)
    (he : e ∉ G.incidentEdges (G.vertexBall u r)) : transport G r s p ω u e = 0 := by
  unfold transport weight
  by_cases hs : small G r ω u
  · have hi : e ∉ G.incidentEdges (G.cluster ω u) := by
      rintro ⟨v,hv,hve⟩
      exact he ⟨v,small_cluster_subset G hs hv,hve⟩
    rw [ite_eq_right hi]
  · simp only [hs,ite_false,zero_mul,ite_self]

lemma transport_column_zero (r s : ℕ) (p : ℝ) (ω : Set E) (u : V) (e : E)
    (hu : u ∉ G.vertexBall (G.ends e).out.1 r ∪ G.vertexBall (G.ends e).out.2 r) :
    transport G r s p ω u e = 0 := by
  unfold transport weight
  by_cases hs : small G r ω u
  · have hi : e ∉ G.incidentEdges (G.cluster ω u) := by
      intro he
      have he' : u ∈ G.cluster ω (G.ends e).out.1 ∪ G.cluster ω (G.ends e).out.2 :=
        Set.ext_iff.mp (incidentRoots G ω e) u |>.mp he
      rcases he' with h | h
      · exact hu (Or.inl (G.vertexBall_comm.mp (small_cluster_subset G hs h.symm)))
      · exact hu (Or.inr (G.vertexBall_comm.mp (small_cluster_subset G hs h.symm)))
    rw [ite_eq_right hi]
  · simp only [hs,ite_false,zero_mul,ite_self]

lemma mass_le_one (s : ℕ) (ω : Set E) (v : V) : mass G s ω v ≤ 1 := by
  by_cases hn : size G ω v = 0
  · simp [mass,hn]
  · have hp : (0:ℝ) < size G ω v := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
    apply (div_le_one hp).mpr
    exact (cappedMass_le_one _ _).trans (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn)

lemma weight_le_one (r s : ℕ) (ω : Set E) (v : V) : weight G r s ω v ≤ 1 := by
  unfold weight
  split_ifs
  · exact mass_le_one G s ω v
  · norm_num

lemma transport_bound (r s : ℕ) {p : ℝ} (hp : p ∈ Ioo 0 1)
    (ω : Set E) (u : V) (e : E) : |transport G r s p ω u e| ≤ 1/p := by
  unfold transport
  split_ifs
  · rw [abs_mul,abs_of_nonneg (weight_nonneg G r s ω u)]
    exact (mul_le_mul (weight_le_one G r s ω u) (coefficient_abs_le hp ω e)
      (abs_nonneg _) (by norm_num)).trans_eq (one_mul _)
  · simpa only [abs_zero] using div_nonneg (show (0:ℝ)≤1 by norm_num) hp.1.le

lemma transport_aut (φ : G.Aut) (r s : ℕ) (p : ℝ) (ω : Set E) (u : V) (e : E) :
    transport G r s p (φ.edge '' ω) (φ.vertex u) (φ.edge e) = transport G r s p ω u e := by
  simp only [transport,weight,incidentCluster_aut G φ,small_aut G φ,mass_aut G φ,coefficient_aut G φ]

variable [Countable V] [Countable E]
lemma measurable_weight (r s : ℕ) (u : V) : Measurable (fun ω => weight G r s ω u) :=
  (measurable_mass G s u).ite (measurable_small G r u).setOf measurable_const

lemma measurable_transport (r s : ℕ) (p : ℝ) (u : V) (e : E) :
    Measurable (fun ω => transport G r s p ω u e) :=
  ((measurable_weight G r s u).mul (measurable_coefficient p e)).ite
    (measurable_incidentCluster G u e) measurable_const

lemma integrable_transport (r s : ℕ) (p : unitInterval) (hp : (p:ℝ) ∈ Ioo 0 1) (u : V) (e : E) :
    Integrable (fun ω => transport G r s p ω u e) (G.law p) := by
  apply Integrable.mono' (integrable_const (1/(p:ℝ))) (measurable_transport G r s p u e).aestronglyMeasurable
  exact Eventually.of_forall (fun ω => transport_bound G r s hp ω u e)

def expectedTransport (r s : ℕ) (p : unitInterval) (u : V) (e : E) : ℝ :=
  ∫ ω, transport G r s p ω u e ∂G.law p

lemma expectedTransport_aut (φ : G.Aut) (r s : ℕ) (p : unitInterval) (u : V) (e : E) :
    expectedTransport G r s p (φ.vertex u) (φ.edge e) = expectedTransport G r s p u e := by
  unfold expectedTransport
  conv_lhs => rw [← G.law_map_aut p φ]
  rw [integral_map (BernoulliProduct.measurable_image_equiv φ.edge).aemeasurable
    (measurable_transport G r s p (φ.vertex u) (φ.edge e)).aestronglyMeasurable]
  apply integral_congr_ae
  exact Eventually.of_forall (fun ω => transport_aut G φ r s p ω u e)

omit [Countable V] [Countable E] in
lemma expectedTransport_row_zero (r s : ℕ) (p : unitInterval) (u : V) (e : E)
    (he : e ∉ G.incidentEdges (G.vertexBall u r)) : expectedTransport G r s p u e = 0 := by
  unfold expectedTransport
  simp only [transport_row_zero G r s p _ u e he,integral_zero]

omit [Countable V] [Countable E] in
lemma expectedTransport_column_zero (r s : ℕ) (p : unitInterval) (u : V) (e : E)
    (hu : u ∉ G.vertexBall (G.ends e).out.1 r ∪ G.vertexBall (G.ends e).out.2 r) :
    expectedTransport G r s p u e = 0 := by
  unfold expectedTransport
  simp only [transport_column_zero G r s p _ u e hu,integral_zero]

omit [Countable V] [Countable E] in
lemma expectedTransport_row_finite (hl : G.LocallyFinite) (r s : ℕ) (p : unitInterval) (u : V) :
    (Function.support (expectedTransport G r s p u)).Finite := by
  apply (G.finite_incident hl (G.vertexBall_finite hl u r)).subset
  intro e he
  by_contra hn
  exact he (expectedTransport_row_zero G r s p u e hn)

omit [Countable V] [Countable E] in
lemma expectedTransport_column_finite (hl : G.LocallyFinite) (r s : ℕ) (p : unitInterval) (e : E) :
    (Function.support (fun u => expectedTransport G r s p u e)).Finite := by
  apply ((G.vertexBall_finite hl (G.ends e).out.1 r).union
    (G.vertexBall_finite hl (G.ends e).out.2 r)).subset
  intro u hu
  by_contra hn
  exact hu (expectedTransport_column_zero G r s p u e hn)

lemma expectedTransport_sum_out (hl : G.LocallyFinite) (r s : ℕ) (p : unitInterval)
    (hp : (p:ℝ) ∈ Ioo 0 1) (u : V) :
    (∑' e, expectedTransport G r s p u e) = ∫ ω, ∑' e, transport G r s p ω u e ∂G.law p := by
  have hI := G.finite_incident hl (G.vertexBall_finite hl u r)
  rw [tsum_eq_sum (s := hI.toFinset) (fun e he => expectedTransport_row_zero G r s p u e
    (fun h => he (hI.mem_toFinset.mpr h)))]
  unfold expectedTransport
  rw [← integral_finsetSum _ (fun e _ => integrable_transport G r s p hp u e)]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro ω
  exact (tsum_eq_sum (s := hI.toFinset) (fun e he => transport_row_zero G r s p ω u e
    (fun h => he (hI.mem_toFinset.mpr h)))).symm

lemma expectedTransport_sum_in (hl : G.LocallyFinite) (r s : ℕ) (p : unitInterval)
    (hp : (p:ℝ) ∈ Ioo 0 1) (e : E) :
    (∑' u, expectedTransport G r s p u e) = ∫ ω, ∑' u, transport G r s p ω u e ∂G.law p := by
  have hB := (G.vertexBall_finite hl (G.ends e).out.1 r).union
    (G.vertexBall_finite hl (G.ends e).out.2 r)
  rw [tsum_eq_sum (s := hB.toFinset) (fun u hu => expectedTransport_column_zero G r s p u e
    (fun h => hu (hB.mem_toFinset.mpr h)))]
  unfold expectedTransport
  rw [← integral_finsetSum _ (fun u _ => integrable_transport G r s p hp u e)]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro ω
  exact (tsum_eq_sum (s := hB.toFinset) (fun u hu => transport_column_zero G r s p ω u e
    (fun h => hu (hB.mem_toFinset.mpr h)))).symm

end CriticalPercolation.FiniteClusters
end
end

end OAI
