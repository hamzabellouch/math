import Mathlib
import OAI.Probability.CriticalPercolation.GraphGeometry.BallCutGeometry
import OAI.Probability.CriticalPercolation.GraphGeometry.GraphBalls
import OAI.Probability.CriticalPercolation.Criticality.ClosedBoundedCuts

namespace OAI

section
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Classical

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

theorem sparse_linear_percolates_null (hc : G.fullGraph.Connected)
    (hl : G.LocallyFinite) (hq : G.QuasiTransitive) (o : V) (C : ℕ)
    (hlin : ∀ R : ℕ, ∃ n≥R, (G.vertexBall o n).ncard ≤ C*n)
    (p : unitInterval) (hp : (p:ℝ)<1) : G.law p G.percolates=0 := by
  obtain ⟨r,hr,hrsmall⟩ := Filter.extraction_of_frequently_atTop
    (G.frequently_small_spheres_of_linear_scales hl o C hlin)
  obtain ⟨D,_,hD⟩ := G.uniform_incident_bound hq
  have hcuts := BernoulliProduct.frequently_closedBlock_ae_of_card_le p hp
    (fun n => G.ballCut o (r n)) (fun n => G.ballCut_finite hl o (r n))
    (fun n m hnm => G.ballCut_pairwise_disjoint o (hr.injective.ne hnm)) (C*D)
    (fun n => (G.ballCut_card_le hl o (r n) D hD).trans
      (Nat.mul_le_mul_right D (hrsmall n)))
  rw [BernoulliProduct.law_const] at hcuts
  have hno : ∀ᵐ ω ∂G.law p, ω ∉ G.percolates := by
    filter_upwards [hcuts] with ω hω
    rintro ⟨v,hv⟩
    obtain ⟨N,hN⟩ := G.reachable_mem_vertexBall (hc o v)
    obtain ⟨n,hn,hncut⟩ := Filter.frequently_atTop.mp hω N
    have hNrad : N ≤ r n := hn.trans (hr.id_le n)
    exact hv ((G.vertexBall_finite hl o (r n)).subset
      (G.cluster_subset_ball_of_closed_ballCut o (r n) ω hncut
        (G.vertexBall_mono o hNrad hN)))
  rw [ae_iff] at hno
  simpa only [not_not,Set.ofPred_mem_eq] using hno

theorem sparse_linear_critical_one (hc : G.fullGraph.Connected)
    (hl : G.LocallyFinite) (hq : G.QuasiTransitive) (o : V) (C : ℕ)
    (hlin : ∀ R : ℕ, ∃ n≥R, (G.vertexBall o n).ncard ≤ C*n) :
    G.criticalProbability=1 := by
  apply le_antisymm le_top
  apply le_sInf
  intro p hp
  by_contra h
  have hlt : (p:ℝ)<1 := lt_of_not_ge h
  exact (ne_of_gt hp) (G.sparse_linear_percolates_null hc hl hq o C hlin p hlt)

lemma fixed_root_linear_scales (hc : G.fullGraph.Connected)
    (hl : G.LocallyFinite) (hq : G.QuasiTransitive) (o : V) (C : ℕ)
    (hlin : ∀ R : ℕ, ∃ n≥R, ∃ v : V, (G.vertexBall v n).ncard ≤ C*n) :
    ∀ R : ℕ, ∃ n≥R, (G.vertexBall o n).ncard ≤ (2*C)*n := by
  obtain ⟨K,hK⟩ := G.orbit_density_radius hc hq o
  intro R
  obtain ⟨n,hn,v,hv⟩ := hlin (R+2*K)
  obtain ⟨φ,hφ⟩ := hK v
  have hKn : K≤n := by omega
  have hsub : G.vertexBall (φ.vertex o) (n-K) ⊆ G.vertexBall v n := by
    simpa only [Nat.add_sub_of_le hKn] using G.vertexBall_add hφ (n-K)
  have hcard := Set.ncard_le_ncard hsub (G.vertexBall_finite hl v n)
  rw [Aut.vertexBall_ncard G φ] at hcard
  refine ⟨n-K,by omega,hcard.trans (hv.trans ?_)⟩
  have hbound : n≤2*(n-K) := by omega
  calc
    C*n ≤ C*(2*(n-K)) := Nat.mul_le_mul_left C hbound
    _ = (2*C)*(n-K) := by ring

theorem moving_sparse_linear_critical_one (hc : G.fullGraph.Connected)
    (hl : G.LocallyFinite) (hq : G.QuasiTransitive) (C : ℕ)
    (hlin : ∀ R : ℕ, ∃ n≥R, ∃ v : V, (G.vertexBall v n).ncard ≤ C*n) :
    G.criticalProbability=1 := by
  obtain ⟨o⟩ := hc.nonempty
  exact G.sparse_linear_critical_one hc hl hq o (2*C)
    (G.fixed_root_linear_scales hc hl hq o C hlin)

end CriticalPercolation.BondGraph
end
end

end OAI
