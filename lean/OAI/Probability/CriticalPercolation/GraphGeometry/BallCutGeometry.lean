import Mathlib
import OAI.Probability.CriticalPercolation.Model
import OAI.Probability.CriticalPercolation.GraphGeometry.CutEdges
import OAI.Probability.CriticalPercolation.GraphGeometry.FiniteInduced
import OAI.Probability.CriticalPercolation.GraphGeometry.GraphBalls
import OAI.Probability.CriticalPercolation.ProductMeasure.LevelContactMeasurability

namespace OAI

section
noncomputable section
open Set Filter
open scoped Classical

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

def ballCut (o : V) (n : ℕ) : Set E := G.cutEdges (G.vertexBall o n)

lemma ballCut_endpoints (o : V) (n : ℕ) {e : E} (he : e ∈ G.ballCut o n) :
    ∃ x y, G.ends e = s(x,y) ∧ x ∈ G.vertexBall o (n+1) \ G.vertexBall o n ∧
      y ∈ G.vertexBall o n := by
  obtain ⟨x,y,he,hx,hy⟩ := he
  have hne : y ≠ x := by rintro rfl; exact hx hy
  have hadj : G.fullGraph.Adj y x :=
    (SimpleGraph.fromEdgeSet_adj _).mpr ⟨⟨e,Set.mem_univ e,he.trans (Sym2.eq_swap)⟩,hne⟩
  exact ⟨x,y,he,⟨G.vertexBall_step hy hadj,hx⟩,hy⟩

lemma ballCut_subset_incident_sphere (o : V) (n : ℕ) :
    G.ballCut o n ⊆ G.incidentEdges (G.vertexBall o (n+1) \ G.vertexBall o n) := by
  intro e he
  obtain ⟨x,y,he,hx,_⟩ := G.ballCut_endpoints o n he
  exact ⟨x,hx,by simp [he]⟩

lemma ballCut_finite (hl : G.LocallyFinite) (o : V) (n : ℕ) :
    (G.ballCut o n).Finite :=
  (G.finite_incident hl ((G.vertexBall_finite hl o (n+1)).sdiff)).subset
    (G.ballCut_subset_incident_sphere o n)

lemma ballCut_endpoints_mem (o : V) (n : ℕ) {e : E} (he : e ∈ G.ballCut o n)
    {x : V} (hx : x ∈ G.ends e) : x ∈ G.vertexBall o (n+1) := by
  obtain ⟨a,b,he,ha,hb⟩ := G.ballCut_endpoints o n he
  rw [he] at hx
  rcases Sym2.mem_iff.mp hx with rfl|rfl
  · exact ha.1
  · exact G.vertexBall_mono o (Nat.le_succ n) hb

lemma ballCut_pairwise_disjoint (o : V) : Pairwise (fun n m =>
    Disjoint (G.ballCut o n) (G.ballCut o m)) := by
  suffices h : ∀ n m : ℕ, n < m → Disjoint (G.ballCut o n) (G.ballCut o m) by
    intro n m hnm
    rcases lt_or_gt_of_ne hnm with hlt|hlt
    · exact h n m hlt
    · exact (h m n hlt).symm
  intro n m hnm
  apply Set.disjoint_left.mpr
  intro e hen hem
  obtain ⟨x,y,he,hx,hy⟩ := hem
  have hmem : x ∈ G.ends e := by simp [he]
  exact hx (G.vertexBall_mono o (Nat.succ_le_iff.mpr hnm)
    (G.ballCut_endpoints_mem o n hen hmem))

lemma ballCut_card_le (hl : G.LocallyFinite) (o : V) (n D : ℕ)
    (hD : ∀ v, (G.incidentEdges {v}).ncard ≤ D) :
    (G.ballCut o n).ncard ≤
      (G.vertexBall o (n+1) \ G.vertexBall o n).ncard * D := by
  exact (Set.ncard_le_ncard (G.ballCut_subset_incident_sphere o n)
    (G.finite_incident hl ((G.vertexBall_finite hl o (n+1)).sdiff))).trans
      (G.incident_ncard_le _ ((G.vertexBall_finite hl o (n+1)).sdiff) D (fun v _ => hD v))

lemma cluster_subset_ball_of_closed_ballCut (o : V) (n : ℕ) (ω : Set E)
    (hc : Disjoint (G.ballCut o n) ω) {v : V} (hv : v ∈ G.vertexBall o n) :
    G.cluster ω v ⊆ G.vertexBall o n := by
  intro x hx
  by_contra hnot
  exact G.not_reachable_of_cut_closed (G.vertexBall o n) ω
    (fun e he => Set.disjoint_left.mp hc he) hnot hv hx.symm

lemma frequently_small_increments_of_linear_scales (f : ℕ → ℕ) (C : ℕ)
    (hf : ∀ R : ℕ, ∃ n≥R, f n ≤ C*n) :
    ∃ᶠ n in atTop, f (n+1)-f n ≤ C := by
  by_contra h
  rw [not_frequently] at h
  obtain ⟨N,hN⟩ := eventually_atTop.mp h
  have hg (k : ℕ) : (C+1)*k ≤ f (N+k) := by
    induction k with
    | zero => omega
    | succ k ih =>
      have hh := hN (N+k) (by omega)
      have he : N+(k+1)=N+k+1 := by omega
      rw [he]
      have hinc : f (N+k)+C+1 ≤ f (N+k+1) := by omega
      nlinarith
  obtain ⟨n,hn,hfn⟩ := hf ((C+1)*N+1)
  have hNn : N ≤ n := by nlinarith
  have hh := hg (n-N)
  rw [Nat.add_sub_cancel' hNn] at hh
  have he := Nat.sub_add_cancel hNn
  nlinarith

lemma frequently_small_spheres_of_linear_scales (hl : G.LocallyFinite)
    (o : V) (C : ℕ) (hf : ∀ R : ℕ, ∃ n≥R, (G.vertexBall o n).ncard ≤ C*n) :
    ∃ᶠ n in atTop, (G.vertexBall o (n+1) \ G.vertexBall o n).ncard ≤ C := by
  have hh := frequently_small_increments_of_linear_scales (fun n => (G.vertexBall o n).ncard) C hf
  apply hh.mono
  intro n hn
  rwa [Set.ncard_sdiff (G.vertexBall_mono o (Nat.le_succ n))
    (G.vertexBall_finite hl o n)]

end CriticalPercolation.BondGraph
end
end

end OAI
