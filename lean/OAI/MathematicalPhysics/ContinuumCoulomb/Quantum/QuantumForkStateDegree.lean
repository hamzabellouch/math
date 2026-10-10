import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumForkState

namespace OAI

/-! Degree and size of the entire graph represented by active stars and background edges. -/

noncomputable section
namespace ContinuumCoulomb
open scoped BigOperators Classical
namespace QMAForkState
variable {n c : ℕ} {d : Fin c → ℕ} {ν : Type*} [Fintype ν]
variable (G : QMAForkState n c d ν)

def fullLeft : ν ⊕ (Σ i, Fin (d i)) → Fin n :=
  Sum.elim G.left (fun p => G.ports.center p.1)
def fullRight : ν ⊕ (Σ i, Fin (d i)) → Fin n :=
  Sum.elim G.right G.ports.port

theorem full_distinct (e : ν ⊕ (Σ i, Fin (d i))) : G.fullLeft e ≠ G.fullRight e := by
  rcases e with e | p
  · exact G.distinct e
  · exact G.ports.center_ne_port p.1 p

theorem full_center_degree (i : Fin c) :
    qmaGraphDegree G.fullLeft G.fullRight (G.ports.center i) = d i := by
  rw [fullLeft,fullRight,qmaGraphDegree_sum,G.center_degree,zero_add]
  have hp (p : Σ i, Fin (d i)) : G.ports.port p ≠ G.ports.center i :=
    (G.ports.center_ne_port i p).symm
  simp only [qmaGraphDegree,hp,or_false,G.ports.center_injective.eq_iff,Fintype.sum_sigma]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    simp [hj]
  · simp

theorem full_noncenter_degree (v : Fin n) (hv : ∀ i, G.ports.center i ≠ v) :
    qmaGraphDegree G.fullLeft G.fullRight v ≤ 3 := by
  rw [fullLeft,fullRight,qmaGraphDegree_sum]
  have hc : qmaGraphDegree (fun p : Σ i, Fin (d i) => G.ports.center p.1) G.ports.port v =
      ∑ p, if G.ports.port p = v then 1 else 0 := by
    simp only [qmaGraphDegree,hv,false_or]
  rw [hc]
  by_cases hp : ∃ p, G.ports.port p = v
  · obtain ⟨p,rfl⟩ := hp
    have hb := G.port_degree p
    have hs := qmaCount_eq_le_one G.ports.port G.ports.port_injective (G.ports.port p)
    omega
  · have hn (p : Σ i, Fin (d i)) : G.ports.port p ≠ v := fun h => hp ⟨p,h⟩
    simpa [hn] using G.degree_le v

theorem full_degree_le_three (hd : ∀ i, d i ≤ 3) (v : Fin n) :
    qmaGraphDegree G.fullLeft G.fullRight v ≤ 3 := by
  by_cases h : ∃ i, G.ports.center i = v
  · obtain ⟨i,rfl⟩ := h
    rw [G.full_center_degree]
    exact hd i
  · exact G.full_noncenter_degree v (by simpa using h)

theorem full_edge_count : Fintype.card (ν ⊕ (Σ i, Fin (d i))) =
    Fintype.card ν + ∑ i, d i := by
  simp [Fintype.card_sigma]

theorem next_edge_count : Fintype.card G.NextEdge =
    Fintype.card ν + 4*G.ports.pairCount := by
  simp only [NextEdge,Fintype.card_sum,Fintype.card_prod,Fintype.card_fin]
  omega

end QMAForkState
end ContinuumCoulomb

end

end OAI
