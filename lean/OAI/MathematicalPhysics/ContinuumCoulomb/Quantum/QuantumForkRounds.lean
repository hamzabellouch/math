import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumForkStateDegree

namespace OAI

/-! Constantly many actual fork rounds give a degree-three graph of linear size. -/

noncomputable section
namespace ContinuumCoulomb
open scoped BigOperators Classical

structure QMAForkNetwork (c : ℕ) where
  n : ℕ
  degree : Fin c → ℕ
  Edge : Type
  [edgeFinite : Fintype Edge]
  state : QMAForkState n c degree Edge

attribute [instance] QMAForkNetwork.edgeFinite

namespace QMAForkNetwork
variable {c : ℕ}

def next (G : QMAForkNetwork c) : QMAForkNetwork c where
  n := G.n + G.state.ports.pairCount*2
  degree := fun i => G.degree i / 2 + G.degree i % 2
  Edge := G.state.NextEdge
  state := G.state.next

def iterate (G : QMAForkNetwork c) : ℕ → QMAForkNetwork c
  | 0 => G
  | k+1 => (G.iterate k).next

theorem iterate_degree (G : QMAForkNetwork c) (k : ℕ) (i : Fin c) :
    (G.iterate k).degree i = qmaForkDegreeAfter (G.degree i) k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change (G.iterate k).degree i / 2 + (G.iterate k).degree i % 2 = _
    rw [ih]
    rfl

theorem next_degree_le (G : QMAForkNetwork c) (i : Fin c) :
    G.next.degree i ≤ G.degree i := by
  change G.degree i / 2 + G.degree i % 2 ≤ G.degree i
  omega

theorem iterate_degree_le (G : QMAForkNetwork c) (k : ℕ) (i : Fin c) :
    (G.iterate k).degree i ≤ G.degree i := by
  induction k with
  | zero => exact le_rfl
  | succ k ih => exact ((G.iterate k).next_degree_le i).trans ih

theorem iterate_mass_le (G : QMAForkNetwork c) (k : ℕ) :
    (∑ i, (G.iterate k).degree i) ≤ ∑ i, G.degree i :=
  Finset.sum_le_sum (fun i _ => G.iterate_degree_le k i)

theorem iterate_vertices (G : QMAForkNetwork c) (k : ℕ) :
    (G.iterate k).n ≤ G.n + 2*k*(∑ i, G.degree i) := by
  induction k with
  | zero => simp [iterate]
  | succ k ih =>
    have hp := (G.iterate k).state.ports.pairCount_bound
    have hm := G.iterate_mass_le k
    change (G.iterate k).n + (G.iterate k).state.ports.pairCount*2 ≤ _
    calc
      _ ≤ (G.n + 2*k*(∑ i, G.degree i)) + 2*(∑ i, G.degree i) := by omega
      _ = G.n + 2*(k+1)*(∑ i, G.degree i) := by ring

theorem iterate_background_edges (G : QMAForkNetwork c) (k : ℕ) :
    Fintype.card (G.iterate k).Edge ≤ Fintype.card G.Edge + 4*k*(∑ i, G.degree i) := by
  induction k with
  | zero =>
    simp only [iterate,Nat.mul_zero,zero_mul,add_zero]
    exact (Fintype.card_congr (Equiv.refl G.Edge)).le
  | succ k ih =>
    have hp := (G.iterate k).state.ports.pairCount_bound
    have hm := G.iterate_mass_le k
    change Fintype.card (G.iterate k).state.NextEdge ≤ _
    rw [(G.iterate k).state.next_edge_count]
    calc
      _ ≤ (Fintype.card G.Edge + 4*k*(∑ i, G.degree i)) + 4*(∑ i, G.degree i) := by omega
      _ = Fintype.card G.Edge + 4*(k+1)*(∑ i, G.degree i) := by ring

theorem constant_round_degree (G : QMAForkNetwork c) (D : ℕ)
    (hD : ∀ i, G.degree i ≤ D) (v : Fin (G.iterate D).n) :
    qmaGraphDegree (G.iterate D).state.fullLeft (G.iterate D).state.fullRight v ≤ 3 := by
  apply (G.iterate D).state.full_degree_le_three
  intro i
  rw [G.iterate_degree]
  exact (qmaForkDegreeAfter_constant _ D (hD i)).trans (by decide)

end QMAForkNetwork
end ContinuumCoulomb

end

end OAI
