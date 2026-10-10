import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumRationalPathStep

namespace OAI

/-! A bounded number of selected odd subdivisions realizes independently prescribed
path lengths. Only edges with remaining work receive a new mediator pair. -/

noncomputable section
namespace ContinuumCoulomb
open MediatorGraph
open scoped BigOperators Classical

structure QMAPathSchedule where
  graph : QMARationalExchangeGraph
  work : graph.Edge → ℕ

namespace QMAPathSchedule

def active (W : QMAPathSchedule) : Finset W.graph.Edge :=
  Finset.univ.filter (fun e => 0 < W.work e)

@[simp] theorem mem_active (W : QMAPathSchedule) (e : W.graph.Edge) :
    e ∈ W.active ↔ 0 < W.work e := by simp [active]

def nextWork (W : QMAPathSchedule) : QMAPartialPathsEdge W.active → ℕ
  | .inl _ => 0
  | .inr (.inl _) => 0
  | .inr (.inr (i,a)) => if a = 1 then W.work (qmaSelectedIndex W.active i)-1 else 0

def next (W : QMAPathSchedule) (N : ℚ) : QMAPathSchedule where
  graph := W.graph.subdivide W.active (fun _ => false) N
  work := W.nextWork

theorem next_work_le (W : QMAPathSchedule) (N : ℚ) {D : ℕ}
    (hD : ∀ e, W.work e ≤ D) : ∀ e, (W.next N).work e ≤ D-1 := by
  intro e
  rcases e with e | e
  · exact Nat.zero_le _
  rcases e with e | ⟨i,a⟩
  · exact Nat.zero_le _
  change (if a = 1 then W.work (qmaSelectedIndex W.active i)-1 else 0) ≤ D-1
  split
  · exact Nat.sub_le_sub_right (hD _) 1
  · exact Nat.zero_le _

theorem next_degree (W : QMAPathSchedule) (N : ℚ) {d : ℕ} (h3 : 3 ≤ d)
    (hd : ∀ v, qmaGraphDegree W.graph.left W.graph.right v ≤ d) :
    ∀ v, qmaGraphDegree (W.next N).graph.left (W.next N).graph.right v ≤ d := by
  intro v
  obtain ⟨v,rfl⟩ := (vertexEquiv W.graph.n W.active.card).surjective v
  rcases v with v | ⟨e,b⟩
  · change qmaGraphDegree (qmaPartialPathsLeft W.graph.left W.graph.right W.active)
      (qmaPartialPathsRight W.graph.right W.active (fun _ => false)) (old _ _ v) ≤ d
    rw [qmaPartialPaths_old_degree _ _ W.graph.distinct]
    exact hd v
  · change qmaGraphDegree (qmaPartialPathsLeft W.graph.left W.graph.right W.active)
      (qmaPartialPathsRight W.graph.right W.active (fun _ => false)) (fresh _ _ e b) ≤ d
    exact (qmaPartialPaths_fresh_degree _ _ _ _ e b).trans h3

def iterate (W : QMAPathSchedule) (N : ℚ) : ℕ → QMAPathSchedule
  | 0 => W
  | k+1 => (W.iterate N k).next N

theorem iterate_work_le (W : QMAPathSchedule) (N : ℚ) {D : ℕ}
    (hD : ∀ e, W.work e ≤ D) (k : ℕ) : ∀ e, (W.iterate N k).work e ≤ D-k := by
  induction k with
  | zero => exact hD
  | succ k ih =>
    change ∀ e, ((W.iterate N k).next N).work e ≤ D-(k+1)
    intro e
    have h := (W.iterate N k).next_work_le N ih e
    simpa only [Nat.sub_sub,Nat.add_comm 1 k] using h

theorem iterate_complete (W : QMAPathSchedule) (N : ℚ) {D : ℕ}
    (hD : ∀ e, W.work e ≤ D) : ∀ e, (W.iterate N D).work e = 0 := by
  intro e
  have h := W.iterate_work_le N hD D e
  omega

theorem iterate_degree (W : QMAPathSchedule) (N : ℚ) {d : ℕ} (h3 : 3 ≤ d)
    (hd : ∀ v, qmaGraphDegree W.graph.left W.graph.right v ≤ d) (k : ℕ) :
    ∀ v, qmaGraphDegree (W.iterate N k).graph.left (W.iterate N k).graph.right v ≤ d := by
  induction k with
  | zero => exact hd
  | succ k ih => exact (W.iterate N k).next_degree N h3 ih

theorem iterate_energy_error (W : QMAPathSchedule) {N : ℚ} (hN : 0 < N) (k : ℕ) :
    |(W.iterate N k).graph.energy-W.graph.energy| ≤ (k:ℝ)/(N:ℝ) := by
  induction k with
  | zero => simp [iterate]
  | succ k ih =>
    have h := (W.iterate N k).graph.subdivide_energy_error (W.iterate N k).active
      (fun _ => false) hN
    change |((W.iterate N k).next N).graph.energy-W.graph.energy| ≤ _
    calc
      _ ≤ |((W.iterate N k).next N).graph.energy-(W.iterate N k).graph.energy| +
          |(W.iterate N k).graph.energy-W.graph.energy| := abs_sub_le _ _ _
      _ ≤ 1/(N:ℝ)+(k:ℝ)/(N:ℝ) := add_le_add h ih
      _ = ((k+1:ℕ):ℝ)/(N:ℝ) := by push_cast; ring

theorem next_edge_count (W : QMAPathSchedule) (N : ℚ) :
    Fintype.card (W.next N).graph.Edge ≤ 3*Fintype.card W.graph.Edge := by
  change Fintype.card (W.graph.subdivide W.active (fun _ => false) N).Edge ≤ _
  rw [QMARationalExchangeGraph.subdivide_edge_count]
  have h := Finset.card_le_univ W.active
  omega

theorem iterate_edge_count (W : QMAPathSchedule) (N : ℚ) (k : ℕ) :
    Fintype.card (W.iterate N k).graph.Edge ≤ 3^k*Fintype.card W.graph.Edge := by
  induction k with
  | zero =>
    change Fintype.card W.graph.Edge ≤ 3^0*Fintype.card W.graph.Edge
    simp only [pow_zero,one_mul,le_refl]
  | succ k ih =>
    change Fintype.card ((W.iterate N k).next N).graph.Edge ≤ _
    exact ((W.iterate N k).next_edge_count N).trans (by simpa [pow_succ,mul_assoc,mul_comm,
      mul_left_comm] using (Nat.mul_le_mul_left 3 ih))

end QMAPathSchedule
end ContinuumCoulomb

end

end OAI
