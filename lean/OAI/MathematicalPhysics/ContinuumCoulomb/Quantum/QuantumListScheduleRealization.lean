import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumListScheduleGeometry

namespace OAI

/-! Actual finite-list schedule: route preservation and nearest-neighbor
realization after the prescribed number of rounds. -/

noncomputable section
namespace ContinuumCoulomb.QuantumListSchedule
open scoped Classical

variable {Γ : SimpleGraph (ℕ × ℕ)}

def nextEmbedding (x : Input) (hs : Valid x.2)
    (P : QMAPathEmbedding (schedule x.2 hs) Γ) :
    QMAPathEmbedding (schedule (value x) (value_valid x hs)) Γ :=
  (nextRelabel x hs).symm.transport (P.next x.1)

theorem nextEmbedding_bounded (x : Input) (hs : Valid x.2)
    (P : QMAPathEmbedding (schedule x.2 hs) Γ) {X Y : ℕ}
    (h : P.Bounded X Y) : (nextEmbedding x hs P).Bounded X Y :=
  (nextRelabel x hs).symm.transport_bounded (P.next x.1) (P.next_bounded x.1 h)

theorem value_degree (x : Input) (hs : Valid x.2) {d : ℕ} (h3 : 3≤d)
    (hd : ∀ v, qmaGraphDegree (graph x.2 hs).left (graph x.2 hs).right v≤d) :
    ∀ v, qmaGraphDegree (graph (value x) (value_valid x hs)).left
      (graph (value x) (value_valid x hs)).right v≤d := by
  intro v
  exact (le_of_eq ((nextRelabel x hs).degree v).symm).trans
    ((schedule x.2 hs).next_degree x.1 h3 hd _)

def iterateEmbedding (N : ℚ) (s : State) (hs : Valid s)
    (P : QMAPathEmbedding (schedule s hs) Γ) :
    (k : ℕ) → QMAPathEmbedding (schedule (iterate N k s) (iterate_valid N s hs k)) Γ
  | 0 => P
  | k+1 => nextEmbedding (N,iterate N k s) (iterate_valid N s hs k)
      (iterateEmbedding N s hs P k)

theorem iterateEmbedding_bounded (N : ℚ) (s : State) (hs : Valid s)
    (P : QMAPathEmbedding (schedule s hs) Γ) {X Y : ℕ}
    (h : P.Bounded X Y) (k : ℕ) : (iterateEmbedding N s hs P k).Bounded X Y := by
  induction k with
  | zero => exact h
  | succ k ih => exact nextEmbedding_bounded _ _ _ ih

theorem iterate_degree (N : ℚ) (s : State) (hs : Valid s) {d : ℕ} (h3 : 3≤d)
    (hd : ∀ v, qmaGraphDegree (graph s hs).left (graph s hs).right v≤d) (k : ℕ) :
    ∀ v, qmaGraphDegree (graph (iterate N k s) (iterate_valid N s hs k)).left
      (graph (iterate N k s) (iterate_valid N s hs k)).right v≤d := by
  induction k with
  | zero => exact hd
  | succ k ih => exact value_degree _ _ h3 ih

theorem realize {N : ℚ} (hN : 0<N) (s : State) (hs : Valid s)
    (P : QMAPathEmbedding (schedule s hs) Γ) {D X Y d : ℕ} (h3 : 3≤d)
    (hD : ∀ e ∈ s.2.2, e.1≤D) (hbox : P.Bounded X Y)
    (hd : ∀ v, qmaGraphDegree (graph s hs).left (graph s hs).right v≤d) :
    ∃ position : Fin (iterate N D s).1 → ℕ × ℕ,
      Function.Injective position ∧
      (∀ v, (position v).1<X ∧ (position v).2<Y) ∧
      (∀ e : (graph (iterate N D s) (iterate_valid N s hs D)).Edge,
        Γ.Adj (position ((graph (iterate N D s) (iterate_valid N s hs D)).left e))
          (position ((graph (iterate N D s) (iterate_valid N s hs D)).right e))) ∧
      (∀ v, qmaGraphDegree (graph (iterate N D s) (iterate_valid N s hs D)).left
        (graph (iterate N D s) (iterate_valid N s hs D)).right v≤d) ∧
      (iterate N D s).1+(iterate N D s).2.2.length≤5^D*(s.1+s.2.2.length) ∧
      |energy (iterate N D s)-energy s|≤(D:ℝ)/(N:ℝ) := by
  let Q := iterateEmbedding N s hs P D
  refine ⟨Q.position,Q.position_injective,?_,?_,?_,?_,?_⟩
  · exact (iterateEmbedding_bounded N s hs P hbox D).1
  · exact Q.adjacent_of_complete (fun e => iterate_complete N s hD _ (List.get_mem _ e))
  · exact iterate_degree N s hs h3 hd D
  · exact iterate_size N s D
  · exact iterate_energy_error hN s hs D

end ContinuumCoulomb.QuantumListSchedule

end

end OAI
