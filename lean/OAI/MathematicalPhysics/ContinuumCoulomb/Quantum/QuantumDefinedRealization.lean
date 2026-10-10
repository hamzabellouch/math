import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumPlanarRouteRealization
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumPathIteratedBound

namespace OAI

/-! The planar realization has a specified finite graph and placement, so its
coefficient and serialization bounds refer to the same physical output. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical

namespace QMAPathSchedule

theorem iterate_vertices_ge (W : QMAPathSchedule) (N : ℚ) (k : ℕ) :
    W.graph.n ≤ (W.iterate N k).graph.n := by
  induction k with
  | zero => exact le_rfl
  | succ k ih =>
    change W.graph.n ≤ (W.iterate N k).graph.n+(W.iterate N k).active.card*2
    omega

end QMAPathSchedule

namespace QMAEvenRouteData
variable {G : QMARationalExchangeGraph} (P : QMAEvenRouteData G)

def output (N : ℚ) (D : ℕ) : QMARationalExchangeGraph := ((P.schedule N).iterate N D).graph

def outputPosition (N : ℚ) (D : ℕ) := ((P.embedding N).iterate N D).position

theorem output_vertices_ge (N : ℚ) (D : ℕ) : G.n ≤ (P.output N D).n := by
  have h := (P.schedule N).iterate_vertices_ge N D
  change G.n+(Finset.univ : Finset G.Edge).card*2 ≤ (P.output N D).n at h
  omega

theorem output_position_injective (N : ℚ) (D : ℕ) :
    Function.Injective (P.outputPosition N D) := ((P.embedding N).iterate N D).position_injective

theorem output_position_bounded (N : ℚ) (D : ℕ) {X Y : ℕ} (hbox : P.Bounded X Y) :
    ∀ v, (P.outputPosition N D v).1 < X ∧ (P.outputPosition N D v).2 < Y :=
  ((P.embedding N).iterate_bounded N (P.embedding_bounded N hbox) D).1

theorem output_adjacent (N : ℚ) {D : ℕ} (hD : ∀ e, P.work e ≤ D)
    (e : (P.output N D).Edge) :
    qmaSquareGrid.Adj (P.outputPosition N D ((P.output N D).left e))
      (P.outputPosition N D ((P.output N D).right e)) :=
  ((P.embedding N).iterate N D).adjacent_of_complete
    ((P.schedule N).iterate_complete N (P.schedule_work_le N hD)) e

theorem output_degree (N : ℚ) (D : ℕ) {d : ℕ} (h3 : 3 ≤ d)
    (hd : ∀ v, qmaGraphDegree G.left G.right v ≤ d) :
    ∀ v, qmaGraphDegree (P.output N D).left (P.output N D).right v ≤ d :=
  (P.schedule N).iterate_degree N h3 (P.schedule_degree N h3 hd) D

theorem output_size (N : ℚ) (D : ℕ) :
    (P.output N D).n+Fintype.card (P.output N D).Edge ≤
      5^(D+1)*(G.n+Fintype.card G.Edge) := by
  have h := (P.schedule N).iterate_size N D
  have hs := Nat.mul_le_mul_left (5^D) (P.schedule_size N)
  exact h.trans (by simpa [pow_succ,mul_assoc] using hs)

theorem output_energy_error {N : ℚ} (hN : 0 < N) (D : ℕ) :
    |(P.output N D).energy-G.energy| ≤ ((D+1:ℕ):ℝ)/(N:ℝ) := by
  have he := (P.schedule N).iterate_energy_error hN D
  calc
    _ ≤ |(P.output N D).energy-(P.schedule N).graph.energy|+
        |(P.schedule N).graph.energy-G.energy| := abs_sub_le _ _ _
    _ ≤ (D:ℝ)/(N:ℝ)+1/(N:ℝ) := add_le_add he (P.schedule_energy_error hN)
    _ = _ := by push_cast; ring

end QMAEvenRouteData
end ContinuumCoulomb

end

end OAI
