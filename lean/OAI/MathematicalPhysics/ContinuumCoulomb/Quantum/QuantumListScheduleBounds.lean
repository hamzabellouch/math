import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumListScheduleWeights
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumPathIteratedBound

namespace OAI

/-! Polynomial coefficient bounds for the actual finite output tape of the
fixed-round subdivision program. -/

noncomputable section
namespace ContinuumCoulomb.QuantumListSchedule
open scoped Classical

theorem value_edge_count (x : Input) : (value x).2.2.length≤3*x.2.2.2.length := by
  rw [value_length]
  have h := partition_lengths x.2.2.2
  omega

theorem iterate_edge_count (N : ℚ) (s : State) (k : ℕ) :
    (iterate N k s).2.2.length≤3^k*s.2.2.length := by
  induction k with
  | zero => simp [iterate]
  | succ k ih =>
    exact (value_edge_count (N,iterate N k s)).trans
      ((Nat.mul_le_mul_left 3 ih).trans_eq (by rw [pow_succ]; ac_rfl))

theorem value_coefficientBound {N : ℚ} (hN : 0 ≤ N) (s : State) (hs : Valid s)
    {m L T : ℝ} (hm : (s.2.2.length:ℝ) ≤ m) (hL : 1 ≤ L)
    (hT : |(N:ℝ)| ≤ T) (hc : (graph s hs).CoefficientBound L) :
    (graph (value (N,s)) (value_valid (N,s) hs)).CoefficientBound
      (qmaPathCoefficientBound m L T) := by
  have hm' : (Fintype.card (graph s hs).Edge:ℝ) ≤ m := by
    have hcard : Fintype.card (graph s hs).Edge=s.2.2.length :=
      (Fintype.card_congr (α := (graph s hs).Edge) (β := Fin s.2.2.length)
        (Equiv.refl _)).trans (Fintype.card_fin _)
    exact (congrArg (fun n : ℕ => (n:ℝ)) hcard).le.trans hm
  have h := (graph s hs).subdivide_coefficientBound (schedule s hs).active
    (fun _ => false) hN hm' hL hT hc
  constructor
  · exact (congrArg (fun q : ℚ => |(q:ℝ)|) (next_constant N s hs)).le.trans h.1
  · intro e
    exact (congrArg (fun q : ℚ => |(q:ℝ)|) (next_weight N s hs e)).le.trans (h.2 _)

theorem iterate_coefficientBound {N : ℚ} (hN : 0 ≤ N) (s : State) (hs : Valid s)
    {m L T : ℝ} (hm : (s.2.2.length:ℝ) ≤ m) (hL : 1 ≤ L)
    (hT : |(N:ℝ)| ≤ T) (hc : (graph s hs).CoefficientBound L) (k : ℕ) :
    (graph (iterate N k s) (iterate_valid N s hs k)).CoefficientBound
      (qmaPathIteratedBound m L T k) := by
  have hm0 : 0 ≤ m := (Nat.cast_nonneg _).trans hm
  induction k with
  | zero => exact hc
  | succ k ih =>
    have hcount : ((iterate N k s).2.2.length:ℝ) ≤ 3^k*m := by
      have hcast : ((iterate N k s).2.2.length:ℝ) ≤ 3^k*(s.2.2.length:ℝ) := by
        exact_mod_cast iterate_edge_count N s k
      exact hcast.trans (mul_le_mul_of_nonneg_left hm (by positivity))
    exact value_coefficientBound hN (iterate N k s) (iterate_valid N s hs k)
      hcount (qmaPathIteratedBound_one hm0 hL k) hT ih

end ContinuumCoulomb.QuantumListSchedule

end

end OAI
