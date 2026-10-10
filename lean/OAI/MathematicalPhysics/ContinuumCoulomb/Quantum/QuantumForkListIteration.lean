import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumForkListNextBackground

namespace OAI

/-! Full-space accuracy of the repeated literal fork compiler. All port and
ordinary-bond hypotheses are propagated from its actual input lists. -/

noncomputable section
namespace ContinuumCoulomb.QuantumForkList
open MediatorGraph QuantumAxisSample
open scoped Classical

theorem iterate_accuracy (s : State) (hs : ValidPorts s.1 s.2.2.2)
    (hb : SourceBondLists.bounded s.1 (background s))
    (hn : ∀ b ∈ background s, b.1 ≠ b.2.1) (N : ℚ) (hN : 0 < N) (k : ℕ) :
    |normalizedBottom (matrix (iterate N k s))-normalizedBottom (matrix s)| ≤
      (k:ℝ)/(N:ℝ) := by
  induction k with
  | zero =>
    rw [iterate]
    rw [sub_self,abs_zero,Nat.cast_zero,zero_div]
  | succ k ih =>
    have hv := iterate_background_valid s hs hb hn N k
    have he := next_accuracy (iterate N k s) (iterate_validPorts N s hs k)
      hv.1 hv.2 N hN
    calc
      _ ≤ |normalizedBottom (matrix (next N (iterate N k s)))-
          normalizedBottom (matrix (iterate N k s))|+
          |normalizedBottom (matrix (iterate N k s))-normalizedBottom (matrix s)| :=
        abs_sub_le _ _ _
      _ ≤ 1/(N:ℝ)+(k:ℝ)/(N:ℝ) := add_le_add he ih
      _ = ((k+1:ℕ):ℝ)/(N:ℝ) := by push_cast; ring

end ContinuumCoulomb.QuantumForkList

end

end OAI
