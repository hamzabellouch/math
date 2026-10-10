import Mathlib
import OAI.Combinatorics.Ramsey.CycleClique.BallPacking
import OAI.Combinatorics.Ramsey.CycleClique.CertificateDecisions
import OAI.Combinatorics.Ramsey.CycleClique.CertificateModel
import OAI.Combinatorics.Ramsey.CycleClique.CompactDecisions
import OAI.Combinatorics.Ramsey.CycleClique.CompactLabels
import OAI.Combinatorics.Ramsey.CycleClique.EdgeBits
import OAI.Combinatorics.Ramsey.CycleClique.EdgeDecisions
import OAI.Combinatorics.Ramsey.CycleClique.FiniteGraphs
import OAI.Combinatorics.Ramsey.CycleClique.LabelDecisions
import OAI.Combinatorics.Ramsey.CycleClique.MatrixBits
import OAI.Combinatorics.Ramsey.CycleClique.PathSystems

namespace OAI

namespace CycleClique
open scoped SimpleGraph

instance : Std.Commutative Nat.lor := ⟨Nat.lor_comm⟩
instance : Std.Associative Nat.lor := ⟨Nat.lor_assoc⟩
def qBits (q : Finset ℕ) : ℕ := q.fold Nat.lor 0 (fun i => 2^i)
theorem qBits_spec (q : Finset ℕ) (i : ℕ) : (qBits q).testBit i = true ↔ i ∈ q := by
  induction q using Finset.induction_on with
  | empty => simp [qBits]
  | @insert a s ha ih =>
    simp only [qBits, Finset.fold_insert ha]
    change ((2^a ||| qBits s).testBit i = true) ↔ _
    simp only [Nat.testBit_lor, Nat.testBit_two_pow, Bool.or_eq_true,
      decide_eq_true_eq, ih, Finset.mem_insert]
    tauto

end CycleClique

end OAI
