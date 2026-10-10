import Mathlib
import OAI.Combinatorics.KMedianRecovery.Branching.CopyComputes

namespace OAI

namespace MetricKMedianRecovery.BitMachine.RawUnary
open WordOperations
lemma copies_singleton (n : ℕ) (b : Bool) : RepeatedAppend.copies n [b]=List.replicate n b := by
  induction n with
  | zero=>rfl
  | succ n ih=>rw [RepeatedAppend.copies,ih,List.replicate_succ']
def run (x : List Bool) : List Bool := List.replicate x.length true
noncomputable def run_computes : PolyComputes run := by
  have hh:=UnaryResources.copy_computes id_computes (const_computes [true])
  unfold run
  simpa only [id_eq,copies_singleton] using hh
lemma run_length (x : List Bool) : (run x).length=x.length := List.length_replicate
end MetricKMedianRecovery.BitMachine.RawUnary

end OAI
