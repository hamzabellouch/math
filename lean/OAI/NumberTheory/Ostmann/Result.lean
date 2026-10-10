import OAI.NumberTheory.Ostmann.Assembly
import OAI.NumberTheory.Ostmann.Conclusion.ActualNoDecomposition
import OAI.NumberTheory.Ostmann.Statement

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

namespace Ostmann
open scoped Pointwise symmDiff

theorem main : ∀ A B : Set ℕ, A.Nontrivial → B.Nontrivial →
    Set.Infinite ((A + B) ∆ {n : ℕ | Nat.Prime n}) :=
  assemble_from_infinite_case Conclusion.actual_no_decomposition

end Ostmann

end OAI
