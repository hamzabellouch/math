import OAI.Combinatorics.Ramsey.CycleClique.Construction.ConditionalMain
import OAI.Combinatorics.Ramsey.CycleClique.Construction.CEHamiltonicity

namespace OAI

/-! The unconditional exact cycle–clique Ramsey numbers, including R(C₃,K₃)=6. -/

namespace CycleClique.Construction
theorem cycle_clique_main_unconditional {m n : ℕ}
    (hn : 3 ≤ n) (hnm : n ≤ m) (hexcept : (m, n) ≠ (3, 3)) :
    IsRamseyNumber m n ((m - 1) * (n - 1) + 1) :=
  cycle_clique_main ceAlphaTwo_proved hn hnm hexcept

theorem cycle_clique_ramsey_unconditional {m n : ℕ}
    (hn : 3 ≤ n) (hnm : n ≤ m) :
    IsRamseyNumber m n (if m = 3 ∧ n = 3 then 6 else (m - 1) * (n - 1) + 1) :=
  cycle_clique_ramsey ceAlphaTwo_proved hn hnm

end CycleClique.Construction

end OAI
