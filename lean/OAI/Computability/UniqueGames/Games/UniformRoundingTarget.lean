import OAI.Computability.UniqueGames.Games.UniformTarget

namespace OAI

section

namespace UniqueGamesTheorem.Explicit.UniformRoundingTarget

open UniqueGamesTheorem.Foundations.Target
open UniqueGamesTheorem.MachineUniformRounding
open UniqueGamesTheorem.MachineUniformCopyOrder

/-- Apply the concrete largest-remainder list of occurrence IDs to the original
list. Equal records at different indices remain separate input occurrences. -/
def rows {α : Type*} (C : Nat) (es : List α) : List α :=
  (Rounding.copies (Rounding.denominator es.length 1 C) es.length
    (fun _ => 1)).map es.get

theorem rows_eq_occurrenceMajor {α : Type*} (C : Nat) (es : List α)
    (h : 0 < es.length) : rows C es = occurrenceMajor C es := by
  unfold rows
  rw [copies_uniform es.length C h]
  simp only [List.map_flatten, List.map_ofFn, Function.comp_def, List.map_replicate]
  change (List.ofFn (fun i => List.replicate C (es.get i))).flatten =
    (es.map (fun e => List.replicate C e)).flatten
  congr 1
  calc
    List.ofFn (fun i => List.replicate C (es.get i)) =
        (List.ofFn es.get).map (fun e => List.replicate C e) := List.map_ofFn.symm
    _ = es.map (fun e => List.replicate C e) := by rw [List.ofFn_get]

/-- Exact multiplicities and full permutation records agree with the machine's
copy-major target; only the enumeration order changes. -/
theorem rows_perm_construct {q : Nat} (C : Nat) (hC : 0 < C) (g : Instance q) :
    (rows C g.constraints).Perm (UniformTarget.construct C hC g).constraints := by
  rw [rows_eq_occurrenceMajor C g.constraints g.constraintCount_positive]
  exact occurrenceMajor_perm_copyMajor C g.constraints

theorem selected_count_construct {q : Nat} (C : Nat) (hC : 0 < C) (g : Instance q)
    (a : Fin g.vertices → Fin q) :
    countSatisfied a (rows C g.constraints) =
      countSatisfied a (UniformTarget.construct C hC g).constraints :=
  Integration.InstanceEquivalences.countSatisfied_perm a (rows_perm_construct C hC g)

end UniqueGamesTheorem.Explicit.UniformRoundingTarget

end

end OAI
