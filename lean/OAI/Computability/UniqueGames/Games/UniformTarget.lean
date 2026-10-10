import OAI.Computability.UniqueGames.Machines.MachineSubroutineLemmas
import OAI.Computability.UniqueGames.Machines.MachineUniformCopyOrder
import OAI.Computability.UniqueGames.Machines.MachineUniformRounding
import OAI.Computability.UniqueGames.Reduction.RealTargetLemmas

namespace OAI

namespace UniqueGamesTheorem.Explicit.UniformTarget

open UniqueGamesTheorem.Foundations Target Complexity
open UniqueGamesTheorem.Integration
open MachineUniformCopyOrder

theorem copy_length {α : Type*} (C : Nat) (xs : List α) :
    (copyMajor C xs).length = C * xs.length := by
  induction C with
  | zero => simp [copyMajor]
  | succ C ih =>
    simp [copyMajor, List.replicate_succ, List.flatten_cons, Nat.add_mul,
      Nat.add_comm]

def construct {q : Nat} (C : Nat) (hC : 0 < C) (g : Instance q) : Instance q where
  vertices := g.vertices
  constraints := copyMajor C g.constraints
  nonempty := by
    apply List.length_pos_iff.mp
    rw [copy_length]
    exact Nat.mul_pos hC g.constraintCount_positive

@[simp] theorem vertices {q : Nat} (C : Nat) (hC : 0 < C) (g : Instance q) :
    (construct C hC g).vertices = g.vertices := rfl

@[simp] theorem edge_count {q : Nat} (C : Nat) (hC : 0 < C) (g : Instance q) :
    (construct C hC g).constraints.length = C * g.constraints.length :=
  copy_length C g.constraints

private theorem count_append {n q : Nat} (a : Fin n → Fin q)
    (xs ys : List (Constraint n q)) :
    countSatisfied a (xs ++ ys) = countSatisfied a xs + countSatisfied a ys := by
  simp [GapSemantics.countSatisfied_eq_sum]

theorem count_copies {n q : Nat} (C : Nat) (es : List (Constraint n q))
    (a : Fin n → Fin q) :
    countSatisfied a (copyMajor C es) = C * countSatisfied a es := by
  induction C with
  | zero => simp [copyMajor, countSatisfied]
  | succ C ih =>
    change countSatisfied a (es ++ copyMajor C es) = _
    rw [count_append, ih, Nat.add_mul, Nat.one_mul]
    omega

theorem count {q : Nat} (C : Nat) (hC : 0 < C) (g : Instance q)
    (a : Fin g.vertices → Fin q) :
    countSatisfied a (construct C hC g).constraints = C * countSatisfied a g.constraints :=
  count_copies C g.constraints a

theorem maxSatisfied {q : Nat} (C : Nat) (hC : 0 < C) (g : Instance q) (hq : 0 < q) :
    InstanceValue.maxSatisfied (construct C hC g) = C * InstanceValue.maxSatisfied g := by
  classical
  apply Nat.le_antisymm
  · unfold InstanceValue.maxSatisfied
    apply Finset.sup_le
    intro a _
    change countSatisfied a (copyMajor C g.constraints) ≤ C * InstanceValue.maxSatisfied g
    erw [count_copies]
    exact Nat.mul_le_mul_left C (InstanceValue.countSatisfied_le_maxSatisfied g a)
  · obtain ⟨a, ha⟩ := InstanceValue.maxSatisfied_attained g hq
    rw [← ha, ← count C hC g a]
    exact InstanceValue.countSatisfied_le_maxSatisfied (construct C hC g) a

theorem value {q : Nat} (C : Nat) (hC : 0 < C) (g : Instance q) (hq : 0 < q) :
    InstanceValue.value (construct C hC g) = InstanceValue.value g := by
  have hc : (C : ℝ) ≠ 0 := by exact_mod_cast hC.ne'
  have hm : (g.constraints.length : ℝ) ≠ 0 := by
    exact_mod_cast g.constraintCount_positive.ne'
  unfold InstanceValue.value
  rw [maxSatisfied C hC g hq, edge_count]
  push_cast
  field_simp

theorem mem_original {q : Nat} (C : Nat) (hC : 0 < C) (g : Instance q)
    (c : Constraint g.vertices q) (hc : c ∈ (construct C hC g).constraints) :
    c ∈ g.constraints := by
  obtain ⟨es, hes, hc⟩ := List.mem_flatten.mp hc
  have he : es = g.constraints := List.eq_of_mem_replicate hes
  simpa [he] using hc

theorem translations {q s : Nat} (C : Nat) (hC : 0 < C) (g : Instance q)
    (coordinates : Fin q ≃ BinaryLinear.Vector s)
    (hg : TranslationTarget.IsTranslationInstance coordinates g) :
    TranslationTarget.IsTranslationInstance coordinates (construct C hC g) := by
  intro c hc
  exact hg c (mem_original C hC g c hc)

theorem flatMap_copies {α β : Type*} (C : Nat) (xs : List α) (f : α → List β) :
    (copyMajor C xs).flatMap f = copyMajor C (xs.flatMap f) := by
  induction C with
  | zero => simp [copyMajor]
  | succ C ih =>
    simpa only [copyMajor, List.replicate_succ, List.flatten_cons,
      List.flatMap_append] using congrArg (fun ys => xs.flatMap f ++ ys) ih

theorem encode_copies (C : Nat) (words : List Nat) :
    encodeWords (copyMajor C words) = copyMajor C (encodeWords words) := by
  induction C with
  | zero => rfl
  | succ C ih =>
    simpa only [copyMajor, List.replicate_succ, List.flatten_cons,
      encodeWords_append] using congrArg (fun xs => encodeWords words ++ xs) ih

/-- The complete output keeps the two first headers and scales the edge count. -/
theorem gameWords_construct {q : Nat} (C : Nat) (hC : 0 < C) (g : Instance q) :
    gameWords (construct C hC g) =
      [g.vertices, q, C * g.constraints.length] ++
        copyMajor C (g.constraints.flatMap constraintWords) := by
  simp only [gameWords, vertices]
  rw [show (construct C hC g).constraints = copyMajor C g.constraints from rfl,
    flatMap_copies, copy_length]

theorem gameBits_construct {q : Nat} (C : Nat) (hC : 0 < C) (g : Instance q) :
    gameBits (construct C hC g) =
      encodeWords [g.vertices, q, C * g.constraints.length] ++
        copyMajor C (encodeWords (g.constraints.flatMap constraintWords)) := by
  rw [gameBits, gameWords_construct, encodeWords_append, encode_copies]

end UniqueGamesTheorem.Explicit.UniformTarget

end OAI
