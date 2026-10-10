import OAI.Computability.BinPacking.Arithmetic.GraphTallyMachine
import OAI.Computability.BinPacking.Packing.PackingTokenAffine

namespace OAI

namespace BinPackingGap.PackingCountMachine

open Turing
open BinPackingGames.Foundations.Complexity

structure Parameters where
  P : Nat
  K : Nat
  t : Nat
  d : Nat

def R (p : Parameters) (n : Nat) : Nat := BinPackingGap.repetitions p.P n p.K

theorem R_affine (p : Parameters) (n : Nat) :
    R p n = 100 * p.K * n + 100 * (p.P + 1) := by
  unfold R BinPackingGap.repetitions
  ring

def B (p : Parameters) (n m : Nat) : Nat := n * p.t + 4 * p.d * m * R p n

theorem B_accumulate (p : Parameters) (n m : Nat) :
    B p n m = (4 * p.d) * (R p n * m) + p.t * n := by
  unfold B
  ring

inductive Phase
  | repetitions
  | edgeCounter
  | treeBins
  | jobBins
  deriving DecidableEq

instance : Fintype Phase where
  elems := {.repetitions, .edgeCounter, .treeBins, .jobBins}
  complete phase := by cases phase <;> simp

inductive Label
  | affine (phase : Phase) (label : PackingTokenAffine.Label)
  | product (label : MachineUnaryMultiply.Label)
  deriving DecidableEq, Fintype

abbrev State (A : Type) := PackingTokenAffine.State A

def clean {A : Type} (ambient : A) : State A := ((ambient, ()), none)

def affineIndices : Phase → Fin 3 ↪ Fin 8
  | .repetitions => ⟨![0, 6, 2], by decide⟩
  | .edgeCounter => ⟨![1, 6, 3], by decide⟩
  | .treeBins => ⟨![0, 6, 5], by decide⟩
  | .jobBins => ⟨![4, 6, 5], by decide⟩

def productIndices : Fin 5 ↪ Fin 8 := ⟨![2, 3, 4, 7, 6], by decide⟩

variable {Tape Λ A : Type} [DecidableEq Tape]

def affineSlots (slots : Fin 8 ↪ Tape) (phase : Phase) : Fin 3 ↪ Tape :=
  (affineIndices phase).trans slots

def productSlots (slots : Fin 8 ↪ Tape) : Fin 5 ↪ Tape := productIndices.trans slots

def coefficient (p : Parameters) : Phase → Nat
  | .repetitions => 100 * p.K
  | .edgeCounter => 1
  | .treeBins => p.t
  | .jobBins => 4 * p.d

def offset (p : Parameters) : Phase → Nat
  | .repetitions => 100 * (p.P + 1)
  | _ => 0

def phaseExit (labels : Label → Λ) (exit : Option Λ) : Phase → Option Λ
  | .repetitions => some (labels (.affine .edgeCounter .seed))
  | .edgeCounter => some (labels (.product .copyDrain))
  | .treeBins => some (labels (.affine .jobBins .scan))
  | .jobBins => exit

def instruction (p : Parameters) (slots : Fin 8 ↪ Tape) (labels : Label → Λ)
    (exit : Option Λ) : Label → TM2.Stmt (fun _ : Tape => Bool) Λ (State A)
  | .affine phase l => PackingTokenAffine.instruction (coefficient p phase) (offset p phase)
      (affineSlots slots phase) (fun l => labels (.affine phase l))
      (phaseExit labels exit phase) l
  | .product l => MachineUnaryMultiply.statement (productSlots slots)
      (fun l => labels (.product l)) (some (labels (.affine .treeBins .seed))) l

def resultTapes (p : Parameters) (slots : Fin 8 ↪ Tape) (base : Tape → List Bool)
    (n m : Nat) : Tape → List Bool :=
  Function.update
    (Function.update
      (Function.update
        (Function.update base (slots 2) (encodeWord (R p n)))
        (slots 3) (encodeWord m))
      (slots 4) (encodeWord (R p n * m)))
    (slots 5) (encodeWord (B p n m))

theorem resultTapes_other (p : Parameters) (slots : Fin 8 ↪ Tape)
    (base : Tape → List Bool) (n m : Nat) (k : Tape)
    (h₂ : k ≠ slots 2) (h₃ : k ≠ slots 3) (h₄ : k ≠ slots 4) (h₅ : k ≠ slots 5) :
    resultTapes p slots base n m k = base k := by
  simp [resultTapes, h₂, h₃, h₄, h₅]

def steps (p : Parameters) (n m : Nat) : Nat :=
  (3 * n + 3) + (3 * m + 3) + MachineUnaryMultiply.steps (R p n) m +
    (3 * n + 3) + (3 * (R p n * m + 1) + 2)

theorem steps_eq (p : Parameters) (n m : Nat) :
    steps p n m = 6 * n + 11 * m + 6 * (R p n * m) + 21 := by
  unfold steps MachineUnaryMultiply.steps
  ring

noncomputable def timePolynomial (p : Parameters) : Polynomial Nat :=
  Polynomial.C (600 * p.K) * Polynomial.X ^ 2 +
    Polynomial.C (600 * (p.P + 1) + 17) * Polynomial.X + Polynomial.C 21

theorem steps_le_timePolynomial (p : Parameters) (n m s : Nat)
    (hn : n ≤ s) (hm : m ≤ s) :
    steps p n m ≤ (timePolynomial p).eval s := by
  have hR : R p n ≤ R p s := by
    unfold R BinPackingGap.repetitions
    exact Nat.mul_le_mul_left 100
      (Nat.add_le_add_right (Nat.add_le_add_left (Nat.mul_le_mul_right p.K hn) p.P) 1)
  have hRm := Nat.mul_le_mul hR hm
  have hlinear : steps p n m ≤ 17 * s + 6 * (R p s * s) + 21 := by
    rw [steps_eq]
    omega
  calc
    steps p n m ≤ 17 * s + 6 * (R p s * s) + 21 := hlinear
    _ = (timePolynomial p).eval s := by
      simp only [timePolynomial, Polynomial.eval_add, Polynomial.eval_mul,
        Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
      unfold R BinPackingGap.repetitions
      ring

theorem graph_steps_le_timePolynomial (p : Parameters) (input : GraphReductionInput) :
    steps p input.graph.n input.graph.edges.length ≤
      (timePolynomial p).eval (graphBits input).length :=
  steps_le_timePolynomial p _ _ _ (graph_vertexCount_le_bits input) (graph_edgeCount_le_bits input)

private theorem joinTrace {X : Type*} {f : X → X} {a b c : X} {n m : Nat}
    (first : f^[n] a = b) (second : f^[m] b = c) : f^[n + m] a = c := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

theorem countTrace (p : Parameters) (slots : Fin 8 ↪ Tape) (labels : Label → Λ)
    (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : Tape => Bool) Λ (State A))
    (atLabels : ∀ l, program (labels l) = instruction p slots labels exit l)
    (base : Tape → List Bool) (n m : Nat)
    (nWord : base (slots 0) = List.replicate n true)
    (mWord : base (slots 1) = List.replicate m true)
    (workspaceEmpty : ∀ j : Fin 8, 2 ≤ j.val → base (slots j) = [])
    (ambient : A) :
    (MachineComposition.advance (TM2.step program))^[steps p n m]
      (some ⟨some (labels (.affine .repetitions .seed)), clean ambient, base⟩) =
      some ⟨exit, clean ambient, resultTapes p slots base n m⟩ := by
  have h₂ := workspaceEmpty 2 (by decide)
  have h₃ := workspaceEmpty 3 (by decide)
  have h₄ := workspaceEmpty 4 (by decide)
  have h₅ := workspaceEmpty 5 (by decide)
  have h₆ := workspaceEmpty 6 (by decide)
  have h₇ := workspaceEmpty 7 (by decide)
  let b₁ := Function.update base (slots 2) (encodeWord (R p n))
  let b₂ := Function.update b₁ (slots 3) (encodeWord m)
  let b₃ := Function.update b₂ (slots 4) (encodeWord (R p n * m))
  let b₄ := Function.update b₃ (slots 5) (encodeWord (p.t * n))
  have r₁ : (MachineComposition.advance (TM2.step program))^[3 * n + 3]
      (some ⟨some (labels (.affine .repetitions .seed)), clean ambient, base⟩) =
      some ⟨some (labels (.affine .edgeCounter .seed)), clean ambient, b₁⟩ := by
    have run := PackingTokenAffine.seededTrace (100 * p.K) (100 * (p.P + 1))
      (affineSlots slots .repetitions) (fun l => labels (.affine .repetitions l))
      (some (labels (.affine .edgeCounter .seed))) program
      (fun l => atLabels (.affine .repetitions l)) base n nWord h₆ ambient
    change (MachineComposition.advance (TM2.step program))^[3 * n + 3]
      (some ⟨some (labels (.affine .repetitions .seed)), clean ambient, base⟩) =
      some ⟨some (labels (.affine .edgeCounter .seed)), clean ambient,
        Function.update base (slots 2)
          (encodeWord (100 * p.K * n + 100 * (p.P + 1)) ++ base (slots 2))⟩ at run
    simpa only [← R_affine, h₂, List.append_nil, b₁] using run
  have m₁ : b₁ (slots 1) = List.replicate m true := by
    simp [b₁, slots.injective.eq_iff, mWord]
  have s₁ : b₁ (slots 6) = [] := by simp [b₁, slots.injective.eq_iff, h₆]
  have e₁ : b₁ (slots 3) = [] := by simp [b₁, slots.injective.eq_iff, h₃]
  have r₂ : (MachineComposition.advance (TM2.step program))^[3 * m + 3]
      (some ⟨some (labels (.affine .edgeCounter .seed)), clean ambient, b₁⟩) =
      some ⟨some (labels (.product .copyDrain)), clean ambient, b₂⟩ := by
    have run := PackingTokenAffine.seededTrace 1 0 (affineSlots slots .edgeCounter)
      (fun l => labels (.affine .edgeCounter l)) (some (labels (.product .copyDrain)))
      program (fun l => atLabels (.affine .edgeCounter l)) b₁ m m₁ s₁ ambient
    change (MachineComposition.advance (TM2.step program))^[3 * m + 3]
      (some ⟨some (labels (.affine .edgeCounter .seed)), clean ambient, b₁⟩) =
      some ⟨some (labels (.product .copyDrain)), clean ambient,
        Function.update b₁ (slots 3) (encodeWord (1 * m + 0) ++ b₁ (slots 3))⟩ at run
    simpa only [one_mul, Nat.add_zero, e₁, List.append_nil, b₂] using run
  have a₂ : b₂ (slots 2) = encodeWord (R p n) := by
    simp [b₂, b₁, slots.injective.eq_iff]
  have b₂word : b₂ (slots 3) = encodeWord m := by simp [b₂]
  have s₂ : b₂ (slots 6) = [] := by simp [b₂, slots.injective.eq_iff, s₁]
  have c₂ : b₂ (slots 7) = [] := by
    simp [b₂, b₁, slots.injective.eq_iff, h₇]
  have e₂ : b₂ (slots 4) = [] := by
    simp [b₂, b₁, slots.injective.eq_iff, h₄]
  have r₃ : (MachineComposition.advance (TM2.step program))^[MachineUnaryMultiply.steps (R p n) m]
      (some ⟨some (labels (.product .copyDrain)), clean ambient, b₂⟩) =
      some ⟨some (labels (.affine .treeBins .seed)), clean ambient, b₃⟩ := by
    have run := MachineUnaryMultiply.multiplyTrace (productSlots slots)
      (fun l => labels (.product l)) (some (labels (.affine .treeBins .seed)))
      program (fun l => atLabels (.product l)) b₂ (R p n) m
      a₂ b₂word c₂ s₂ ambient none
    simpa [productSlots, productIndices, MachineUnaryMultiply.resultTapes,
      e₂, b₃, clean] using run
  have n₃ : b₃ (slots 0) = List.replicate n true := by
    simp [b₃, b₂, b₁, slots.injective.eq_iff, nWord]
  have s₃ : b₃ (slots 6) = [] := by simp [b₃, slots.injective.eq_iff, s₂]
  have e₃ : b₃ (slots 5) = [] := by
    simp [b₃, b₂, b₁, slots.injective.eq_iff, h₅]
  have r₄ : (MachineComposition.advance (TM2.step program))^[3 * n + 3]
      (some ⟨some (labels (.affine .treeBins .seed)), clean ambient, b₃⟩) =
      some ⟨some (labels (.affine .jobBins .scan)), clean ambient, b₄⟩ := by
    have run := PackingTokenAffine.seededTrace p.t 0 (affineSlots slots .treeBins)
      (fun l => labels (.affine .treeBins l)) (some (labels (.affine .jobBins .scan)))
      program (fun l => atLabels (.affine .treeBins l)) b₃ n n₃ s₃ ambient
    change (MachineComposition.advance (TM2.step program))^[3 * n + 3]
      (some ⟨some (labels (.affine .treeBins .seed)), clean ambient, b₃⟩) =
      some ⟨some (labels (.affine .jobBins .scan)), clean ambient,
        Function.update b₃ (slots 5) (encodeWord (p.t * n + 0) ++ b₃ (slots 5))⟩ at run
    simpa only [Nat.add_zero, e₃, List.append_nil, b₄] using run
  have a₄ : b₄ (slots 4) = encodeWord (R p n * m) := by
    simp [b₄, b₃, slots.injective.eq_iff]
  have s₄ : b₄ (slots 6) = [] := by simp [b₄, slots.injective.eq_iff, s₃]
  have d₄ : b₄ (slots 5) = encodeWord (p.t * n) ++ [] := by simp [b₄]
  have r₅ : (MachineComposition.advance (TM2.step program))^[3 * (R p n * m + 1) + 2]
      (some ⟨some (labels (.affine .jobBins .scan)), clean ambient, b₄⟩) =
      some ⟨exit, clean ambient, resultTapes p slots base n m⟩ := by
    have run := PackingTokenAffine.encodedAccumulateTrace (4 * p.d) 0
      (affineSlots slots .jobBins) (fun l => labels (.affine .jobBins l)) exit
      program (fun l => atLabels (.affine .jobBins l)) b₄ (R p n * m) (p.t * n) []
      a₄ s₄ d₄ ambient
    change (MachineComposition.advance (TM2.step program))^[3 * (R p n * m + 1) + 2]
      (some ⟨some (labels (.affine .jobBins .scan)), clean ambient, b₄⟩) =
      some ⟨exit, clean ambient,
        Function.update b₄ (slots 5)
          (encodeWord ((4 * p.d) * (R p n * m) + p.t * n) ++ [])⟩ at run
    simpa only [← B_accumulate, List.append_nil, b₄, b₃, b₂, b₁,
      Function.update_idem, resultTapes] using run
  exact joinTrace (joinTrace (joinTrace (joinTrace r₁ r₂) r₃) r₄) r₅

def countInTime (p : Parameters) (slots : Fin 8 ↪ Tape) (labels : Label → Λ)
    (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : Tape => Bool) Λ (State A))
    (atLabels : ∀ l, program (labels l) = instruction p slots labels exit l)
    (base : Tape → List Bool) (n m : Nat)
    (nWord : base (slots 0) = List.replicate n true)
    (mWord : base (slots 1) = List.replicate m true)
    (workspaceEmpty : ∀ j : Fin 8, 2 ≤ j.val → base (slots j) = [])
    (ambient : A) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels (.affine .repetitions .seed)), clean ambient, base⟩
      (some ⟨exit, clean ambient, resultTapes p slots base n m⟩) (steps p n m) where
  steps := steps p n m
  evals_in_steps := countTrace p slots labels exit program atLabels base n m
    nWord mWord workspaceEmpty ambient
  steps_le_m := Nat.le_refl _

def graphCountInTime (p : Parameters) (slots : Fin 8 ↪ Tape) (labels : Label → Λ)
    (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : Tape => Bool) Λ (State A))
    (atLabels : ∀ l, program (labels l) = instruction p slots labels exit l)
    (base : Tape → List Bool) (input : GraphReductionInput)
    (nWord : base (slots 0) = List.replicate input.graph.n true)
    (mWord : base (slots 1) = List.replicate input.graph.edges.length true)
    (workspaceEmpty : ∀ j : Fin 8, 2 ≤ j.val → base (slots j) = [])
    (ambient : A) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels (.affine .repetitions .seed)), clean ambient, base⟩
      (some ⟨exit, clean ambient,
        resultTapes p slots base input.graph.n input.graph.edges.length⟩)
      ((timePolynomial p).eval (graphBits input).length) where
  steps := steps p input.graph.n input.graph.edges.length
  evals_in_steps := countTrace p slots labels exit program atLabels base
    input.graph.n input.graph.edges.length nWord mWord workspaceEmpty ambient
  steps_le_m := graph_steps_le_timePolynomial p input

end BinPackingGap.PackingCountMachine

end OAI
