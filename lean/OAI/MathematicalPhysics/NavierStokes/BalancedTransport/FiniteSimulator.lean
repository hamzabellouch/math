import OAI.MathematicalPhysics.NavierStokes.BalancedTransport.MachineRecursion

namespace OAI

noncomputable section
namespace BalancedTransport.Universal
open Turing StateTransition
open scoped Classical
variable {α : Type*} [Fintype α]

def finiteIndex (a : α) : Fin (Fintype.card α + 1) := (Fintype.equivFin α a).castSucc

def finiteUnindex (a₀ : α) (i : Fin (Fintype.card α + 1)) : α :=
  if h : i.val < Fintype.card α then (Fintype.equivFin α).symm ⟨i.val,h⟩ else a₀

@[simp] lemma finiteUnindex_index (a₀ a : α) : finiteUnindex a₀ (finiteIndex a) = a := by
  simp [finiteUnindex, finiteIndex]

lemma finiteIndex_injective : Function.Injective (finiteIndex (α := α)) :=
  fun a b h => by simpa using congrArg (finiteUnindex a) h

end BalancedTransport.Universal
end

noncomputable section
namespace BalancedTransport.Universal
open Turing StateTransition
open scoped Classical
variable {Γ Λ : Type*} [Fintype Γ] [Inhabited Γ] [Inhabited Λ]
variable (P : TM0.Machine Γ Λ) (S : Finset Λ) (ss : TM0.Supports P S)

def stateIndex (q : Λ) : Fin (Fintype.card {q : Λ // q ∈ S} + 1) :=
  finiteIndex (if h : q ∈ S then (⟨q,h⟩ : {q : Λ // q ∈ S}) else ⟨default,ss.1⟩)

omit [Fintype Γ] [Inhabited Γ] in
lemma stateIndex_decode {q : Λ} (hq : q ∈ S) :
    (finiteUnindex ⟨default,ss.1⟩ (stateIndex P S ss q) : {q : Λ // q ∈ S}).val = q := by
  simp [stateIndex, hq]

def postInstruction (a : Fin (Fintype.card Γ + 1)) (v : Λ × TM0.Stmt Γ) :
    Recorder.Transition (Fin (Fintype.card {q : Λ // q ∈ S} + 1)) (Fin (Fintype.card Γ + 1)) :=
  ⟨stateIndex P S ss v.1,
    (match v.2 with | .write b => finiteIndex b | .move _ => a),
    (match v.2 with | .write _ => .stay | .move .left => .left | .move .right => .right)⟩

abbrev finitePostMachine : FiniteMachine where
  states := Fintype.card {q : Λ // q ∈ S}
  symbols := Fintype.card Γ
  initial := stateIndex P S ss default
  blank := finiteIndex (default : Γ)
  transition q a := (P (finiteUnindex ⟨default,ss.1⟩ q : {q : Λ // q ∈ S}).val (finiteUnindex default a)).map
    (postInstruction P S ss a)

lemma finitePostMachine_instruction (q : Λ) (hq : q ∈ S) (a : Γ) :
    (finitePostMachine P S ss).transition (stateIndex P S ss q) (finiteIndex a) =
      (P q a).map (postInstruction P S ss (finiteIndex a)) := by
  simp [finitePostMachine, stateIndex_decode P S ss hq]

def PostRel (c : TM0.Cfg Γ Λ) (d : TapeConfiguration (finitePostMachine P S ss)) : Prop :=
  c.q ∈ S ∧ d.state = stateIndex P S ss c.q ∧
    ∀ i : ℤ, d.tape (d.head + i) = finiteIndex (c.Tape.nth i)

lemma post_initial_rel (w : List Γ) : PostRel P S ss (TM0.init w)
    (initialConfiguration (finitePostMachine P S ss) (w.map finiteIndex)) := by
  refine ⟨ss.1, rfl, ?_⟩
  intro i
  simp only [initialConfiguration, zero_add, TM0.init, Tape.mk₁, Tape.mk₂]
  by_cases hi : 0 ≤ i
  · rw [ite_eq_left hi, ← Int.toNat_of_nonneg hi]
    simp only [Tape.mk'_nth_nat, ListBlank.nth_mk, List.getI_eq_getElem?_getD,
      List.getElem?_map, Int.toNat_natCast]
    cases w[i.toNat]? <;> rfl
  · have hi' : i < 0 := lt_of_not_ge hi
    rw [ite_eq_right hi]
    cases i with
    | ofNat n => exact False.elim (not_lt_of_ge (Int.natCast_nonneg _) hi')
    | negSucc n =>
      change finiteIndex (default : Γ) = finiteIndex ((ListBlank.mk []).nth n)
      rw [ListBlank.nth_mk]
      rfl

lemma post_tape_head {c : TM0.Cfg Γ Λ} {d : TapeConfiguration (finitePostMachine P S ss)}
    (h : PostRel P S ss c d) : d.tape d.head = finiteIndex c.Tape.head := by
  simpa using h.2.2 0

lemma post_step (c : TM0.Cfg Γ Λ) (d : TapeConfiguration (finitePostMachine P S ss))
    (h : PostRel P S ss c d) :
    match TM0.step P c with
    | none => machineStep (finitePostMachine P S ss) d = none
    | some c' => ∃ d', machineStep (finitePostMachine P S ss) d = some d' ∧ PostRel P S ss c' d' := by
  have ht : (finitePostMachine P S ss).transition d.state (d.tape d.head) =
      (P c.q c.Tape.head).map (postInstruction P S ss (finiteIndex c.Tape.head)) := by
    rw [h.2.1, post_tape_head P S ss h, finitePostMachine_instruction P S ss _ h.1]
  unfold machineStep
  rw [ht]
  simp only [TM0.step]
  cases hp : P c.q c.Tape.head with
  | none => rfl
  | some v =>
    rcases v with ⟨q', act⟩
    have hq' : q' ∈ S := ss.2 hp h.1
    cases act with
    | write b =>
      simp only [Option.map_some, postInstruction]
      refine ⟨_,rfl,hq',rfl,?_⟩
      intro i
      change Function.update d.tape d.head (finiteIndex b) (d.head + 0 + i) =
        finiteIndex ((c.Tape.write b).nth i)
      simp only [Int.add_zero, Tape.write_nth]
      by_cases hi : i = 0
      · subst i; simp
      · have hi' : d.head + i ≠ d.head := by omega
        rw [ite_eq_right hi, Function.update_of_ne hi']
        exact h.2.2 i
    | move dir =>
      have hu : Function.update d.tape d.head (finiteIndex c.Tape.head) = d.tape := by
        rw [← post_tape_head P S ss h, Function.update_eq_self]
      cases dir with
      | left =>
        simp only [Option.map_some, postInstruction]
        refine ⟨_,rfl,hq',rfl,?_⟩
        intro i
        change Function.update d.tape d.head (finiteIndex c.Tape.head) (d.head + (-1) + i) =
          finiteIndex ((c.Tape.move .left).nth i)
        rw [hu, Tape.move_left_nth]
        convert h.2.2 (i-1) using 1
        congr 1
        ring
      | right =>
        simp only [Option.map_some, postInstruction]
        refine ⟨_,rfl,hq',rfl,?_⟩
        intro i
        change Function.update d.tape d.head (finiteIndex c.Tape.head) (d.head + 1 + i) =
          finiteIndex ((c.Tape.move .right).nth i)
        rw [hu, Tape.move_right_nth]
        convert h.2.2 (i+1) using 1
        congr 1
        ring

lemma post_respects : StateTransition.Respects (TM0.step P) (machineStep (finitePostMachine P S ss))
    (PostRel P S ss) := by
  intro c d hr
  have h := post_step P S ss c d hr
  cases he : TM0.step P c with
  | none => simpa [he] using h
  | some c' =>
    simp only [he] at h
    obtain ⟨d',hd,hr'⟩ := h
    exact ⟨d',hr',Relation.TransGen.single hd⟩

lemma halts_finitePostMachine (w : List Γ) :
    Halts (finitePostMachine P S ss) (w.map finiteIndex) ↔ (TM0.eval P w).Dom := by
  exact (halts_iff_eval_dom _ _).trans
    (StateTransition.tr_eval_dom (post_respects P S ss) (post_initial_rel P S ss w))

end BalancedTransport.Universal
end

end OAI
