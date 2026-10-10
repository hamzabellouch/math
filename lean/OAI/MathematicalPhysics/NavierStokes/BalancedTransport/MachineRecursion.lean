import OAI.MathematicalPhysics.NavierStokes.BalancedTransport.ComputabilityRules

namespace OAI

noncomputable section
namespace BalancedTransport.Universal
open Effectivity
open Effectivity.ComputableRules

abbrev RawInstruction := ℕ × ℕ × ℕ

abbrev RawMachine := ℕ × ℕ × ℕ × ℕ × List (List (Option RawInstruction))

abbrev RawState := ℕ × ℤ × List (ℤ × ℕ)

abbrev RawRun := RawMachine × List ℕ × RawState

def serialize (M : FiniteMachine) : RawMachine :=
  (M.states, M.symbols, M.initial.val, M.blank.val,
    (List.finRange (M.states + 1)).map fun q =>
      (List.finRange (M.symbols + 1)).map fun a =>
        (M.transition q a).map fun v => (v.state.val, v.write.val, v.move.number))

def rawBase (blank : ℕ) (w : List ℕ) (z : ℤ) : ℕ :=
  if (z.toNat : ℤ) = z then w.getD z.toNat blank else blank

def rawRead (blank : ℕ) (w : List ℕ) (writes : List (ℤ × ℕ)) (z : ℤ) : ℕ :=
  writes.foldl (fun value p => if z = p.1 then p.2 else value) (rawBase blank w z)

def rawMove (d : ℕ) : ℤ := if d = 0 then 0 else if d = 1 then -1 else 1

def rawStep (r : RawRun) : Option RawRun :=
  let m := r.1
  let w := r.2.1
  let c := r.2.2
  ((m.2.2.2.2.getD c.1 []).getD (rawRead m.2.2.2.1 w c.2.2 c.2.1) none).map
    fun v => (m, w, v.1, c.2.1 + rawMove v.2.2, c.2.2 ++ [(c.2.1, v.2.1)])

def rawInit (n : ℕ) : RawRun :=
  let p := (Encodable.decode (α := ℕ × List ℕ) n).getD (0, [])
  let m := (Encodable.decode (α := RawMachine) p.1).getD (0,0,0,0,[])
  (m, p.2, m.2.2.1, 0, [])

@[fun_prop] lemma computable_int_toNat : Computable Int.toNat := primrec_int_toNat.to_comp

@[fun_prop] lemma computable_int_ofNat : Computable (Int.ofNat : ℕ → ℤ) := primrec_int_ofNat.to_comp

@[fun_prop] lemma computable_int_add : Computable (fun p : ℤ × ℤ => p.1 + p.2) := primrec_int_add.to_comp

lemma primrec_rawBase : Primrec (fun p : ℕ × List ℕ × ℤ => rawBase p.1 p.2.1 p.2.2) := by
  unfold rawBase
  exact Primrec.ite
    (Primrec.eq.comp (primrec_int_ofNat.comp (primrec_int_toNat.comp (Primrec.snd.comp Primrec.snd)))
      (Primrec.snd.comp Primrec.snd))
    (Primrec.option_getD.comp (Primrec.list_getElem?.comp (Primrec.fst.comp Primrec.snd)
      (primrec_int_toNat.comp (Primrec.snd.comp Primrec.snd))) Primrec.fst)
    Primrec.fst

lemma computable_rawRead : Computable (fun p : ℕ × List ℕ × List (ℤ × ℕ) × ℤ =>
    rawRead p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  unfold rawRead
  apply Primrec.to_comp
  apply Primrec.list_foldl (h := fun (p : ℕ × List ℕ × List (ℤ × ℕ) × ℤ) (v : ℕ × (ℤ × ℕ)) =>
      if p.2.2.2 = v.2.1 then v.2.2 else v.1) (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
    (primrec_rawBase.comp (Primrec.fst.pair ((Primrec.fst.comp Primrec.snd).pair
      (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))))
  exact (Primrec.ite
    (Primrec.eq.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))
      (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)))
    (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
    (Primrec.fst.comp Primrec.snd)).to₂

lemma computable_rawMove : Computable rawMove := by
  unfold rawMove
  exact (Primrec.ite (Primrec.eq.comp Primrec.id (Primrec.const 0)) (Primrec.const (0:ℤ))
    (Primrec.ite (Primrec.eq.comp Primrec.id (Primrec.const 1))
      (Primrec.const (-1:ℤ)) (Primrec.const (1:ℤ)))).to_comp

lemma computable_rawSymbol : Computable (fun r : RawRun =>
    rawRead r.1.2.2.2.1 r.2.1 r.2.2.2.2 r.2.2.2.1) := by
  have hM : Computable (fun r : RawRun => r.1) := Computable.fst
  have hw : Computable (fun r : RawRun => r.2.1) := Computable.fst.comp Computable.snd
  have hc : Computable (fun r : RawRun => r.2.2) := Computable.snd.comp Computable.snd
  have hh : Computable (fun r : RawRun => r.2.2.2.1) := Computable.fst.comp (Computable.snd.comp hc)
  have hs : Computable (fun r : RawRun => r.2.2.2.2) := Computable.snd.comp (Computable.snd.comp hc)
  have hb : Computable (fun r : RawRun => r.1.2.2.2.1) :=
    Computable.fst.comp (Computable.snd.comp (Computable.snd.comp (Computable.snd.comp hM)))
  exact computable_rawRead.comp
    (g := fun r : RawRun => (r.1.2.2.2.1,r.2.1,r.2.2.2.2,r.2.2.2.1))
    (hb.pair (hw.pair (hs.pair hh)))

lemma computable_rawInstruction : Computable (fun r : RawRun =>
    (r.1.2.2.2.2.getD r.2.2.1 []).getD
      (rawRead r.1.2.2.2.1 r.2.1 r.2.2.2.2 r.2.2.2.1) none) := by
  have hq : Computable (fun r : RawRun => r.2.2.1) :=
    Computable.fst.comp (Computable.snd.comp Computable.snd)
  have ht : Computable (fun r : RawRun => r.1.2.2.2.2) :=
    Computable.snd.comp (Computable.snd.comp (Computable.snd.comp (Computable.snd.comp Computable.fst)))
  exact (Primrec.list_getD (none : Option RawInstruction)).to_comp.comp
    ((Primrec.list_getD ([] : List (Option RawInstruction))).to_comp.comp ht hq) computable_rawSymbol

lemma computable_rawAdvanceState : Computable (fun p : RawState × RawInstruction =>
    (p.2.1, p.1.2.1 + rawMove p.2.2.2, p.1.2.2 ++ [(p.1.2.1,p.2.2.1)])) := by
  have hh : Computable (fun p : RawState × RawInstruction => p.1.2.1) :=
    Computable.fst.comp (Computable.snd.comp Computable.fst)
  have hs : Computable (fun p : RawState × RawInstruction => p.1.2.2) :=
    Computable.snd.comp (Computable.snd.comp Computable.fst)
  have hw : Computable (fun p : RawState × RawInstruction => p.2.2.1) :=
    Computable.fst.comp (Computable.snd.comp Computable.snd)
  have hd : Computable (fun p : RawState × RawInstruction => rawMove p.2.2.2) :=
    computable_rawMove.comp (Computable.snd.comp (Computable.snd.comp Computable.snd))
  exact (Computable.fst.comp Computable.snd).pair
    ((primrec_int_add.to_comp.comp hh hd).pair
      (Primrec.list_append.to_comp.comp hs
        (Primrec.list_cons.to_comp.comp (hh.pair hw) (Computable.const []))))

lemma computable_rawAdvance : Computable (fun p : RawRun × RawInstruction =>
    (p.1.1, p.1.2.1, p.2.1, p.1.2.2.2.1 + rawMove p.2.2.2,
      p.1.2.2.2.2 ++ [(p.1.2.2.2.1,p.2.2.1)])) := by
  have hc : Computable (fun p : RawRun × RawInstruction => p.1.2.2) :=
    Computable.snd.comp (Computable.snd.comp Computable.fst)
  exact (Computable.fst.comp Computable.fst).pair
    ((Computable.fst.comp (Computable.snd.comp Computable.fst)).pair
      (computable_rawAdvanceState.comp (g := fun p : RawRun × RawInstruction => (p.1.2.2,p.2))
        (hc.pair Computable.snd)))

lemma computable_rawStep : Computable rawStep :=
  Computable.option_map computable_rawInstruction computable_rawAdvance.to₂

lemma computable_rawInit : Computable rawInit := by
  have hp : Computable (fun n : ℕ => (Encodable.decode (α := ℕ × List ℕ) n).getD (0,[])) :=
    Computable.option_getD Computable.decode (Computable.const _)
  have hm : Computable (fun n : ℕ =>
      (Encodable.decode (α := RawMachine) ((Encodable.decode (α := ℕ × List ℕ) n).getD (0,[])).1).getD (0,0,0,0,[])) :=
    Computable.option_getD (Computable.decode.comp (Computable.fst.comp hp)) (Computable.const _)
  exact hm.pair ((Computable.snd.comp hp).pair
    ((Computable.fst.comp (Computable.snd.comp (Computable.snd.comp hm))).pair
      ((Computable.const (0 : ℤ)).pair (Computable.const []))))

@[simp] lemma rawInit_inputCode (M : FiniteMachine) (w : Input M) :
    rawInit (inputCode M w) = (serialize M, w.map Fin.val, M.initial.val, 0, []) := by
  simp [rawInit, inputCode, FiniteMachine.code, serialize]

@[simp] lemma rawMove_number (d : Recorder.Direction) : rawMove d.number =
    match d with | .stay => 0 | .left => -1 | .right => 1 := by
  cases d <;> simp [rawMove, Recorder.Direction.number]

lemma rawBase_initial (M : FiniteMachine) (w : Input M) (z : ℤ) :
    rawBase M.blank.val (w.map Fin.val) z = ((initialConfiguration M w).tape z).val := by
  have hz : ((z.toNat : ℤ) = z) ↔ 0 ≤ z := by omega
  simp only [rawBase, initialConfiguration, hz]
  split_ifs with h
  · simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
    cases w[z.toNat]? <;> rfl
  · rfl

lemma rawRead_append (b : ℕ) (w : List ℕ) (s : List (ℤ × ℕ)) (z k : ℤ) (a : ℕ) :
    rawRead b w (s ++ [(k,a)]) z = if z = k then a else rawRead b w s z := by
  simp [rawRead, List.foldl_append]

lemma serialize_instruction (M : FiniteMachine) (q : Fin (M.states+1)) (a : Fin (M.symbols+1)) :
    (((serialize M).2.2.2.2.getD q.val []).getD a.val none) =
      (M.transition q a).map (fun v => (v.state.val, v.write.val, v.move.number)) := by
  have hq : q.val < (List.finRange (M.states+1)).length := by simpa using q.isLt
  have ha : a.val < (List.finRange (M.symbols+1)).length := by simpa using a.isLt
  simp [serialize, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hq,
    List.getElem?_eq_getElem ha]

def RawRel (M : FiniteMachine) (w : Input M) (c : TapeConfiguration M) (r : RawRun) : Prop :=
  r.1 = serialize M ∧ r.2.1 = w.map Fin.val ∧ r.2.2.1 = c.state.val ∧ r.2.2.2.1 = c.head ∧
    ∀ z, rawRead M.blank.val (w.map Fin.val) r.2.2.2.2 z = (c.tape z).val

lemma rawRel_initial (M : FiniteMachine) (w : Input M) :
    RawRel M w (initialConfiguration M w) (rawInit (inputCode M w)) := by
  rw [rawInit_inputCode]
  exact ⟨rfl,rfl,rfl,rfl, fun z => rawBase_initial M w z⟩

lemma rawStep_rel (M : FiniteMachine) (w : Input M) (c : TapeConfiguration M) (r : RawRun)
    (hr : RawRel M w c r) :
    match machineStep M c with
    | none => rawStep r = none
    | some c' => ∃ r', rawStep r = some r' ∧ RawRel M w c' r' := by
  rcases r with ⟨m,w',q,h,s⟩
  rcases hr with ⟨rfl,rfl,hq,hh,hs⟩
  dsimp at hq hh
  subst q; subst h
  have hi := serialize_instruction M c.state (c.tape c.head)
  dsimp only [rawStep]
  rw [show (serialize M).2.2.2.1 = M.blank.val from rfl, hs, hi]
  unfold machineStep
  cases hv : M.transition c.state (c.tape c.head) with
  | none => rfl
  | some v =>
    simp only [Option.map_some, rawMove_number]
    refine ⟨_, rfl, rfl, rfl, rfl, rfl, ?_⟩
    intro z
    rw [rawRead_append, hs]
    by_cases hz : z = c.head
    · subst z; simp
    · simp [hz]

lemma raw_respects (M : FiniteMachine) (w : Input M) :
    StateTransition.Respects (machineStep M) rawStep (RawRel M w) := by
  intro c r hr
  have h := rawStep_rel M w c r hr
  cases he : machineStep M c with
  | none => simpa [he] using h
  | some c' =>
    simp only [he] at h
    obtain ⟨r',hs,hr'⟩ := h
    exact ⟨r',hr', Relation.TransGen.single hs⟩

lemma halts_iff_eval_dom (M : FiniteMachine) (w : Input M) :
    Halts M w ↔ (StateTransition.eval (machineStep M) (initialConfiguration M w)).Dom := by
  rw [Part.dom_iff_mem]
  simp only [StateTransition.mem_eval]
  rfl

lemma raw_eval_dom (M : FiniteMachine) (w : Input M) :
    (StateTransition.eval rawStep (rawInit (inputCode M w))).Dom ↔ Halts M w := by
  exact (StateTransition.tr_eval_dom (raw_respects M w) (rawRel_initial M w)).trans
    (halts_iff_eval_dom M w).symm

lemma partrec_raw_eval : Partrec (StateTransition.eval rawStep) := by
  unfold StateTransition.eval
  apply Partrec.fix
  apply Computable.partrec
  exact (Computable.option_casesOn computable_rawStep Computable.sumInl
    (Computable.sumInr.comp Computable.snd).to₂).of_eq (fun r => by
      cases rawStep r <;> rfl)

def universalPartial (n : ℕ) : Part ℕ :=
  (StateTransition.eval rawStep (rawInit n)).map (fun _ => 0)

lemma universalPartial_partrec : Partrec universalPartial :=
  (partrec_raw_eval.comp computable_rawInit).map (Computable.const 0).to₂

lemma universalPartial_dom (M : FiniteMachine) (w : Input M) :
    (universalPartial (inputCode M w)).Dom ↔ Halts M w := raw_eval_dom M w

lemma exists_universal_code : ∃ c : Turing.ToPartrec.Code, ∀ n,
    (c.eval [n]).Dom ↔ (universalPartial n).Dom := by
  obtain ⟨c,hc⟩ := Turing.ToPartrec.Code.exists_code (Nat.Partrec'.part_iff₁.mpr universalPartial_partrec)
  refine ⟨c, fun n => ?_⟩
  have h := hc ⟨[n],rfl⟩
  simpa [List.Vector.head] using congrArg Part.Dom h

end BalancedTransport.Universal
end

end OAI
