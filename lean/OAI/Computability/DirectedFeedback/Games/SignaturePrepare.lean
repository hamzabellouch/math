import Mathlib
import OAI.Computability.DirectedFeedback.Encoding.Bounds

namespace OAI


namespace DFVSGames.Foundations.Hastad.SourceSignaturePrepare

open Turing
open Target PCP SourceContexts SourceOccurrences SourceLocalSignature SourceProfileBridge
open DFVSGames.Foundations.Complexity

abbrev Width (u : ℕ) := (positionEncoding u).size
abbrev Arena (u : ℕ) (Extra : Type) := SourceContextLoad.Tape u Extra
abbrev ProfileState (u : ℕ) := MachineCompare.State (MachineFieldProfile.Profile (Width u))
abbrev State (u : ℕ) (τ : Type) := ProfileState u × (Signature u × τ)
abbrev ProfileLabel (u : ℕ) := MachineFieldProfile.Label (MachineFieldProfile.allPairs (Width u))

inductive Label (u : ℕ)
  | profile (label : ProfileLabel u)
  | commit
  deriving DecidableEq, Fintype

variable {u : ℕ} {Extra τ : Type}

def variableField (p : Position u) : Arena u Extra :=
  SourceContextLoad.variableField p.1 (slotEncoding.code p.2)

def polarityField (p : Position u) : Arena u Extra :=
  SourceContextLoad.polarityField p.1 (slotEncoding.code p.2)

def place : MachineFieldProfile.Tape (Width u) → Arena u Extra
  | .inl i => variableField ((positionEncoding u).code.symm i)
  | .inr w => if w = 0 then .index else if w = 1 then .work else .scratch

def unplace : Arena u Extra → Option (MachineFieldProfile.Tape (Width u))
  | .index => some (.inr 0)
  | .work => some (.inr 1)
  | .scratch => some (.inr 2)
  | .field t s =>
    if s = 0 then some (.inl ((positionEncoding u).code (t, .first)))
    else if s = 2 then some (.inl ((positionEncoding u).code (t, .second)))
    else if s = 4 then some (.inl ((positionEncoding u).code (t, .third))) else none
  | _ => none

@[simp] theorem unplace_place (k : MachineFieldProfile.Tape (Width u)) :
    unplace (place (Extra := Extra) k) = some k := by
  cases k with
  | inl i =>
    obtain ⟨p, rfl⟩ := (positionEncoding u).code.surjective i
    rcases p with ⟨t, s⟩
    simp only [place, Equiv.symm_apply_apply]
    cases s <;> rfl
  | inr w =>
    obtain ⟨w, hw⟩ := w
    have h : w = 0 ∨ w = 1 ∨ w = 2 := by omega
    rcases h with rfl | rfl | rfl <;> rfl

theorem place_injective : Function.Injective (place (u := u) (Extra := Extra)) := by
  intro a b h
  have h' := congrArg unplace h
  simpa only [unplace_place, Option.some.injEq] using h'

theorem place_unplace (a : Arena u Extra) (k : MachineFieldProfile.Tape (Width u))
    (h : unplace a = some k) : place k = a := by
  cases a with
  | formula => simp [unplace] at h
  | index => cases Option.some.inj h; rfl
  | work => cases Option.some.inj h; rfl
  | scratch => cases Option.some.inj h; rfl
  | copyScratch => simp [unplace] at h
  | current t => simp [unplace] at h
  | remaining t => simp [unplace] at h
  | extra e => simp [unplace] at h
  | field t s =>
    by_cases h0 : s = 0
    · subst s
      simp only [unplace, ↓reduceIte] at h
      cases Option.some.inj h
      simp only [place, Equiv.symm_apply_apply]
      rfl
    · by_cases h2 : s = 2
      · subst s
        simp only [unplace, ↓reduceIte] at h
        cases Option.some.inj h
        simp only [place, Equiv.symm_apply_apply]
        rfl
      · by_cases h4 : s = 4
        · subst s
          simp only [unplace, ↓reduceIte] at h
          cases Option.some.inj h
          simp only [place, Equiv.symm_apply_apply]
          rfl
        · simp [unplace, h0, h2, h4] at h

def fill (base : Arena u Extra → List Bool)
    (localTapes : MachineFieldProfile.Tape (Width u) → List Bool) : Arena u Extra → List Bool :=
  fun a => match unplace a with
    | some k => localTapes k
    | none => base a

@[simp] theorem fill_place (base : Arena u Extra → List Bool)
    (localTapes : MachineFieldProfile.Tape (Width u) → List Bool)
    (k : MachineFieldProfile.Tape (Width u)) : fill base localTapes (place k) = localTapes k := by
  simp only [fill, unplace_place]

@[simp] theorem fill_self (base : Arena u Extra → List Bool) :
    fill base (base ∘ place) = base := by
  funext a
  cases h : unplace a with
  | none => simp only [fill, h]
  | some k =>
    simp only [fill, h, Function.comp_apply, place_unplace a k h]

theorem fill_frame (base : Arena u Extra → List Bool)
    (localTapes : MachineFieldProfile.Tape (Width u) → List Bool)
    (a : Arena u Extra) (h : unplace a = none) : fill base localTapes a = base a := by
  simp only [fill, h]

variable [DecidableEq Extra]

theorem fill_update (base : Arena u Extra → List Bool)
    (localTapes : MachineFieldProfile.Tape (Width u) → List Bool)
    (k : MachineFieldProfile.Tape (Width u)) (value : List Bool) :
    fill base (Function.update localTapes k value) =
      Function.update (fill base localTapes) (place k) value := by
  funext a
  cases hu : unplace a with
  | none =>
    have hne : a ≠ place k := by
      intro h
      rw [h, unplace_place] at hu
      contradiction
    simp only [fill, hu, Function.update_of_ne hne]
  | some j =>
    have ha := place_unplace a j hu
    rw [← ha]
    by_cases h : j = k
    · subst j
      simp only [fill_place]
      simp [Function.update]
    · have hne : place (Extra := Extra) j ≠ place k := fun h' => h (place_injective h')
      simp only [fill_place, Function.update_of_ne h, Function.update_of_ne hne]

def placedLabel : Option (ProfileLabel u) → Option (Label u)
  | none => some .commit
  | some l => some (.profile l)

def placedConfiguration (base : Arena u Extra → List Bool) (metadata : Signature u × τ)
    (c : TM2.Cfg (fun _ : MachineFieldProfile.Tape (Width u) => Bool)
      (ProfileLabel u) (ProfileState u)) :
    TM2.Cfg (fun _ : Arena u Extra => Bool) (Label u) (State u τ) :=
  ⟨placedLabel c.l, (c.var, metadata), fill base c.stk⟩

def placedStatement :
    TM2.Stmt (fun _ : MachineFieldProfile.Tape (Width u) => Bool)
      (ProfileLabel u) (ProfileState u) →
    TM2.Stmt (fun _ : Arena u Extra => Bool) (Label u) (State u τ)
  | .push k f next => .push (place k) (fun state => f state.1) (placedStatement next)
  | .peek k f next => .peek (place k) (fun state bit => (f state.1 bit, state.2))
      (placedStatement next)
  | .pop k f next => .pop (place k) (fun state bit => (f state.1 bit, state.2))
      (placedStatement next)
  | .load f next => .load (fun state => (f state.1, state.2)) (placedStatement next)
  | .branch f yes no => .branch (fun state => f state.1)
      (placedStatement yes) (placedStatement no)
  | .goto f => .goto (fun state => .profile (f state.1))
  | .halt => .goto (fun _ => .commit)

theorem placed_stepAux (base : Arena u Extra → List Bool) (metadata : Signature u × τ)
    (q : TM2.Stmt (fun _ : MachineFieldProfile.Tape (Width u) => Bool)
      (ProfileLabel u) (ProfileState u))
    (state : ProfileState u) (localTapes : MachineFieldProfile.Tape (Width u) → List Bool) :
    TM2.stepAux (placedStatement q) (state, metadata) (fill base localTapes) =
      placedConfiguration base metadata (TM2.stepAux q state localTapes) := by
  induction q generalizing state localTapes with
  | push k f next ih =>
    simp only [placedStatement, TM2.stepAux, fill_place]
    rw [← fill_update]
    exact ih state _
  | peek k f next ih =>
    simpa only [placedStatement, TM2.stepAux, fill_place] using
      ih (f state (localTapes k).head?) localTapes
  | pop k f next ih =>
    simp only [placedStatement, TM2.stepAux, fill_place]
    rw [← fill_update]
    exact ih (f state (localTapes k).head?) _
  | load f next ih =>
    simpa only [placedStatement, TM2.stepAux] using ih (f state) localTapes
  | branch f yes no ihYes ihNo =>
    cases h : f state
    · simpa only [placedStatement, TM2.stepAux, h, Bool.cond_false] using ihNo state localTapes
    · simpa only [placedStatement, TM2.stepAux, h, Bool.cond_true] using ihYes state localTapes
  | goto f => rfl
  | halt => rfl

def signStateEquiv (u : ℕ) (τ : Type) :
    SourceSignLoad.State u (ProfileState u × τ) ≃ State u τ where
  toFun x := (x.2.1, (x.1, x.2.2))
  invFun x := (x.2.1, (x.1, x.2.2))
  left_inv _ := rfl
  right_inv _ := rfl

def commitStatement : TM2.Stmt (fun _ : Arena u Extra => Bool) (Label u) (State u τ) :=
  .load (fun state =>
    (state.1, ({state.2.1 with sameName := reindexProfile u state.1.1}, state.2.2)))
    (MachineControl.statement id (signStateEquiv u τ)
      (SourceSignLoad.statement polarityField none))

def program : Label u → TM2.Stmt (fun _ : Arena u Extra => Bool) (Label u) (State u τ)
  | .profile label => placedStatement
      (MachineFieldProfile.profileProgram (MachineFieldProfile.allPairs (Width u)) label)
  | .commit => commitStatement

theorem placed_step (base : Arena u Extra → List Bool) (metadata : Signature u × τ)
    (a b : TM2.Cfg (fun _ : MachineFieldProfile.Tape (Width u) => Bool)
      (ProfileLabel u) (ProfileState u))
    (h : (MachineFieldProfile.profileMachine (Width u)).step a = some b) :
    TM2.step program (placedConfiguration base metadata a) =
      some (placedConfiguration base metadata b) := by
  rcases a with ⟨label, state, tapes⟩
  cases label with
  | none => cases h
  | some label =>
    change some (TM2.stepAux
      (MachineFieldProfile.profileProgram (MachineFieldProfile.allPairs (Width u)) label)
      state tapes) = some b at h
    cases Option.some.inj h
    change some (TM2.stepAux (placedStatement _) (state, metadata) (fill base tapes)) = _
    rw [placed_stepAux]

theorem stepAux_commit (work : ProfileState u) (initial : Signature u) (ambient : τ)
    (tapes : Arena u Extra → List Bool) :
    TM2.stepAux commitStatement (work, (initial, ambient)) tapes =
      ⟨none, (work, (⟨SourceSignLoad.readSigns polarityField tapes,
        reindexProfile u work.1, initial.selected⟩, ambient)), tapes⟩ := by
  change TM2.stepAux (MachineControl.statement id (signStateEquiv u τ)
    (SourceSignLoad.statement polarityField none))
      ((signStateEquiv u τ)
        ({initial with sameName := reindexProfile u work.1}, (work, ambient))) tapes = _
  rw [MachineControl.stepAux_simulation, SourceSignLoad.stepAux_statement]
  rfl

def profileInTime (tapes : Arena u Extra → List Bool)
    (hwork : ∀ w : Fin 3, tapes (place (.inr w)) = [])
    (initialProfile : MachineFieldProfile.Profile (Width u))
    (initial : Signature u) (ambient : τ) (L : ℕ)
    (hL : ∀ i, (tapes (place (.inl i))).length ≤ L) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (.profile (MachineFieldProfile.labelAt (MachineFieldProfile.allPairs (Width u)) 0 0)),
        (MachineFieldProfile.normalState initialProfile, (initial, ambient)), tapes⟩
      (some ⟨some .commit,
        (MachineFieldProfile.normalState
          (MachineFieldProfile.equalityProfile (fun i => tapes (place (.inl i)))),
          (initial, ambient)), tapes⟩)
      (Width u * Width u * (5 * L + 6) + 1) := by
  let run := MachineFieldProfile.profileInTime_bounded (Width u) (tapes ∘ place)
    hwork initialProfile L hL
  have lifted := MachineComposition.liftExecutionInTime _ _
    (placedConfiguration tapes (initial, ambient))
    (placed_step tapes (initial, ambient)) run
  simpa only [placedConfiguration, placedLabel, fill_self, Function.comp_apply] using lifted

def commitInTime (work : ProfileState u) (initial : Signature u) (ambient : τ)
    (tapes : Arena u Extra → List Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some .commit, (work, (initial, ambient)), tapes⟩
      (some ⟨none, (work, (⟨SourceSignLoad.readSigns polarityField tapes,
        reindexProfile u work.1, initial.selected⟩, ambient)), tapes⟩) 1 where
  steps := 1
  evals_in_steps := by
    change TM2.step program ⟨some .commit, (work, (initial, ambient)), tapes⟩ = _
    change some (TM2.stepAux commitStatement (work, (initial, ambient)) tapes) = _
    rw [stepAux_commit]
  steps_le_m := Nat.le_refl _

def prepareInTime (F : Formula) (c : ClauseContext F u) (selected : SlotContext u)
    (tapes : Arena u Extra → List Bool)
    (hwork : ∀ w : Fin 3, tapes (place (.inr w)) = [])
    (hnames : ∀ i, tapes (place (.inl i)) = nameWords F c i)
    (suffix : Position u → List Bool)
    (hsigns : ∀ p, tapes (polarityField p) =
      encodeWord (if positiveAt (clauseAt F (c p.1)) p.2 then 1 else 0) ++ suffix p)
    (initialProfile : MachineFieldProfile.Profile (Width u))
    (initial : Signature u) (hselected : initial.selected = selected) (ambient : τ) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (.profile (MachineFieldProfile.labelAt (MachineFieldProfile.allPairs (Width u)) 0 0)),
        (MachineFieldProfile.normalState initialProfile, (initial, ambient)), tapes⟩
      (some ⟨none,
        (MachineFieldProfile.normalState (MachineFieldProfile.equalityProfile (nameWords F c)),
          (ofContext F c selected, ambient)), tapes⟩)
      (Width u * Width u * (5 * (formulaBits F).length + 6) + 2) := by
  have hfields : (fun i => tapes (place (.inl i))) = nameWords F c := funext hnames
  have hsign : SourceSignLoad.readSigns polarityField tapes =
      fun p => positiveAt (clauseAt F (c p.1)) p.2 :=
    SourceSignLoad.readSigns_of_unary polarityField tapes _ suffix hsigns
  have hL : ∀ i, (tapes (place (.inl i))).length ≤ (formulaBits F).length := by
    intro i
    rw [hnames]
    exact nameWords_length_le_input F c i
  have first := profileInTime tapes hwork initialProfile initial ambient
    (formulaBits F).length hL
  rw [hfields] at first
  have last := commitInTime
    (MachineFieldProfile.normalState (MachineFieldProfile.equalityProfile (nameWords F c)))
    initial ambient tapes
  dsimp only [MachineFieldProfile.normalState] at last
  rw [hsign, hselected, prepared_signature_eq F c selected] at last
  let run := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ first last
  refine { toEvalsTo := run.toEvalsTo, steps_le_m := ?_ }
  have h := run.steps_le_m
  omega

omit [DecidableEq Extra] in

theorem loaded_name_field (F : Formula) (c : ClauseContext F u)
    (base : Arena u Extra → List Bool)
    (hbase : ∀ p : Position u, base (variableField p) = [])
    (i : Fin (Width u)) :
    SourceContextLoad.stageTapes F c base u (place (.inl i)) = nameWords F c i := by
  obtain ⟨p, rfl⟩ := (positionEncoding u).code.surjective i
  simp only [place, Equiv.symm_apply_apply]
  have ho := SourceContextLoad.output_variable F c base p.1 (slotEncoding.code p.2)
  change SourceContextLoad.stageTapes F c base u (variableField p) =
    encodeWord (F.clauses[(c p.1).val][(slotEncoding.code p.2).val].variableIndex.val) ++
      base (variableField p) at ho
  rw [ho, hbase p, List.append_nil]
  simp only [nameWords, names, Equiv.symm_apply_apply]
  rcases p with ⟨t, s⟩
  cases s <;> rfl

omit [DecidableEq Extra] in

theorem loaded_sign_field (F : Formula) (c : ClauseContext F u)
    (base : Arena u Extra → List Bool) (p : Position u) :
    SourceContextLoad.stageTapes F c base u (polarityField p) =
      encodeWord (if positiveAt (clauseAt F (c p.1)) p.2 then 1 else 0) ++
        base (polarityField p) := by
  have ho := SourceContextLoad.output_polarity F c base p.1 (slotEncoding.code p.2)
  change SourceContextLoad.stageTapes F c base u (polarityField p) =
    encodeWord (if F.clauses[(c p.1).val][(slotEncoding.code p.2).val].positive then 1 else 0) ++
      base (polarityField p) at ho
  rw [ho]
  rcases p with ⟨t, s⟩
  cases s <;> rfl

def loadedPrepareInTime (F : Formula) (c : ClauseContext F u) (selected : SlotContext u)
    (base : Arena u Extra → List Bool)
    (hindex : base .index = []) (hwork : base .work = []) (hscratch : base .scratch = [])
    (hbase : ∀ p : Position u, base (variableField p) = [])
    (initialProfile : MachineFieldProfile.Profile (Width u))
    (initial : Signature u) (hselected : initial.selected = selected) (ambient : τ) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (.profile (MachineFieldProfile.labelAt (MachineFieldProfile.allPairs (Width u)) 0 0)),
        (MachineFieldProfile.normalState initialProfile, (initial, ambient)),
        SourceContextLoad.stageTapes F c base u⟩
      (some ⟨none,
        (MachineFieldProfile.normalState (MachineFieldProfile.equalityProfile (nameWords F c)),
          (ofContext F c selected, ambient)), SourceContextLoad.stageTapes F c base u⟩)
      (Width u * Width u * (5 * (formulaBits F).length + 6) + 2) := by
  apply prepareInTime F c selected (SourceContextLoad.stageTapes F c base u) _
    (loaded_name_field F c base hbase) (fun p => base (polarityField p))
    (loaded_sign_field F c base) initialProfile initial hselected ambient
  intro w
  have hc := SourceContextLoad.stageTapes_clean F c base u hindex hwork
  have hs : SourceContextLoad.stageTapes F c base u .scratch = [] := by
    rw [SourceContextLoad.stageTapes_frame F c base u .scratch
      (by simp) (by simp) (by intros; simp)]
    exact hscratch
  obtain ⟨w, hw⟩ := w
  have h : w = 0 ∨ w = 1 ∨ w = 2 := by omega
  rcases h with rfl | rfl | rfl
  · exact hc.1
  · exact hc.2
  · exact hs

def machine (u : ℕ) (Extra τ : Type) [DecidableEq Extra] [Fintype Extra] [Fintype τ]
    (initialProfile : MachineFieldProfile.Profile (Width u))
    (initial : Signature u) (ambient : τ) : FinTM2 where
  K := Arena u Extra
  k₀ := .formula
  k₁ := .formula
  Γ _ := Bool
  Λ := Label u
  main := .profile (MachineFieldProfile.labelAt (MachineFieldProfile.allPairs (Width u)) 0 0)
  σ := State u τ
  initialState := (MachineFieldProfile.normalState initialProfile, (initial, ambient))
  m := program

end DFVSGames.Foundations.Hastad.SourceSignaturePrepare


namespace DFVSGames.Foundations.Complexity.MachineStateFrame

open Turing

variable {K Λ Λ' σ τ : Type} {Γ : K → Type}

def frameStatement : TM2.Stmt Γ Λ σ → TM2.Stmt Γ Λ (σ × τ)
  | .push k f next => .push k (fun state => f state.1) (frameStatement next)
  | .peek k f next => .peek k (fun state bit => (f state.1 bit, state.2))
      (frameStatement next)
  | .pop k f next => .pop k (fun state bit => (f state.1 bit, state.2))
      (frameStatement next)
  | .load f next => .load (fun state => (f state.1, state.2)) (frameStatement next)
  | .branch f yes no => .branch (fun state => f state.1)
      (frameStatement yes) (frameStatement no)
  | .goto f => .goto (fun state => f state.1)
  | .halt => .halt

def frameConfiguration (ambient : τ) (c : TM2.Cfg Γ Λ σ) : TM2.Cfg Γ Λ (σ × τ) :=
  ⟨c.l, (c.var, ambient), c.stk⟩

def frameProgram (source : Λ → TM2.Stmt Γ Λ σ) : Λ → TM2.Stmt Γ Λ (σ × τ) :=
  fun label => frameStatement (source label)

@[simp] theorem frameConfiguration_state (ambient : τ) (c : TM2.Cfg Γ Λ σ) :
    (frameConfiguration ambient c).var.1 = c.var := rfl

@[simp] theorem frameConfiguration_metadata (ambient : τ) (c : TM2.Cfg Γ Λ σ) :
    (frameConfiguration ambient c).var.2 = ambient := rfl

@[simp] theorem frameConfiguration_tapes (ambient : τ) (c : TM2.Cfg Γ Λ σ) :
    (frameConfiguration ambient c).stk = c.stk := rfl

theorem frameStatement_pushBound (q : TM2.Stmt Γ Λ σ) :
    Runtime.statementPushBound (frameStatement (τ := τ) q) = Runtime.statementPushBound q := by
  induction q <;> simp_all only [frameStatement, Runtime.statementPushBound]

def statement (labels : Λ → Λ') (exit : Option Λ') (q : TM2.Stmt Γ Λ σ) :
    TM2.Stmt Γ Λ' (σ × τ) :=
  MachineSubroutine.statement labels exit (frameStatement q)

def configuration (labels : Λ → Λ') (exit : Option Λ') (ambient : τ)
    (c : TM2.Cfg Γ Λ σ) : TM2.Cfg Γ Λ' (σ × τ) :=
  MachineSubroutine.configuration labels exit (frameConfiguration ambient c)

@[simp] theorem configuration_state (labels : Λ → Λ') (exit : Option Λ')
    (ambient : τ) (c : TM2.Cfg Γ Λ σ) :
    (configuration labels exit ambient c).var.1 = c.var := rfl

@[simp] theorem configuration_metadata (labels : Λ → Λ') (exit : Option Λ')
    (ambient : τ) (c : TM2.Cfg Γ Λ σ) :
    (configuration labels exit ambient c).var.2 = ambient := rfl

@[simp] theorem configuration_tapes (labels : Λ → Λ') (exit : Option Λ')
    (ambient : τ) (c : TM2.Cfg Γ Λ σ) :
    (configuration labels exit ambient c).stk = c.stk := rfl

theorem statement_pushBound (labels : Λ → Λ') (exit : Option Λ')
    (q : TM2.Stmt Γ Λ σ) :
    Runtime.statementPushBound (statement (τ := τ) labels exit q) =
      Runtime.statementPushBound q := by
  induction q <;> simp_all only [statement, frameStatement,
    MachineSubroutine.statement, Runtime.statementPushBound]
  cases exit <;> rfl

variable [DecidableEq K]

theorem frame_stepAux (q : TM2.Stmt Γ Λ σ) (state : σ) (ambient : τ)
    (tapes : ∀ k, List (Γ k)) :
    TM2.stepAux (frameStatement q) (state, ambient) tapes =
      frameConfiguration ambient (TM2.stepAux q state tapes) := by
  induction q generalizing state tapes with
  | push k f next ih =>
    simpa only [frameStatement, TM2.stepAux] using
      ih state (Function.update tapes k (f state :: tapes k))
  | peek k f next ih =>
    simpa only [frameStatement, TM2.stepAux] using ih (f state (tapes k).head?) tapes
  | pop k f next ih =>
    simpa only [frameStatement, TM2.stepAux] using
      ih (f state (tapes k).head?) (Function.update tapes k (tapes k).tail)
  | load f next ih => simpa only [frameStatement, TM2.stepAux] using ih (f state) tapes
  | branch f yes no ihYes ihNo =>
    cases h : f state with
    | false => simpa only [frameStatement, TM2.stepAux, h, Bool.cond_false] using ihNo state tapes
    | true => simpa only [frameStatement, TM2.stepAux, h, Bool.cond_true] using ihYes state tapes
  | goto f => rfl
  | halt => rfl

theorem frame_step (source : Λ → TM2.Stmt Γ Λ σ) (ambient : τ)
    (c : TM2.Cfg Γ Λ σ) :
    TM2.step (frameProgram source) (frameConfiguration ambient c) =
      (TM2.step source c).map (frameConfiguration ambient) := by
  rcases c with ⟨label, state, tapes⟩
  cases label with
  | none => rfl
  | some label =>
    change some (TM2.stepAux (frameStatement (source label)) (state, ambient) tapes) = _
    rw [frame_stepAux]
    rfl

theorem frame_advance (source : Λ → TM2.Stmt Γ Λ σ) (ambient : τ)
    (c : Option (TM2.Cfg Γ Λ σ)) :
    MachineComposition.advance (TM2.step (frameProgram source))
        (c.map (frameConfiguration ambient)) =
      (MachineComposition.advance (TM2.step source) c).map (frameConfiguration ambient) := by
  cases c with
  | none => rfl
  | some c => exact frame_step source ambient c

theorem frame_iterate (source : Λ → TM2.Stmt Γ Λ σ) (ambient : τ)
    (steps : ℕ) (c : Option (TM2.Cfg Γ Λ σ)) :
    (MachineComposition.advance (TM2.step (frameProgram source)))^[steps]
        (c.map (frameConfiguration ambient)) =
      ((MachineComposition.advance (TM2.step source))^[steps] c).map
        (frameConfiguration ambient) := by
  induction steps with
  | zero => rfl
  | succ steps ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
    exact frame_advance source ambient _

def frameExecution (source : Λ → TM2.Stmt Γ Λ σ) (ambient : τ)
    {start : TM2.Cfg Γ Λ σ} {finish : Option (TM2.Cfg Γ Λ σ)} {budget : ℕ}
    (run : StateTransition.EvalsToInTime (TM2.step source) start finish budget) :
    StateTransition.EvalsToInTime (TM2.step (frameProgram source))
      (frameConfiguration ambient start) (finish.map (frameConfiguration ambient)) budget where
  steps := run.steps
  evals_in_steps := by
    have h := run.evals_in_steps
    change (MachineComposition.advance (TM2.step source))^[run.steps] (some start) = finish at h
    change (MachineComposition.advance (TM2.step (frameProgram source)))^[run.steps]
      ((some start).map (frameConfiguration ambient)) = finish.map (frameConfiguration ambient)
    rw [frame_iterate, h]
  steps_le_m := run.steps_le_m

@[simp] theorem frameExecution_steps (source : Λ → TM2.Stmt Γ Λ σ) (ambient : τ)
    {start : TM2.Cfg Γ Λ σ} {finish : Option (TM2.Cfg Γ Λ σ)} {budget : ℕ}
    (run : StateTransition.EvalsToInTime (TM2.step source) start finish budget) :
    (frameExecution source ambient run).steps = run.steps := rfl

theorem stepAux_simulation (labels : Λ → Λ') (exit : Option Λ')
    (q : TM2.Stmt Γ Λ σ) (state : σ) (ambient : τ) (tapes : ∀ k, List (Γ k)) :
    TM2.stepAux (statement labels exit q) (state, ambient) tapes =
      configuration labels exit ambient (TM2.stepAux q state tapes) := by
  rw [statement, MachineSubroutine.stepAux_simulation, frame_stepAux]
  rfl

theorem step_simulation (labels : Λ → Λ') (exit : Option Λ') (ambient : τ)
    (source : Λ → TM2.Stmt Γ Λ σ) (target : Λ' → TM2.Stmt Γ Λ' (σ × τ))
    (atLabels : ∀ l, target (labels l) = statement labels exit (source l))
    (a b : TM2.Cfg Γ Λ σ) (h : TM2.step source a = some b) :
    TM2.step target (configuration labels exit ambient a) =
      some (configuration labels exit ambient b) := by
  have framed : TM2.step (frameProgram source) (frameConfiguration ambient a) =
      some (frameConfiguration ambient b) := by
    rw [frame_step, h]
    rfl
  exact MachineSubroutine.step_simulation labels exit (frameProgram source) target
    atLabels _ _ framed

theorem trace (labels : Λ → Λ') (exit : Option Λ') (ambient : τ)
    (source : Λ → TM2.Stmt Γ Λ σ) (target : Λ' → TM2.Stmt Γ Λ' (σ × τ))
    (atLabels : ∀ l, target (labels l) = statement labels exit (source l))
    (steps : ℕ) (a b : TM2.Cfg Γ Λ σ)
    (run : (MachineComposition.advance (TM2.step source))^[steps] (some a) = some b) :
    (MachineComposition.advance (TM2.step target))^[steps]
      (some (configuration labels exit ambient a)) = some (configuration labels exit ambient b) :=
  MachineComposition.liftSuccessfulTrace (TM2.step source) (TM2.step target)
    (configuration labels exit ambient) (step_simulation labels exit ambient source target atLabels)
    steps a b run

def execution (labels : Λ → Λ') (exit : Option Λ') (ambient : τ)
    (source : Λ → TM2.Stmt Γ Λ σ) (target : Λ' → TM2.Stmt Γ Λ' (σ × τ))
    (atLabels : ∀ l, target (labels l) = statement labels exit (source l))
    {a b : TM2.Cfg Γ Λ σ} {budget : ℕ}
    (run : StateTransition.EvalsToInTime (TM2.step source) a (some b) budget) :
    StateTransition.EvalsToInTime (TM2.step target)
      (configuration labels exit ambient a) (some (configuration labels exit ambient b)) budget :=
  MachineComposition.liftExecutionInTime (TM2.step source) (TM2.step target)
    (configuration labels exit ambient) (step_simulation labels exit ambient source target atLabels) run

@[simp] theorem execution_steps (labels : Λ → Λ') (exit : Option Λ') (ambient : τ)
    (source : Λ → TM2.Stmt Γ Λ σ) (target : Λ' → TM2.Stmt Γ Λ' (σ × τ))
    (atLabels : ∀ l, target (labels l) = statement labels exit (source l))
    {a b : TM2.Cfg Γ Λ σ} {budget : ℕ}
    (run : StateTransition.EvalsToInTime (TM2.step source) a (some b) budget) :
    (execution labels exit ambient source target atLabels run).steps = run.steps := rfl

end DFVSGames.Foundations.Complexity.MachineStateFrame


namespace DFVSGames.Foundations.Hastad.SourceContextPrepare

open Turing DFVSGames.Foundations.Complexity
open Target PCP SourceContexts SourceOccurrences SourceLocalSignature SourceProfileBridge

abbrev Arena (u : Nat) (Extra : Type) := SourceContextLoad.Tape u Extra
abbrev LoadState := Unit × Option Bool
abbrev PrepareState (u : Nat) (τ : Type) := SourceSignaturePrepare.State u τ
abbrev State (u : Nat) (τ : Type) := LoadState × PrepareState u τ
abbrev Label (u : Nat) := SourceContextLoad.Label u ⊕ SourceSignaturePrepare.Label u

variable {u : Nat} {Extra τ : Type}

def prepareEntry (u : Nat) : SourceSignaturePrepare.Label u :=
  .profile (MachineFieldProfile.labelAt
    (MachineFieldProfile.allPairs (SourceSignaturePrepare.Width u)) 0 0)

def stateSwap (u : Nat) (τ : Type) : PrepareState u τ × LoadState ≃ State u τ :=
  Equiv.prodComm _ _

def program : Label u → TM2.Stmt (fun _ : Arena u Extra => Bool) (Label u) (State u τ)
  | .inl l => MachineStateFrame.statement Sum.inl (some (.inr (prepareEntry u)))
      (SourceContextLoad.program l)
  | .inr l => MachineControl.statement id (stateSwap u τ)
      (MachineStateFrame.statement Sum.inr none (SourceSignaturePrepare.program l))

def preparationConfiguration (loaderState : LoadState)
    (c : TM2.Cfg (fun _ : Arena u Extra => Bool) (SourceSignaturePrepare.Label u) (PrepareState u τ)) :
    TM2.Cfg (fun _ : Arena u Extra => Bool) (Label u) (State u τ) :=
  MachineControl.configuration id (stateSwap u τ)
    (MachineStateFrame.configuration Sum.inr none loaderState c)

variable [DecidableEq Extra]

theorem preparation_step (loaderState : LoadState)
    (a b : TM2.Cfg (fun _ : Arena u Extra => Bool)
      (SourceSignaturePrepare.Label u) (PrepareState u τ))
    (h : TM2.step SourceSignaturePrepare.program a = some b) :
    TM2.step program (preparationConfiguration loaderState a) =
      some (preparationConfiguration loaderState b) := by
  rcases a with ⟨label, state, tapes⟩
  cases label with
  | none => cases h
  | some l =>
    change some (TM2.stepAux (SourceSignaturePrepare.program l) state tapes) = some b at h
    cases Option.some.inj h
    change some (TM2.stepAux
      (MachineControl.statement id (stateSwap u τ)
        (MachineStateFrame.statement Sum.inr none (SourceSignaturePrepare.program l)))
      ((stateSwap u τ) (state, loaderState)) tapes) = _
    rw [MachineControl.stepAux_simulation, MachineStateFrame.stepAux_simulation]
    rfl

def initialState (initialProfile : MachineFieldProfile.Profile (SourceSignaturePrepare.Width u))
    (initial : Signature u) (ambient : τ) : State u τ :=
  (((), none), (MachineFieldProfile.normalState initialProfile, (initial, ambient)))

def finalState (F : Formula) (c : ClauseContext F u) (selected : SlotContext u)
    (ambient : τ) : State u τ :=
  (((), none), (MachineFieldProfile.normalState (MachineFieldProfile.equalityProfile (nameWords F c)),
    (ofContext F c selected, ambient)))

noncomputable def loadInTime (F : Formula) (c : ClauseContext F u)
    (base : Arena u Extra → List Bool)
    (hformula : base .formula = formulaBits F)
    (hcurrent : ∀ j, base (.current j) = encodeWord (c j).val)
    (hindex : base .index = []) (hwork : base .work = [])
    (hscratch : base .scratch = []) (hcopy : base .copyScratch = [])
    (initialProfile : MachineFieldProfile.Profile (SourceSignaturePrepare.Width u))
    (initial : Signature u) (ambient : τ) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (.inl (SourceContextLoad.labelAt 0)), initialState initialProfile initial ambient, base⟩
      (some ⟨some (.inr (prepareEntry u)), initialState initialProfile initial ambient,
        SourceContextLoad.stageTapes F c base u⟩)
      (u * (10 * (formulaBits F).length + 20) + 1) := by
  have run := SourceContextLoad.loadUnaryInTime F c base hformula hcurrent
    hindex hwork hscratch hcopy
  have lifted := MachineStateFrame.execution Sum.inl (some (.inr (prepareEntry u)))
    (MachineFieldProfile.normalState initialProfile, (initial, ambient))
    SourceContextLoad.program program (fun _ => rfl) run
  simpa only [MachineStateFrame.configuration, MachineStateFrame.frameConfiguration,
    MachineSubroutine.configuration, MachineSubroutine.label, initialState] using lifted

def signatureInTime (F : Formula) (c : ClauseContext F u) (selected : SlotContext u)
    (base : Arena u Extra → List Bool)
    (hindex : base .index = []) (hwork : base .work = []) (hscratch : base .scratch = [])
    (hfields : ∀ p : Position u, base (SourceSignaturePrepare.variableField p) = [])
    (initialProfile : MachineFieldProfile.Profile (SourceSignaturePrepare.Width u))
    (initial : Signature u) (hselected : initial.selected = selected) (ambient : τ) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (.inr (prepareEntry u)), initialState initialProfile initial ambient,
        SourceContextLoad.stageTapes F c base u⟩
      (some ⟨none, finalState F c selected ambient, SourceContextLoad.stageTapes F c base u⟩)
      (SourceSignaturePrepare.Width u * SourceSignaturePrepare.Width u *
        (5 * (formulaBits F).length + 6) + 2) := by
  have run := SourceSignaturePrepare.loadedPrepareInTime F c selected base
    hindex hwork hscratch hfields initialProfile initial hselected ambient
  have lifted := MachineComposition.liftExecutionInTime
    (TM2.step SourceSignaturePrepare.program) (TM2.step program)
    (preparationConfiguration ((), none)) (preparation_step ((), none)) run
  simpa only [preparationConfiguration, MachineControl.configuration, MachineStateFrame.configuration,
    MachineStateFrame.frameConfiguration, MachineSubroutine.configuration,
    MachineSubroutine.label, Option.map_some, Option.map_none, id_eq, stateSwap,
    Equiv.prodComm_apply, Prod.swap, initialState, finalState, prepareEntry] using lifted

noncomputable def prepareInTime (F : Formula) (c : ClauseContext F u) (selected : SlotContext u)
    (base : Arena u Extra → List Bool)
    (hformula : base .formula = formulaBits F)
    (hcurrent : ∀ j, base (.current j) = encodeWord (c j).val)
    (hindex : base .index = []) (hwork : base .work = [])
    (hscratch : base .scratch = []) (hcopy : base .copyScratch = [])
    (hfields : ∀ p : Position u, base (SourceSignaturePrepare.variableField p) = [])
    (initialProfile : MachineFieldProfile.Profile (SourceSignaturePrepare.Width u))
    (initial : Signature u) (hselected : initial.selected = selected) (ambient : τ) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (.inl (SourceContextLoad.labelAt 0)), initialState initialProfile initial ambient, base⟩
      (some ⟨none, finalState F c selected ambient, SourceContextLoad.stageTapes F c base u⟩)
      ((u * (10 * (formulaBits F).length + 20) + 1) +
        (SourceSignaturePrepare.Width u * SourceSignaturePrepare.Width u *
          (5 * (formulaBits F).length + 6) + 2)) := by
  have firstRun := loadInTime F c base hformula hcurrent hindex hwork hscratch hcopy
    initialProfile initial ambient
  have secondRun := signatureInTime F c selected base hindex hwork hscratch hfields
    initialProfile initial hselected ambient
  simpa only [Nat.add_comm] using
    StateTransition.EvalsToInTime.trans (TM2.step program) _ _ _ _ _ firstRun secondRun

def machine (u : Nat) (Extra τ : Type) [DecidableEq Extra] [Fintype Extra] [Fintype τ]
    (initialProfile : MachineFieldProfile.Profile (SourceSignaturePrepare.Width u))
    (initial : Signature u) (ambient : τ) : FinTM2 where
  K := Arena u Extra
  k₀ := .formula
  k₁ := .formula
  Γ _ := Bool
  Λ := Label u
  main := .inl (SourceContextLoad.labelAt 0)
  σ := State u τ
  initialState := initialState initialProfile initial ambient
  m := program

end DFVSGames.Foundations.Hastad.SourceContextPrepare

end OAI
