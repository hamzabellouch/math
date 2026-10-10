import OAI.Computability.UniqueGames.Machines.MachineSubroutineLemmas
import OAI.Computability.UniqueGames.PCP.HonestTestLemmas
import OAI.Computability.UniqueGames.PCP.SourceContextLoad
import OAI.Computability.UniqueGames.PCP.SourceDescriptorEmissionLemmas
import OAI.Computability.UniqueGames.PCP.SourceOccurrences

namespace OAI

namespace UniqueGamesTheorem.Foundations.Hastad.SourceSignaturePrepare

open Turing
open Target PCP SourceContexts SourceOccurrences SourceLocalSignature SourceProfileBridge
open UniqueGamesTheorem.Foundations.Complexity

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

/-- Reassociate finite registers without adding a transition. -/
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

/-- The actual profile execution, placed in the loaded context arena. -/
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

/-- Actual preparation from isolated name fields and unary sign fields. The
conclusion preserves every tape and arbitrary caller metadata. -/
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
/-- Unary sign fields may retain arbitrary old suffixes: only the leading
sign bit is read. -/
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

/-- Exactly the loaded context signature is computed by the concrete finite
program. Scratch is reset and all loaded fields and caller tapes are preserved. -/
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

/-- Finiteness of tape addresses and registers constructs an actual TM2;
its execution bound is established above by the concrete transitions. -/
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

end UniqueGamesTheorem.Foundations.Hastad.SourceSignaturePrepare

namespace UniqueGamesTheorem.Foundations.Hastad.SourceContextPrepare

open Turing UniqueGamesTheorem.Foundations.Complexity
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

end UniqueGamesTheorem.Foundations.Hastad.SourceContextPrepare

/-! The actual numbered equation list has exactly the acceptance bounded by
the private Fourier decoder. Only the repeated base-game value is an input
here; list semantics and all finite sampling laws are supplied. -/
noncomputable section
namespace UniqueGamesTheorem.Foundations.Hastad.SourceSoundness

open scoped BigOperators
open Target SourceContexts SourceOccurrences SourceGame

def leftTable (F : Formula) (u : ℕ) (bits : Fin (nBits F u) → Bool)
    (v : VariableContext F u) : HalfCube (leftAnchor u) → Bool :=
  fun h => bits ((proofEncoding F u).code (.inl (v, h.val)))

def rightOracle (F : Formula) (u : ℕ) (bits : Fin (nBits F u) → Bool)
    (c : ClauseContext F u) : ConditionedOracle (validJ F c) :=
  match h : rightAnchor F c with
  | none => .empty ((rightAnchor_none_iff F c).mp h)
  | some j₀ => .stored j₀
      (fun h => bits ((proofEncoding F u).code
        (.inr (.inl (c, extendRestricted (validJ F c) h.val)))))

@[simp] theorem rightOracle_answer (F : Formula) (u : ℕ)
    (bits : Fin (nBits F u) → Bool) (c : ClauseContext F u) :
    (rightOracle F u bits c).answer = rightResponse F u bits c := by
  unfold rightOracle
  split <;> simp_all [rightResponse, ConditionedOracle.answer]

@[simp] theorem leftTable_answer (F : Formula) (u : ℕ)
    (bits : Fin (nBits F u) → Bool) (v : VariableContext F u) :
    foldedAnswer (leftAnchor u) (leftTable F u bits v) = leftResponse F u bits v := rfl

/-- Exact finite occurrence-list soundness, including arbitrary assignments
to unused padded proof bits and to the dummy bit. -/
theorem sourceList_sound (F : Formula) (hne : F.clauses ≠ []) (u D : ℕ)
    (hD : 0 < D) (hDtwo : 2 ≤ D) (δ : ℝ) (hδ : 0 ≤ δ)
    (hvalue : ((baseGame F hne).repetition u).value ≤
      4 * (D : ℝ)⁻¹ * δ ^ 2)
    (bits : Fin (nBits F u) → Bool) :
    ((sourceList F u D).countP (fun e => UniqueGamesTheorem.Reduction.CloneGap.satisfied e bits) : ℝ) /
      (sourceList F u D).length ≤ (1 + δ) / 2 := by
  rw [sourceList_nonempty F u D hne, rawSourceList_acceptance F u D hD]
  have hε : (0 : ℝ) < (D : ℝ)⁻¹ := inv_pos.mpr (Nat.cast_pos.mpr hD)
  have hε' : (D : ℝ)⁻¹ ≤ (1 : ℝ) / 2 := by
    have hd : (2 : ℝ) ≤ D := by exact_mod_cast hDtwo
    simpa only [one_div] using
      (inv_le_inv₀ (Nat.cast_pos.mpr hD) (by norm_num : (0 : ℝ) < 2)).mpr hd
  have h := source_acceptance_le_split F hne u ((D : ℝ)⁻¹) δ
    (fun _ => leftAnchor u) (leftTable F u bits) (rightOracle F u bits)
    hε hε' hδ hvalue
  simpa only [leftTable_answer, rightOracle_answer] using h

/-- The direct uniform reduction consumes rational occurrence fractions. -/
theorem sourceList_sound_rat (F : Formula) (hne : F.clauses ≠ []) (u D : ℕ)
    (hD : 0 < D) (hDtwo : 2 ≤ D) (δ : ℚ) (hδ : 0 ≤ δ)
    (hvalue : ((baseGame F hne).repetition u).value ≤
      4 * (D : ℝ)⁻¹ * (δ : ℝ) ^ 2)
    (bits : Fin (nBits F u) → Bool) :
    ((sourceList F u D).countP (fun e => UniqueGamesTheorem.Reduction.CloneGap.satisfied e bits) : ℚ) /
      (sourceList F u D).length ≤ (1 + δ) / 2 := by
  have h := sourceList_sound F hne u D hD hDtwo (δ : ℝ)
    (by exact_mod_cast hδ) hvalue bits
  apply (Rat.cast_le (K := ℝ)).mp
  push_cast
  exact h

end UniqueGamesTheorem.Foundations.Hastad.SourceSoundness

end

namespace UniqueGamesTheorem.Foundations.Hastad.SourceTestEmit

open Turing
open Target SourceContexts SourceOccurrences SourceLocalSignature SourceLocalEquation
open SourceAddressDescriptors SourceEquationEmit
open UniqueGamesTheorem.Reduction.CloneGap
open Complexity

abbrev Label (u D : ℕ) := Unit ⊕ (LocalInput u D × SourceEquationEmit.Label)
abbrev State (u D : ℕ) := LocalInput u D × Option Bool

def localEquation (u D : ℕ) (state : LocalInput u D) : Equation Descriptor :=
  mapEquation (descriptor u) (SourceLocalEquation.emit u D state)

def bodyLabel (u D : ℕ) (state : LocalInput u D) (label : SourceEquationEmit.Label) :
    Label u D := .inr (state, label)

variable {K : Type} [DecidableEq K]

def program (u D : ℕ) (sources : Fin 3 → K) (destination scratch : K)
    (exit : Option (Label u D)) :
    Label u D → TM2.Stmt (fun _ : K => Bool) (Label u D) (State u D)
  | .inl _ => .goto (fun state => bodyLabel u D state.1 .seed)
  | .inr (state, label) =>
      SourceEquationEmit.statement sources destination scratch (localEquation u D state)
        (bodyLabel u D state) exit label

/-- The table selector is one real transition; every subsequent copy/push
transition belongs to the same fixed program. -/
theorem testTrace (u D : ℕ) (sources : Fin 3 → K) (destination scratch : K)
    (sourceDestination : ∀ side, sources side ≠ destination)
    (sourceScratch : ∀ side, sources side ≠ scratch)
    (destinationScratch : destination ≠ scratch) (exit : Option (Label u D))
    (state : LocalInput u D) (base : K → List Bool) (values : Fin 3 → ℕ)
    (sourceWords : ∀ side, base (sources side) = encodeWord (values side))
    (scratchEmpty : base scratch = []) (register : Option Bool) :
    (MachineComposition.advance (TM2.step (program u D sources destination scratch exit)))^[
      SourceEquationEmit.steps values (localEquation u D state) + 1]
        (some ⟨some (.inl ()), (state, register), base⟩) =
      some ⟨exit, (state, none),
        prefixTapes destination base (words values (localEquation u D state))⟩ := by
  rw [Function.iterate_succ_apply]
  change (MachineComposition.advance (TM2.step (program u D sources destination scratch exit)))^[
    SourceEquationEmit.steps values (localEquation u D state)]
      (some ⟨some (bodyLabel u D state .seed), (state, register), base⟩) = _
  exact SourceEquationEmit.equationTrace sources destination scratch sourceDestination
    sourceScratch destinationScratch (localEquation u D state) (bodyLabel u D state) exit
    (program u D sources destination scratch exit) (fun _ => rfl)
    base values sourceWords scratchEmpty state register

def testInTime (u D : ℕ) (sources : Fin 3 → K) (destination scratch : K)
    (sourceDestination : ∀ side, sources side ≠ destination)
    (sourceScratch : ∀ side, sources side ≠ scratch)
    (destinationScratch : destination ≠ scratch) (exit : Option (Label u D))
    (state : LocalInput u D) (base : K → List Bool) (values : Fin 3 → ℕ)
    (sourceWords : ∀ side, base (sources side) = encodeWord (values side))
    (scratchEmpty : base scratch = []) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step (program u D sources destination scratch exit))
      ⟨some (.inl ()), (state, register), base⟩
      (some ⟨exit, (state, none),
        prefixTapes destination base (words values (localEquation u D state))⟩)
      (SourceEquationEmit.steps values (localEquation u D state) + 1) where
  steps := SourceEquationEmit.steps values (localEquation u D state) + 1
  evals_in_steps := testTrace u D sources destination scratch sourceDestination sourceScratch
    destinationScratch exit state base values sourceWords scratchEmpty register
  steps_le_m := Nat.le_refl _

def sourceTestInTime (F : Formula) (u D : ℕ) (p : SourceIndex F u D)
    (sources : Fin 3 → K) (destination scratch : K)
    (sourceDestination : ∀ side, sources side ≠ destination)
    (sourceScratch : ∀ side, sources side ≠ scratch)
    (destinationScratch : destination ≠ scratch) (exit : Option (Label u D))
    (base : K → List Bool)
    (sourceWords : ∀ side, base (sources side) = encodeWord
      (baseValue F u p.1.1 (sampledVariables F p.1.1 p.1.2) side))
    (scratchEmpty : base scratch = []) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step (program u D sources destination scratch exit))
      ⟨some (.inl ()), ((ofContext F p.1.1 p.1.2, p.2), register), base⟩
      (some ⟨exit, ((ofContext F p.1.1 p.1.2, p.2), none),
        prefixTapes destination base
          (UniqueGamesTheorem.Reduction.SourceEncoding.equationWords (sourceEquation F u D p))⟩)
      (6 * nBits F u + 17) where
  steps := SourceEquationEmit.steps
    (baseValue F u p.1.1 (sampledVariables F p.1.1 p.1.2))
    (localEquation u D (ofContext F p.1.1 p.1.2, p.2)) + 1
  evals_in_steps := by
    rw [sourceEquation_words]
    exact testTrace u D sources destination scratch sourceDestination sourceScratch
      destinationScratch exit (ofContext F p.1.1 p.1.2, p.2) base
      (baseValue F u p.1.1 (sampledVariables F p.1.1 p.1.2)) sourceWords scratchEmpty register
  steps_le_m := by
    have h := equation_emit_steps_le F u p.1.1 (sampledVariables F p.1.1 p.1.2)
      (localEquation u D (ofContext F p.1.1 p.1.2, p.2))
    change _ + 1 ≤ _
    unfold SourceEquationEmit.steps
    omega

end UniqueGamesTheorem.Foundations.Hastad.SourceTestEmit

namespace UniqueGamesTheorem.Foundations.Hastad.SourceTestAppend

open Turing Complexity
open Target SourceContexts SourceOccurrences SourceLocalSignature SourceLocalEquation
open SourceAddressDescriptors SourceEquationEmit SourceTestEmit

inductive Label (u D : Nat)
  | test (label : SourceTestEmit.Label u D)
  | append
  deriving DecidableEq, Fintype

abbrev State (u D : Nat) := SourceTestEmit.State u D

structure Layout (K : Type) where
  sources : Fin 3 → K
  temporary : K
  scratch : K
  accumulator : K
  sourceTemporary : ∀ side, sources side ≠ temporary
  sourceScratch : ∀ side, sources side ≠ scratch
  sourceAccumulator : ∀ side, sources side ≠ accumulator
  temporaryScratch : temporary ≠ scratch
  temporaryAccumulator : temporary ≠ accumulator
  scratchAccumulator : scratch ≠ accumulator

def equationBits (u D : Nat) (values : Fin 3 → Nat) (state : LocalInput u D) : List Bool :=
  encodeWords (words values (localEquation u D state))

def steps (u D : Nat) (values : Fin 3 → Nat) (state : LocalInput u D) : Nat :=
  SourceEquationEmit.steps values (localEquation u D state) + 1 +
    (equationBits u D values state).length + 1

variable {K Λ : Type} [DecidableEq K]

def bodyLabel (u D : Nat) (labels : Label u D → Λ) (state : LocalInput u D)
    (label : SourceEquationEmit.Label) : Λ :=
  labels (.test (SourceTestEmit.bodyLabel u D state label))

def statement (u D : Nat) (layout : Layout K) (labels : Label u D → Λ) (exit : Option Λ) :
    Label u D → TM2.Stmt (fun _ : K => Bool) Λ (State u D)
  | .test (.inl _) => .goto (fun state => bodyLabel u D labels state.1 .seed)
  | .test (.inr (state, label)) =>
      SourceEquationEmit.statement layout.sources layout.temporary layout.scratch
        (localEquation u D state) (bodyLabel u D labels state) (some (labels .append)) label
  | .append => Reduction.MachineTransfer.loopAt layout.temporary layout.accumulator id false
      (labels .append) exit

def program (u D : Nat) (layout : Layout K) (exit : Option (Label u D)) :
    Label u D → TM2.Stmt (fun _ : K => Bool) (Label u D) (State u D) :=
  statement u D layout id exit

def resultTapes (layout : Layout K) (base : K → List Bool) (bits : List Bool) : K → List Bool :=
  Function.update base layout.accumulator (bits.reverse ++ base layout.accumulator)

theorem resultTapes_other (layout : Layout K) (base : K → List Bool) (bits : List Bool)
    (k : K) (hk : k ≠ layout.accumulator) : resultTapes layout base bits k = base k := by
  simp [resultTapes, hk]

theorem resultTapes_source (layout : Layout K) (base : K → List Bool) (bits : List Bool)
    (side : Fin 3) : resultTapes layout base bits (layout.sources side) = base (layout.sources side) :=
  resultTapes_other layout base bits _ (layout.sourceAccumulator side)

theorem resultTapes_temporary (layout : Layout K) (base : K → List Bool) (bits : List Bool) :
    resultTapes layout base bits layout.temporary = base layout.temporary :=
  resultTapes_other layout base bits _ layout.temporaryAccumulator

theorem resultTapes_scratch (layout : Layout K) (base : K → List Bool) (bits : List Bool) :
    resultTapes layout base bits layout.scratch = base layout.scratch :=
  resultTapes_other layout base bits _ layout.scratchAccumulator

/-- Placement-aware finite selection plus actual equation emission. -/
theorem emitTrace (u D : Nat) (layout : Layout K) (labels : Label u D → Λ) (exit : Option Λ)
    (p : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State u D))
    (atLabels : ∀ label, p (labels label) = statement u D layout labels exit label)
    (state : LocalInput u D) (base : K → List Bool) (values : Fin 3 → Nat)
    (sourceWords : ∀ side, base (layout.sources side) = encodeWord (values side))
    (scratchEmpty : base layout.scratch = []) (register : Option Bool) :
    (MachineComposition.advance (TM2.step p))^[
      SourceEquationEmit.steps values (localEquation u D state) + 1]
      (some ⟨some (labels (.test (.inl ()))), (state, register), base⟩) =
      some ⟨some (labels .append), (state, none),
        prefixTapes layout.temporary base (words values (localEquation u D state))⟩ := by
  have select : TM2.step p
      ⟨some (labels (.test (.inl ()))), (state, register), base⟩ =
      some ⟨some (bodyLabel u D labels state .seed), (state, register), base⟩ := by
    change some (TM2.stepAux (p (labels (.test (.inl ())))) (state, register) base) = _
    rw [atLabels]
    rfl
  rw [Function.iterate_succ_apply]
  change (MachineComposition.advance (TM2.step p))^[
    SourceEquationEmit.steps values (localEquation u D state)]
      (TM2.step p ⟨some (labels (.test (.inl ()))), (state, register), base⟩) = _
  rw [select]
  exact SourceEquationEmit.equationTrace layout.sources layout.temporary layout.scratch
    layout.sourceTemporary layout.sourceScratch layout.temporaryScratch (localEquation u D state)
    (bodyLabel u D labels state) (some (labels .append)) p
    (fun label => atLabels (.test (SourceTestEmit.bodyLabel u D state label)))
    base values sourceWords scratchEmpty state register

/-- Exact one-record append trace in an arbitrary caller program. -/
theorem appendTrace (u D : Nat) (layout : Layout K) (labels : Label u D → Λ) (exit : Option Λ)
    (p : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State u D))
    (atLabels : ∀ label, p (labels label) = statement u D layout labels exit label)
    (state : LocalInput u D) (base : K → List Bool) (values : Fin 3 → Nat)
    (sourceWords : ∀ side, base (layout.sources side) = encodeWord (values side))
    (scratchEmpty : base layout.scratch = []) (temporaryEmpty : base layout.temporary = [])
    (register : Option Bool) :
    (MachineComposition.advance (TM2.step p))^[steps u D values state]
      (some ⟨some (labels (.test (.inl ()))), (state, register), base⟩) =
      some ⟨exit, (state, none), resultTapes layout base (equationBits u D values state)⟩ := by
  let emitted := prefixTapes layout.temporary base (words values (localEquation u D state))
  have hemit := emitTrace u D layout labels exit p atLabels state base values sourceWords
    scratchEmpty register
  have htemp : emitted layout.temporary = equationBits u D values state := by
    simp [emitted, prefixTapes, equationBits, temporaryEmpty]
  have hacc : emitted layout.accumulator = base layout.accumulator :=
    prefixTapes_other _ _ _ _ (Ne.symm layout.temporaryAccumulator)
  have hfinal : Reduction.MachineTransfer.tapesAt layout.temporary layout.accumulator emitted []
      ((equationBits u D values state).reverse ++ base layout.accumulator) =
      resultTapes layout base (equationBits u D values state) := by
    funext k
    by_cases hka : k = layout.accumulator
    · subst k
      simp [Reduction.MachineTransfer.tapesAt, resultTapes]
    · by_cases hkt : k = layout.temporary
      · subst k
        simp [Reduction.MachineTransfer.tapesAt, resultTapes, layout.temporaryAccumulator,
          temporaryEmpty]
      · simp [Reduction.MachineTransfer.tapesAt, resultTapes, emitted, prefixTapes, hka, hkt]
  have transferred := Reduction.MachineTransfer.transferAt_fromTapes
    (Γ := fun _ : K => Bool) (σ := LocalInput u D)
    layout.temporary layout.accumulator layout.temporaryAccumulator id false (labels .append)
    exit p (by simpa only [statement] using atLabels .append) emitted state none
  change (MachineComposition.advance (TM2.step p))^[(emitted layout.temporary).length + 1]
    (some ⟨some (labels .append), (state, none), emitted⟩) = _ at transferred
  rw [htemp, hacc] at transferred
  simp only [List.map_id] at transferred
  rw [hfinal] at transferred
  rw [show steps u D values state = ((equationBits u D values state).length + 1) +
      (SourceEquationEmit.steps values (localEquation u D state) + 1) by unfold steps; omega,
    Function.iterate_add_apply, hemit]
  exact transferred

def appendInTime (u D : Nat) (layout : Layout K) (labels : Label u D → Λ) (exit : Option Λ)
    (p : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State u D))
    (atLabels : ∀ label, p (labels label) = statement u D layout labels exit label)
    (state : LocalInput u D) (base : K → List Bool) (values : Fin 3 → Nat)
    (sourceWords : ∀ side, base (layout.sources side) = encodeWord (values side))
    (scratchEmpty : base layout.scratch = []) (temporaryEmpty : base layout.temporary = [])
    (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step p)
      ⟨some (labels (.test (.inl ()))), (state, register), base⟩
      (some ⟨exit, (state, none), resultTapes layout base (equationBits u D values state)⟩)
      (steps u D values state) where
  steps := steps u D values state
  evals_in_steps := appendTrace u D layout labels exit p atLabels state base values
    sourceWords scratchEmpty temporaryEmpty register
  steps_le_m := Nat.le_refl _

def programInTime (u D : Nat) (layout : Layout K) (exit : Option (Label u D))
    (state : LocalInput u D) (base : K → List Bool) (values : Fin 3 → Nat)
    (sourceWords : ∀ side, base (layout.sources side) = encodeWord (values side))
    (scratchEmpty : base layout.scratch = []) (temporaryEmpty : base layout.temporary = [])
    (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step (program u D layout exit))
      ⟨some (.test (.inl ())), (state, register), base⟩
      (some ⟨exit, (state, none), resultTapes layout base (equationBits u D values state)⟩)
      (steps u D values state) :=
  appendInTime u D layout id exit (program u D layout exit) (fun _ => rfl) state base values
    sourceWords scratchEmpty temporaryEmpty register

def sourceAppendInTime (F : Formula) (u D : Nat) (occurrence : SourceIndex F u D)
    (layout : Layout K) (labels : Label u D → Λ) (exit : Option Λ)
    (p : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State u D))
    (atLabels : ∀ label, p (labels label) = statement u D layout labels exit label)
    (base : K → List Bool)
    (sourceWords : ∀ side, base (layout.sources side) = encodeWord
      (baseValue F u occurrence.1.1 (sampledVariables F occurrence.1.1 occurrence.1.2) side))
    (scratchEmpty : base layout.scratch = []) (temporaryEmpty : base layout.temporary = [])
    (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step p)
      ⟨some (labels (.test (.inl ()))),
        ((ofContext F occurrence.1.1 occurrence.1.2, occurrence.2), register), base⟩
      (some ⟨exit, ((ofContext F occurrence.1.1 occurrence.1.2, occurrence.2), none),
        resultTapes layout base (encodeWords
          (UniqueGamesTheorem.Reduction.SourceEncoding.equationWords (sourceEquation F u D occurrence)))⟩)
      (9 * nBits F u + 20) where
  steps := steps u D
    (baseValue F u occurrence.1.1 (sampledVariables F occurrence.1.1 occurrence.1.2))
    (ofContext F occurrence.1.1 occurrence.1.2, occurrence.2)
  evals_in_steps := by
    rw [sourceEquation_words]
    exact appendTrace u D layout labels exit p atLabels
      (ofContext F occurrence.1.1 occurrence.1.2, occurrence.2) base
      (baseValue F u occurrence.1.1 (sampledVariables F occurrence.1.1 occurrence.1.2))
      sourceWords scratchEmpty temporaryEmpty register
  steps_le_m := by
    have he := equation_emit_steps_le F u occurrence.1.1
      (sampledVariables F occurrence.1.1 occurrence.1.2)
      (localEquation u D (ofContext F occurrence.1.1 occurrence.1.2, occurrence.2))
    have hl := UniqueGamesTheorem.Reduction.SourceEncoding.equationBits_length_le
      (sourceEquation F u D occurrence)
    rw [sourceEquation_words] at hl
    unfold steps SourceEquationEmit.steps equationBits
    dsimp only [localEquation] at he hl ⊢
    omega

abbrev Tape := Fin 3 ⊕ Fin 3

def standardLayout : Layout Tape where
  sources := Sum.inl
  temporary := .inr 0
  scratch := .inr 1
  accumulator := .inr 2
  sourceTemporary _ := Sum.inl_ne_inr
  sourceScratch _ := Sum.inl_ne_inr
  sourceAccumulator _ := Sum.inl_ne_inr
  temporaryScratch := by decide
  temporaryAccumulator := by decide
  scratchAccumulator := by decide

def machine (u D : Nat) (initial : LocalInput u D) : FinTM2 where
  K := Tape
  k₀ := .inl 0
  k₁ := .inr 2
  Γ _ := Bool
  Λ := Label u D
  main := .test (.inl ())
  σ := State u D
  initialState := (initial, none)
  m := program u D standardLayout none

def machineInTime (u D : Nat) (initial state : LocalInput u D)
    (base : Tape → List Bool) (values : Fin 3 → Nat)
    (sourceWords : ∀ side, base (.inl side) = encodeWord (values side))
    (scratchEmpty : base (.inr 1) = []) (temporaryEmpty : base (.inr 0) = [])
    (register : Option Bool) :
    StateTransition.EvalsToInTime (machine u D initial).step
      ⟨some (Label.test (.inl ())), (state, register), base⟩
      (some ⟨none, (state, none), resultTapes standardLayout base (equationBits u D values state)⟩)
      (steps u D values state) :=
  programInTime u D standardLayout none state base values sourceWords scratchEmpty temporaryEmpty register

end UniqueGamesTheorem.Foundations.Hastad.SourceTestAppend

end OAI
