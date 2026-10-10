import OAI.Computability.DepthThree.MachineBasic
import Mathlib.Data.Fintype.Sets

namespace OAI

namespace DepthThreeLowerBound
namespace MachineFiniteRestriction

open Turing

variable {Γ Λ : Type} [instInhabitedΓ : Inhabited Γ] [Inhabited Λ]

def Label (M : TM0.Machine Γ Λ) (S : Finset Λ)
    (_hs : TM0.Supports M (S : Set Λ)) :=
  {q : Λ // q ∈ S}

variable (M : TM0.Machine Γ Λ) (S : Finset Λ)
variable (hs : TM0.Supports M (S : Set Λ))

instance labelInhabited : Inhabited (Label M S hs) :=
  ⟨⟨default, hs.1⟩⟩

instance labelFintype : Fintype (Label M S hs) :=
  inferInstanceAs (Fintype {q : Λ // q ∈ S})

noncomputable def retract (q : Λ) : Label M S hs := by
  classical
  exact if hq : q ∈ S then ⟨q, hq⟩ else default

theorem retract_val
    {Γ : Type}
    {Λ : Type}
    [Inhabited Γ]
    [Inhabited Λ]
    (M : Turing.TM0.Machine Γ Λ)
    (S : Finset Λ)
    (hs : Turing.TM0.Supports M ↑S)
    (q : Λ) (hq : q ∈ S) :
    (retract M S hs q).val = q := by
  classical
  have hr : retract M S hs q = (⟨q, hq⟩ : Label M S hs) := by
    unfold retract
    exact dite_eq_left hq
  exact congrArg Subtype.val hr

@[simp] theorem retract_default :
    retract M S hs default = (default : Label M S hs) := by
  apply Subtype.ext
  exact retract_val M S hs default hs.1

private def idAlphabet : PointedMap Γ Γ := ⟨id, rfl⟩

private theorem listBlank_map_id (l : ListBlank Γ) :
    l.map (idAlphabet (Γ := Γ)) = l := by
  apply ListBlank.ext
  intro n
  rw [ListBlank.nth_map]
  rfl

private theorem tape_map_id (t : Tape Γ) :
    t.map (idAlphabet (Γ := Γ)) = t := by
  cases t with
  | mk a l r =>
    change Tape.mk a (l.map (idAlphabet (Γ := Γ))) (r.map (idAlphabet (Γ := Γ))) =
      Tape.mk a l r
    rw [listBlank_map_id, listBlank_map_id]

noncomputable def restrict : TM0.Machine Γ (Label M S hs) :=
  M.map idAlphabet idAlphabet (retract M S hs) Subtype.val

noncomputable def restrictCfg (c : TM0.Cfg Γ Λ) : TM0.Cfg Γ (Label M S hs) :=
  ⟨retract M S hs c.q, c.Tape⟩

def includeCfg (c : TM0.Cfg Γ (Label M S hs)) : TM0.Cfg Γ Λ :=
  ⟨c.q.val, c.Tape⟩

theorem include_restrict (c : TM0.Cfg Γ Λ) (hc : c.q ∈ S) :
    includeCfg M S hs (restrictCfg M S hs c) = c := by
  cases c with
  | mk q t =>
    exact congrArg (fun q => TM0.Cfg.mk q t) (retract_val M S hs q hc)

@[simp] theorem restrict_include (c : TM0.Cfg Γ (Label M S hs)) :
    restrictCfg M S hs (includeCfg M S hs c) = c := by
  cases c with
  | mk q t =>
    have hq : retract M S hs q.val = q :=
      Subtype.ext (retract_val M S hs q.val q.property)
    exact congrArg (fun q => TM0.Cfg.mk q t) hq

theorem includeCfg_injective : Function.Injective (includeCfg M S hs) := by
  intro a b h
  have h' := congrArg (restrictCfg M S hs) h
  simpa only [restrict_include] using h'

private theorem cfg_map_eq (c : TM0.Cfg Γ Λ) :
    TM0.Cfg.map idAlphabet (retract M S hs) c = restrictCfg M S hs c := by
  cases c with
  | mk q t =>
    change TM0.Cfg.mk (retract M S hs q) (t.map idAlphabet) =
      TM0.Cfg.mk (retract M S hs q) t
    rw [tape_map_id]

theorem restrict_step (c : TM0.Cfg Γ Λ) (hc : c.q ∈ S) :
    (TM0.step M c).map (restrictCfg M S hs) =
      TM0.step (restrict M S hs) (restrictCfg M S hs c) := by
  have h := M.map_step idAlphabet idAlphabet (retract M S hs) Subtype.val
    (S := (S : Set Λ)) (by intro a; rfl)
    (fun q hq => retract_val M S hs q hq) c hc
  have hm : TM0.Cfg.map idAlphabet (retract M S hs) = restrictCfg M S hs :=
    funext (cfg_map_eq M S hs)
  rw [hm] at h
  exact h

theorem include_step (c : TM0.Cfg Γ (Label M S hs)) :
    (TM0.step (restrict M S hs) c).map (includeCfg M S hs) =
      TM0.step M (includeCfg M S hs c) := by
  have h := restrict_step M S hs (includeCfg M S hs c) c.q.property
  rw [restrict_include] at h
  rw [← h]
  cases he : TM0.step M (includeCfg M S hs c) with
  | none => rfl
  | some d =>
    have hd : d.q ∈ S := TM0.step_supports M hs he c.q.property
    exact congrArg some (include_restrict M S hs d hd)

@[simp] theorem restrict_init (l : List Γ) :
    restrictCfg M S hs (TM0.init l) = TM0.init l := by
  exact congrArg (fun q => TM0.Cfg.mk q (Tape.mk₁ l)) (retract_default M S hs)

@[simp] theorem include_init (l : List Γ) :
    includeCfg M S hs (TM0.init l) = TM0.init l := rfl

theorem include_runSteps (n : ℕ) (c : Option (TM0.Cfg Γ (Label M S hs))) :
    (runSteps (TM0.step (restrict M S hs)) n c).map (includeCfg M S hs) =
      runSteps (TM0.step M) n (c.map (includeCfg M S hs)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [runSteps_succ, runSteps_succ, ← ih]
    cases runSteps (TM0.step (restrict M S hs)) n c with
    | none => rfl
    | some d => exact include_step M S hs d

theorem restrict_runSteps (n : ℕ) (c : TM0.Cfg Γ Λ) (hc : c.q ∈ S) :
    (runSteps (TM0.step M) n (some c)).map (restrictCfg M S hs) =
      runSteps (TM0.step (restrict M S hs)) n (some (restrictCfg M S hs c)) := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
    rw [runSteps_succ_left, runSteps_succ_left]
    change (runSteps (TM0.step M) n (TM0.step M c)).map (restrictCfg M S hs) =
      runSteps (TM0.step (restrict M S hs)) n
        (TM0.step (restrict M S hs) (restrictCfg M S hs c))
    rw [← restrict_step M S hs c hc]
    cases he : TM0.step M c with
    | none => simp only [Option.map_none, runSteps_none]
    | some d => exact ih d (TM0.step_supports M hs he hc)

include hs in

theorem runSteps_supports (n : ℕ) (c : TM0.Cfg Γ Λ) (hc : c.q ∈ S)
    {d : TM0.Cfg Γ Λ} (hrun : runSteps (TM0.step M) n (some c) = some d) :
    d.q ∈ S := by
  induction n generalizing c with
  | zero =>
    have hcd : c = d := Option.some.inj hrun
    cases hcd
    exact hc
  | succ n ih =>
    rw [runSteps_succ_left] at hrun
    change runSteps (TM0.step M) n (TM0.step M c) = some d at hrun
    cases he : TM0.step M c with
    | none =>
      rw [he, runSteps_none] at hrun
      cases hrun
    | some e =>
      rw [he] at hrun
      exact ih e (TM0.step_supports M hs he hc) hrun

theorem restrict_runsIn {a b : TM0.Cfg Γ Λ} {bound : ℕ} (ha : a.q ∈ S)
    (h : RunsIn (TM0.step M) a b bound) :
    RunsIn (TM0.step (restrict M S hs))
      (restrictCfg M S hs a) (restrictCfg M S hs b) bound := by
  obtain ⟨n, hn, he⟩ := h
  refine ⟨n, hn, ?_⟩
  rw [← restrict_runSteps M S hs n a ha, he]
  rfl

theorem include_runsIn_iff (a b : TM0.Cfg Γ (Label M S hs)) (bound : ℕ) :
    RunsIn (TM0.step M) (includeCfg M S hs a) (includeCfg M S hs b) bound ↔
      RunsIn (TM0.step (restrict M S hs)) a b bound := by
  constructor
  · rintro ⟨n, hn, he⟩
    refine ⟨n, hn, ?_⟩
    apply Option.map_injective (includeCfg_injective M S hs)
    rw [include_runSteps]
    exact he
  · rintro ⟨n, hn, he⟩
    refine ⟨n, hn, ?_⟩
    have h := congrArg (Option.map (includeCfg M S hs)) he
    rw [include_runSteps] at h
    exact h

theorem restrict_halt_iff (c : TM0.Cfg Γ Λ) (hc : c.q ∈ S) :
    TM0.step (restrict M S hs) (restrictCfg M S hs c) = none ↔
      TM0.step M c = none := by
  rw [← restrict_step M S hs c hc]
  cases TM0.step M c <;> simp

theorem include_halt_iff (c : TM0.Cfg Γ (Label M S hs)) :
    TM0.step M (includeCfg M S hs c) = none ↔
      TM0.step (restrict M S hs) c = none := by
  rw [← include_step M S hs c]
  cases TM0.step (restrict M S hs) c <;> simp

variable [Fintype Γ]
variable (inputSymbol : Bool → Γ) (hinj : Function.Injective inputSymbol)
variable (hblank : ∀ b, inputSymbol b ≠ default) (accept : Λ → Bool)

noncomputable def toFiniteMachine : FiniteMachine where
  Γ := Γ
  alphabetInhabited := inferInstance
  alphabetFinite := inferInstance
  Λ := Label M S hs
  stateInhabited := labelInhabited M S hs
  stateFinite := labelFintype M S hs
  inputSymbol := inputSymbol
  input_injective := hinj
  input_ne_blank := hblank
  code := restrict M S hs
  accept := fun q => accept q.val

theorem toFiniteMachine_haltsIn_iff (w : List Bool) (output : Bool) (time : ℕ) :
    HaltsIn (toFiniteMachine M S hs inputSymbol hinj hblank accept) w output time ↔
      ∃ k ≤ time, ∃ c : TM0.Cfg Γ Λ,
        runSteps (TM0.step M) k (some (TM0.init (w.map inputSymbol))) = some c ∧
        TM0.step M c = none ∧ accept c.q = output := by
  dsimp only [HaltsIn, toFiniteMachine]
  constructor
  · rintro ⟨k, hk, c, hrun, hhalt, haccept⟩
    refine ⟨k, hk, includeCfg M S hs c, ?_, ?_, haccept⟩
    · have h := congrArg (Option.map (includeCfg M S hs)) hrun
      change (runSteps (TM0.step (restrict M S hs)) k
        (some (TM0.init (w.map inputSymbol)))).map (includeCfg M S hs) =
        some (includeCfg M S hs c) at h
      rw [include_runSteps] at h
      simpa only [Option.map_some, include_init] using h
    · exact (include_halt_iff M S hs c).2 hhalt
  · rintro ⟨k, hk, c, hrun, hhalt, haccept⟩
    have hc : c.q ∈ S :=
      runSteps_supports M S hs k (TM0.init (w.map inputSymbol)) hs.1 hrun
    refine ⟨k, hk, restrictCfg M S hs c, ?_, ?_, ?_⟩
    · have h := restrict_runSteps M S hs k (TM0.init (w.map inputSymbol)) hs.1
      rw [hrun, Option.map_some, restrict_init] at h
      exact h.symm
    · exact (restrict_halt_iff M S hs c hc).2 hhalt
    · change accept (retract M S hs c.q).val = output
      rw [retract_val M S hs c.q hc]
      exact haccept

end MachineFiniteRestriction
end DepthThreeLowerBound

end OAI
