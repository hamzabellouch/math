import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.ExecutionState

namespace OAI

namespace MetricKMedianRecovery

inductive CountedTrace {A : Type*} (R : A → A → Prop) : ℕ → A → A → Prop
  | nil (s : A) : CountedTrace R 0 s s
  | cons {s u e : A} {n : ℕ} (step : R s u) (tail : CountedTrace R n u e) :
      CountedTrace R (n+1) s e

namespace CountedTrace
variable {A : Type*} {R S : A → A → Prop} {n m : ℕ} {s u e : A}
lemma append (h : CountedTrace R n s u) (h' : CountedTrace R m u e) :
    CountedTrace R (n+m) s e := by
  induction h with
  | nil => simpa using h'
  | cons step tail ih => simpa only [Nat.add_assoc,Nat.add_comm 1 m] using cons step (ih h')
lemma map (h : CountedTrace R n s e) (f : ∀ a b, R a b → S a b) : CountedTrace S n s e := by
  induction h with
  | nil s => exact nil s
  | cons step tail ih => exact cons (f _ _ step) ih
lemma invariant (h : CountedTrace R n s e) (P : A → Prop)
    (hP : ∀ a b, R a b → P a → P b) (hs : P s) : P e := by
  induction h with
  | nil => exact hs
  | cons step tail ih => exact ih (hP _ _ step hs)
lemma exists_path (h : CountedTrace R n s e) :
    ∃ path : ℕ → A, path 0 = s ∧ path n = e ∧ ∀ j < n, R (path j) (path (j+1)) := by
  induction h with
  | nil s => exact ⟨fun _ => s,rfl,rfl,by intro j hj; omega⟩
  | @cons s u e n step tail ih =>
    obtain ⟨path,h0,he,hsteps⟩ := ih
    let path' : ℕ → A := fun j => if j = 0 then s else path (j-1)
    refine ⟨path',by simp [path'],by simpa [path'] using he,?_⟩
    intro j hj
    cases j with
    | zero => simpa [path',h0] using step
    | succ j => simpa [path'] using hsteps j (by omega)
end CountedTrace

namespace OrdinaryProducer
variable {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]

def PlainOpening (loc : D → X) (F : Finset X) (v lam : ℝ)
    (s e : ExecutionState D X) : Prop :=
  ∃ i ∈ F, i ∉ s.opened ∧ ∃ tau : D → ℝ,
    admissibleBids loc (1-3*v) (1+v^2) v s.phase s.opened i tau ∧
    lam ≤ openingPayment loc (1-3*v) s.phase s.opened i tau ∧
    (∀ i₀ ∈ F, ∀ a, activeAt loc (1-3*v) s.phase s.opened a →
      openingDual loc (1-3*v) s.phase s.opened i₀ tau a ≤ lam) ∧
    e = regularUpdate loc (1-3*v) s i s.opened tau

def PhaseMaximal (loc : D → X) (F : Finset X) (v lam : ℝ) (s : ExecutionState D X) : Prop :=
  ∀ i ∈ F, i ∉ s.opened → ¬etaOpenable loc F s.opened (1-3*v) (1+v^2) v s.phase lam 0 i

namespace PlainOpening
variable {loc : D → X} {F : Finset X} {v lam : ℝ} {s e : ExecutionState D X}
lemma atomic (h : PlainOpening loc F v lam s e) : AtomicStep loc F v lam 0 s e := by
  obtain ⟨i,hi,_,tau,hbid,hpay,hdual,rfl⟩ := h
  exact AtomicStep.regular s i s.opened tau hi (Finset.Subset.refl _) hbid (by simpa using hpay) hdual
lemma phase_eq (h : PlainOpening loc F v lam s e) : e.phase = s.phase := by
  obtain ⟨i,_,_,tau,_,_,_,rfl⟩ := h
  rfl
lemma opened_in (h : PlainOpening loc F v lam s e) (hs : s.opened ⊆ F) : e.opened ⊆ F := by
  obtain ⟨i,hi,_,tau,_,_,_,rfl⟩ := h
  exact Finset.insert_subset hi hs
lemma remaining_drop (h : PlainOpening loc F v lam s e) :
    (F \ e.opened).card + 1 = (F \ s.opened).card := by
  obtain ⟨i,hi,hin,tau,_,_,_,rfl⟩ := h
  change (F \ insert i s.opened).card + 1 = _
  rw [Finset.sdiff_insert,Finset.card_erase_of_mem (Finset.mem_sdiff.mpr ⟨hi,hin⟩)]
  have hp := Finset.card_pos.mpr ⟨i,Finset.mem_sdiff.mpr ⟨hi,hin⟩⟩
  omega
end PlainOpening

theorem complete_phase (loc : D → X) (F : Finset X) (v lam : ℝ)
    (s : ExecutionState D X) (hs : s.opened ⊆ F) :
    ∃ n ≤ (F \ s.opened).card, ∃ e : ExecutionState D X,
      CountedTrace (PlainOpening loc F v lam) n s e ∧ e.opened ⊆ F ∧
      e.phase = s.phase ∧ PhaseMaximal loc F v lam e := by
  classical
  generalize heq : (F \ s.opened).card = fuel
  induction fuel using Nat.strong_induction_on generalizing s with
  | h fuel ih =>
    by_cases hmax : PhaseMaximal loc F v lam s
    · exact ⟨0,Nat.zero_le _,s,CountedTrace.nil s,hs,rfl,hmax⟩
    · simp only [PhaseMaximal,not_forall,not_not] at hmax
      obtain ⟨i,hi,hin,tau,hbid,hpay,hdual⟩ := hmax
      let s' := regularUpdate loc (1-3*v) s i s.opened tau
      have hop : PlainOpening loc F v lam s s' :=
        ⟨i,hi,hin,tau,hbid,by simpa using hpay,hdual,rfl⟩
      have hdrop := hop.remaining_drop
      obtain ⟨n,hn,e,htrace,he,hephase,hmax⟩ :=
        ih (F \ s'.opened).card (by omega) s' (hop.opened_in hs) rfl
      exact ⟨n+1,by omega,e,CountedTrace.cons hop htrace,he,hephase.trans hop.phase_eq,hmax⟩

end OrdinaryProducer
end MetricKMedianRecovery

end OAI
