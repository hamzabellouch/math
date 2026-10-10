import OAI.Combinatorics.ContingencyTables.Counting.CompanionPhaseFinishSemantics
import OAI.Combinatorics.ContingencyTables.Rooted.RootedRestartAgreement
import OAI.Combinatorics.ContingencyTables.Rooted.RootedPhaseHistory

namespace OAI

/-! # Canonical multiplier entries determine the projected phase history

The extension uses only the first label of a raw coordinate pair. Its values
away from canonical pairs need not match the original multiplier.
-/
namespace ContingencyTables.CompanionCanonicalHistory
open CompanionFactorialApplication CompanionRationalUpdates CompanionMultiplierAgreement
open CommonBasesFPRAS TwoLiftStates GridBoundary
open CompanionPhaseWords (Stored phaseBits)
open scoped Classical
noncomputable section
variable {I J : Type} [Fintype I] [Fintype J]
variable (A : Instance I J) {p : ℕ} (g : Fin p ≃ Labels A)

abbrev Canonical := (Fin p→Fin p→ℚ)×ℚ

def project (s : Stored A) : Canonical (p := p) :=
  CompanionPhaseFinishProgram.storedView A g s

def extend (s : Canonical (p := p)) : Stored A :=
  ⟨(fun a b => s.1 (g.symm a.1.1) (g.symm b.1.1)),s.2⟩

@[simp] theorem project_extend (s : Canonical (p := p)) :
    project A g (extend A g s)=s := by
  apply Prod.ext
  · funext i j
    simp only [project,extend,CompanionPhaseFinishProgram.storedView,pair,Equiv.symm_apply_apply]
  · rfl

theorem project_eq_iff (s t : Stored A) :
    project A g s=project A g t ↔ Agree A s.multiplier t.multiplier ∧ s.estimate=t.estimate := by
  constructor
  · intro h
    constructor
    · intro a b
      have he := congrFun (congrFun (congrArg Prod.fst h) (g.symm a)) (g.symm b)
      simpa only [project,CompanionPhaseFinishProgram.storedView,Equiv.apply_symm_apply] using he
    · exact congrArg Prod.snd h
  · rintro ⟨hw,he⟩
    apply Prod.ext
    · funext i j
      exact hw (g i) (g j)
    · exact he

theorem extend_project_agree (s : Stored A) :
    Agree A (extend A g (project A g s)).multiplier s.multiplier := by
  intro a b
  simp only [extend,project,CompanionPhaseFinishProgram.storedView,pair,Equiv.apply_symm_apply]

theorem learn_agree (w w' : Pair A→Pair A→ℚ) (hw : Agree A w w')
    (states : List (Set (Labels A×Bool))) :
    Agree A (rationalLearn pairs w states) (rationalLearn pairs w' states) := by
  intro a b
  by_cases h : pair a∈(pairs : List (Pair A)) ∧ pair b∈(pairs : List (Pair A)) ∧ pair a≠pair b
  · simp only [rationalLearn,h,hw a b]
  · simp only [rationalLearn,h,ite_false,hw a b]

theorem update_project_eq (R : RootedCompletion.Selection A.T) (C K j N : ℕ)
    (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W) (xi : ℚ)
    (v : Grid (I := Fin (CompanionOracleDensity.dimension A)) K)
    (s t : Stored A) (h : project A g s=project A g t)
    (states : Fin N→Set (Labels A×Bool)) (bits : Fin (phaseBits A C K j N xi)→Bool) :
    (RootedPhaseWords.update A R C K j N hK hW xi v s states bits).map (project A g)=
      (RootedPhaseWords.update A R C K j N hK hW xi v t states bits).map (project A g) := by
  obtain ⟨hw,he⟩ := (project_eq_iff A g s t).mp h
  unfold RootedPhaseWords.update
  split_ifs
  · simp only [Option.map_some]
    apply congrArg Option.some
    apply (project_eq_iff A g _ _).mpr
    exact ⟨learn_agree A s.multiplier t.multiplier hw _,congrArg (fun e => e*_) he⟩
  · rfl

theorem trial_project_eq (R : RootedCompletion.Selection A.T) (C K j k N : ℕ)
    (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W) (xi : ℚ)
    (v : Grid (I := Fin (CompanionOracleDensity.dimension A)) K)
    (s t : Stored A) (h : project A g s=project A g t)
    (S : CompanionBooleanPhase.State A) (bits : RootedPhaseTrial.TrialWords A C K j k N xi) :
    (RootedPhaseTrial.trial A R C K j k N hK hW xi v s S bits).map (project A g)=
      (RootedPhaseTrial.trial A R C K j k N hK hW xi v t S bits).map (project A g) := by
  have hw := ((project_eq_iff A g s t).mp h).1
  unfold RootedPhaseTrial.trial
  rw [observedStates_eq A R C K j k N hK hW xi v s.multiplier t.multiplier hw]
  exact update_project_eq A g R C K j (N+1) hK hW xi v s t h _ _

theorem restart_project_eq (R : RootedCompletion.Selection A.T)
    (C K H L j k n N h : ℕ) (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W) (xi : ℚ)
    (v : Grid (I := Fin (CompanionOracleDensity.dimension A)) K)
    (w w' : ℕ→Pair A→Pair A→ℚ) (e e' : ℚ)
    (hw : ∀ i,i ≤ j → Agree A (w i) (w' i)) (he : e=e')
    (bits : RootedRestartTrial.Words A C K H L j k n N h xi) :
    (RootedRestartTrial.run A R C K H L j k n N h hK hW xi v w e bits).map (project A g)=
      (RootedRestartTrial.run A R C K H L j k n N h hK hW xi v w' e' bits).map (project A g) := by
  have hi := RootedRestartWords.initializedStages_agree A R C K H L k n h j hK hW xi v w w'
    (fun i hi => hw (i+1) (by omega)) bits.1
  unfold RootedRestartTrial.run
  rw [hi]
  exact trial_project_eq A g R C K j k N hK hW xi v ⟨w j,e⟩ ⟨w' j,e'⟩
    ((project_eq_iff A g _ _).mpr ⟨hw j le_rfl,he⟩) _ _

theorem lookup_project_eq (history history' : List (Stored A))
    (h : history.map (project A g)=history'.map (project A g)) (i : ℕ) :
    project A g (RootedStoredHistory.lookup A history i)=
      project A g (RootedStoredHistory.lookup A history' i) := by
  cases i with
  | zero => rfl
  | succ i =>
    have he := congrArg (fun xs : List (Canonical (p := p)) =>
      xs.getD i (project A g (RootedStoredEstimate.initialStored A))) h
    simpa only [RootedStoredHistory.lookup,List.getD_map] using he

private theorem project_getD (a b : Option (Stored A)) (s t : Stored A)
    (h : a.map (project A g)=b.map (project A g)) (he : project A g s=project A g t) :
    project A g (a.getD s)=project A g (b.getD t) := by
  cases a <;> cases b <;> simp_all

theorem step_project_eq (R : RootedCompletion.Selection A.T) (s : RootedPhaseHistory.Settings A)
    (history history' : List (Stored A))
    (hh : history.map (project A g)=history'.map (project A g)) (bits : RootedPhaseHistory.Word A s) :
    project A g (RootedPhaseHistory.step A R s history bits)=
      project A g (RootedPhaseHistory.step A R s history' bits) := by
  have hlen : history.length=history'.length := by
    simpa only [List.length_map] using congrArg List.length hh
  have hold := lookup_project_eq A g history history' hh history'.length
  dsimp only [RootedPhaseHistory.step]
  rw [hlen]
  split_ifs with hj
  · apply project_getD A g _ _ _ _ _ hold
    apply restart_project_eq A g R s.C s.K s.H s.L history'.length s.k s.n s.N s.h
      s.hK s.hW s.xi s.v
    · intro i _
      exact ((project_eq_iff A g _ _).mp (lookup_project_eq A g history history' hh i)).1
    · exact ((project_eq_iff A g _ _).mp hold).2
  · exact hold

def canonicalStep (R : RootedCompletion.Selection A.T) (s : RootedPhaseHistory.Settings A)
    (history : List (Canonical (p := p))) (bits : RootedPhaseHistory.Word A s) : Canonical (p := p) :=
  project A g (RootedPhaseHistory.step A R s (history.map (extend A g)) bits)

theorem step_project (R : RootedCompletion.Selection A.T) (s : RootedPhaseHistory.Settings A)
    (history : List (Stored A)) (bits : RootedPhaseHistory.Word A s) :
    project A g (RootedPhaseHistory.step A R s history bits)=
      canonicalStep A g R s (history.map (project A g)) bits := by
  apply step_project_eq A g R s history ((history.map (project A g)).map (extend A g))
  simp only [List.map_map,Function.comp_def,project_extend]

end
end ContingencyTables.CompanionCanonicalHistory

end OAI
