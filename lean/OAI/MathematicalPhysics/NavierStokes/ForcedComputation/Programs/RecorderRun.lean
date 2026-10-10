import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.Recorder

namespace OAI

/-! Iterating the seven-row recorder from its actual initialized tape. -/

namespace ForcedComputation.Recorder

variable {Q A : Type*}

open History Control

structure WorkConfiguration (Q A : Type*) where
  state : Q
  head : ℤ
  tape : ℤ → A

def workNext (M : Machine Q A) (C : WorkConfiguration Q A) : WorkConfiguration Q A :=
  { state := M.next C.state (C.tape C.head)
    head := C.head + M.move C.state (C.tape C.head)
    tape := Function.update C.tape C.head (M.write C.state (C.tape C.head)) }

def workAt (M : Machine Q A) (q : Q) (w : ℤ → A) (n : ℕ) : WorkConfiguration Q A :=
  (workNext M)^[n] ⟨q, 0, w⟩

theorem workAt_zero (M : Machine Q A) (q : Q) (w : ℤ → A) :
    workAt M q w 0 = ⟨q, 0, w⟩ := rfl

theorem workAt_succ (M : Machine Q A) (q : Q) (w : ℤ → A) (n : ℕ) :
    workAt M q w (n + 1) = workNext M (workAt M q w n) :=
  Function.iterate_succ_apply' _ _ _

theorem workAt_head_bounds (M : Machine Q A) (q : Q) (w : ℤ → A) (n : ℕ) :
    -(n : ℤ) ≤ (workAt M q w n).head ∧ (workAt M q w n).head ≤ n := by
  induction n with
  | zero => simp [workAt_zero]
  | succ n ih =>
    have hm := M.move_bound (workAt M q w n).state
      ((workAt M q w n).tape (workAt M q w n).head)
    rw [workAt_succ]
    dsimp only [workNext]
    constructor <;> push_cast <;> omega

/-- The history track retains every recorded instruction. -/
def historyRun (g₀ : ℤ) (r : ℕ → Record Q A) : ℕ → ℤ → History Q A :=
  Nat.rec (Function.update (fun _ => empty) g₀ frontier)
    (fun n h => Function.update
      (Function.update h (g₀ + (n : ℤ)) (History.record (r n)))
      (g₀ + (n : ℤ) + 1) frontier)

theorem historyRun_frontier (g₀ : ℤ) (r : ℕ → Record Q A) (n : ℕ) :
    historyRun g₀ r n (g₀ + (n : ℤ)) = frontier := by
  cases n with
  | zero => simp [historyRun]
  | succ n => simp [historyRun, Nat.cast_add, Nat.cast_one, add_assoc]

theorem historyRun_before (g₀ : ℤ) (r : ℕ → Record Q A) (n : ℕ)
    (j : ℤ) (hj : j < g₀ + (n : ℤ)) : historyRun g₀ r n j ≠ frontier := by
  induction n with
  | zero => simp [historyRun, Function.update_of_ne (by omega : j ≠ g₀)]
  | succ n ih =>
    have hjnew : j ≠ g₀ + (n : ℤ) + 1 := by omega
    simp only [historyRun, Function.update_of_ne hjnew]
    by_cases hjold : j = g₀ + (n : ℤ)
    · simp [hjold]
    · rw [Function.update_of_ne hjold]
      exact ih (by omega)

theorem historyRun_after (g₀ : ℤ) (r : ℕ → Record Q A) (n : ℕ)
    (j : ℤ) (hj : g₀ + (n : ℤ) < j) : historyRun g₀ r n j = empty := by
  induction n with
  | zero => simp [historyRun, Function.update_of_ne (by omega : j ≠ g₀)]
  | succ n ih =>
    have hjnew : j ≠ g₀ + (n : ℤ) + 1 := by omega
    have hjold : j ≠ g₀ + (n : ℤ) := by omega
    simp only [historyRun, Function.update_of_ne hjnew, Function.update_of_ne hjold]
    exact ih (by omega)

def workRecord (M : Machine Q A) (q : Q) (w : ℤ → A) (n : ℕ) : Record Q A :=
  ((workAt M q w n).state, (workAt M q w n).tape (workAt M q w n).head)

def checkpointAt (M : Machine Q A) (q : Q) (w : ℤ → A) (g₀ : ℤ) (n : ℕ) :
    Configuration Q A :=
  ⟨checkpoint (workAt M q w n).state, (workAt M q w n).head,
    tracks (workAt M q w n).tape (historyRun g₀ (workRecord M q w) n) (fun _ => false)⟩

theorem checkpointAt_zero (M : Machine Q A) (q : Q) (w : ℤ → A) (g₀ : ℤ) :
    checkpointAt M q w g₀ 0 =
      ⟨checkpoint q, 0, tracks w (Function.update (fun _ => empty) g₀ frontier)
        (fun _ => false)⟩ := rfl

theorem checkpoint_successor (M : Machine Q A) (q : Q) (w : ℤ → A)
    (g₀ : ℤ) (hg₀ : 2 ≤ g₀) (n : ℕ)
    (hn : M.halting (workAt M q w n).state = false) :
    ∃ m : ℕ, 0 < m ∧ Steps M m
      (checkpointAt M q w g₀ n) (checkpointAt M q w g₀ (n + 1)) := by
  let C := workAt M q w n
  let H := historyRun g₀ (workRecord M q w) n
  let h' := C.head + M.move C.state (C.tape C.head)
  let g := g₀ + (n : ℤ)
  have hhead : C.head ≤ (n : ℤ) := (workAt_head_bounds M q w n).2
  have hmove := (M.move_bound C.state (C.tape C.head)).2
  have hsep : h' < g := by dsimp [h', g]; omega
  let k := (g - h' - 1).toNat
  have hk : (k : ℤ) = g - h' - 1 := Int.toNat_of_nonneg (by omega)
  have hgap : C.head + M.move C.state (C.tape C.head) + (k : ℤ) + 1 = g := by
    dsimp [h'] at hk
    omega
  have hbefore : ∀ j < g, H j ≠ frontier := historyRun_before _ _ n
  have hfront : H g = frontier := historyRun_frontier _ _ n
  have hempty : H (g + 1) = empty := historyRun_after _ _ n _ (by dsimp [g]; omega)
  have hc := checkpoint_cycle M C.state C.tape H C.head k hn
    (hbefore _ (by dsimp [g]; omega))
    (by simpa only [hgap] using hbefore)
    (by simpa only [hgap] using hfront)
    (by simpa only [hgap] using hempty)
  refine ⟨2 * k + 6, by omega, ?_⟩
  dsimp only at hc
  rw [hgap] at hc
  simpa only [checkpointAt, workAt_succ, workNext, historyRun, workRecord,
    C, H, g] using hc

/-- Every finite nonhalting prefix of the original machine has a finite
recorder execution reaching exactly its work configuration. -/
theorem simulate_prefix (M : Machine Q A) (q : Q) (w : ℤ → A)
    (g₀ : ℤ) (hg₀ : 2 ≤ g₀) (n : ℕ)
    (hn : ∀ i < n, M.halting (workAt M q w i).state = false) :
    ∃ m : ℕ, Steps M m (checkpointAt M q w g₀ 0) (checkpointAt M q w g₀ n) := by
  induction n with
  | zero => exact ⟨0, Steps.zero _⟩
  | succ n ih =>
    obtain ⟨m, hm⟩ := ih (fun i hi => hn i (Nat.lt_succ_of_lt hi))
    obtain ⟨k, _, hk⟩ := checkpoint_successor M q w g₀ hg₀ n (hn n (Nat.lt_succ_self n))
    exact ⟨m + k, hm.trans hk⟩

theorem simulate_prefix_length (M : Machine Q A) (q : Q) (w : ℤ → A)
    (g₀ : ℤ) (hg₀ : 2 ≤ g₀) (n : ℕ)
    (hn : ∀ i < n, M.halting (workAt M q w i).state = false) :
    ∃ m : ℕ, n ≤ m ∧
      Steps M m (checkpointAt M q w g₀ 0) (checkpointAt M q w g₀ n) := by
  induction n with
  | zero => exact ⟨0, le_rfl, Steps.zero _⟩
  | succ n ih =>
    obtain ⟨m, hnm, hm⟩ := ih (fun i hi => hn i (Nat.lt_succ_of_lt hi))
    obtain ⟨k, hkpos, hk⟩ := checkpoint_successor M q w g₀ hg₀ n
      (hn n (Nat.lt_succ_self n))
    exact ⟨m + k, by omega, hm.trans hk⟩

theorem Step.successor_unique [DecidableEq Q] [DecidableEq A]
    {M : Machine Q A} {C D E : Configuration Q A} (hD : Step M C D) (hE : Step M C E) :
    D = E := by
  obtain ⟨qD, sD, dD, hlD, rfl⟩ := hD
  obtain ⟨qE, sE, dE, hlE, rfl⟩ := hE
  obtain ⟨rfl, rfl, rfl⟩ := hlD.successor_unique hlE
  rfl

theorem Steps.head {M : Machine Q A} {n : ℕ} {C E : Configuration Q A}
    (h : Steps M (n + 1) C E) :
    ∃ D, Step M C D ∧ Steps M n D E := by
  induction n generalizing C E with
  | zero =>
    cases h with
    | next h hs =>
      cases h
      exact ⟨_, hs, Steps.zero _⟩
  | succ n ih =>
    cases h with
    | next h hs =>
      obtain ⟨D, hD, hrest⟩ := ih h
      exact ⟨D, hD, Steps.next hrest hs⟩

theorem Steps.prefix_has_successor [DecidableEq Q] [DecidableEq A]
    {M : Machine Q A} {m n : ℕ} {C D E : Configuration Q A}
    (hshort : Steps M m C D) (hlong : Steps M n C E) (hmn : m < n) :
    ∃ F, Step M D F := by
  induction m generalizing n C D E with
  | zero =>
    cases hshort
    cases n with
    | zero => omega
    | succ n =>
      obtain ⟨F, hF, _⟩ := hlong.head
      exact ⟨F, hF⟩
  | succ m ih =>
    obtain ⟨C₁, hC₁, hrest⟩ := hshort.head
    cases n with
    | zero => omega
    | succ n =>
      obtain ⟨C₂, hC₂, htail⟩ := hlong.head
      have he : C₁ = C₂ := hC₁.successor_unique hC₂
      subst C₂
      exact ih hrest htail (by omega)

def haltingControl (M : Machine Q A) : Control Q A → Bool
  | checkpoint q => M.halting q
  | _ => false

theorem LocalStep.source_nonhalting {M : Machine Q A} {q q' : Control Q A}
    {s s' : Symbol Q A} {d : ℤ} (h : LocalStep M q s q' s' d) :
    haltingControl M q = false := by
  cases h <;> simp_all [haltingControl]

theorem halted_no_step (M : Machine Q A) (q : Q) (head : ℤ)
    (tape : ℤ → Symbol Q A) (hq : M.halting q = true) (D : Configuration Q A) :
    ¬ Step M ⟨checkpoint q, head, tape⟩ D := by
  rintro ⟨q', s', d, hlocal, _⟩
  have hfalse := hlocal.source_nonhalting
  simp [haltingControl, hq] at hfalse

/-- Starting with the actual finite-history initialization, a recorder reaches
a halting checkpoint exactly when the original machine halts. -/
theorem halting_checkpoint_iff [DecidableEq Q] [DecidableEq A]
    (M : Machine Q A) (q : Q) (w : ℤ → A) (g₀ : ℤ) (hg₀ : 2 ≤ g₀) :
    (∃ m C q', Steps M m (checkpointAt M q w g₀ 0) C ∧
      C.control = checkpoint q' ∧ M.halting q' = true) ↔
      ∃ n, M.halting (workAt M q w n).state = true := by
  classical
  constructor
  · rintro ⟨m, C, q', hrun, hcontrol, hhalt⟩
    by_contra hnone
    have hnonhalt (i : ℕ) : M.halting (workAt M q w i).state = false := by
      cases he : M.halting (workAt M q w i).state with
      | false => rfl
      | true => exact False.elim (hnone ⟨i, he⟩)
    obtain ⟨k, hmk, hlong⟩ := simulate_prefix_length M q w g₀ hg₀ (m + 1)
      (fun i _ => hnonhalt i)
    obtain ⟨D, hD⟩ := hrun.prefix_has_successor hlong (by omega)
    cases C with
    | mk control head tape =>
      simp only at hcontrol
      subst control
      exact halted_no_step M q' head tape hhalt D hD
  · intro hhalt
    let n := Nat.find hhalt
    have hn : M.halting (workAt M q w n).state = true := Nat.find_spec hhalt
    have hprior (i : ℕ) (hi : i < n) : M.halting (workAt M q w i).state = false := by
      cases he : M.halting (workAt M q w i).state with
      | false => rfl
      | true => exact False.elim (Nat.find_min hhalt hi he)
    obtain ⟨m, hm⟩ := simulate_prefix M q w g₀ hg₀ n hprior
    exact ⟨m, checkpointAt M q w g₀ n, (workAt M q w n).state, hm, rfl, hn⟩

end ForcedComputation.Recorder

end OAI
