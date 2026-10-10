import OAI.Combinatorics.ContingencyTables.Sampling.PhysicalPrefixTail
import OAI.Combinatorics.MatchingCount.Machines.PhysicalProgramSeal

namespace OAI

/-! # Terminal-event bounds from finite stopping prefixes -/

namespace ContingencyTables.PhysicalEventBounds
open MatchingFPRAS MatchingFPRAS.PhysicalStream MatchingFPRAS.PhysicalPost Turing
open scoped BigOperators Classical
noncomputable section
variable {Γ Q A : Type} [Inhabited Γ]

def event (P : Cfg Γ Q → Prop) (c : Cfg Γ Q) : ℚ := if P c then 1 else 0

lemma event_nonneg (P : Cfg Γ Q → Prop) (c : Cfg Γ Q) : 0≤event P c := by
  unfold event; split_ifs <;> norm_num
lemma event_le_one (P : Cfg Γ Q → Prop) (c : Cfg Γ Q) : event P c≤1 := by
  unfold event; split_ifs <;> norm_num

lemma mean_mono (p : Experiment A) (f g : A → ℚ) (h : ∀ a,f a≤g a) :
    p.mean f≤p.mean g := by
  induction p with
  | done a => exact h a
  | read p ih => simp only [Experiment.mean]; linarith [ih false,ih true]
  | delay n p ih => exact ih

lemma average_mono {n : ℕ} (f g : Bits n → ℚ) (h : ∀ b,f b≤g b) :
    average f≤average g := by
  unfold average
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum (fun b _ => h b)) (by positivity)

/-- Only successful endpoints need be halted; the failure endpoint can be live. -/
theorem stopped_event_bounds (M : PhysicalPost.Table Γ Q) (out : Option A → Cfg Γ Q)
    (c : Cfg Γ Q) (p : Experiment (Option A)) (hp : Implements M out c p)
    (hhalt : ∀ a,(out (some a)).state=none) (P : Cfg Γ Q → Prop)
    (n : ℕ) (hn : p.cost≤n) :
    p.mean (fun o => o.elim 0 (fun a => event P (out (some a))))≤
        (experiment M n c).mean (event P) ∧
      (experiment M n c).mean (event P)≤
        p.mean (fun o => o.elim 0 (fun a => event P (out (some a))))+
          p.mean (fun o => if o=none then 1 else 0) := by
  have lower (b : Bits n) :
      ((p.run (extend b)).1.elim 0 (fun a => event P (out (some a))))≤
        event P (execute M n c (extend b)) := by
    cases he : (p.run (extend b)).1 with
    | none => exact event_nonneg P _
    | some a =>
      have hh : (out (p.run (extend b)).1).state=none := by rw [he]; exact hhalt a
      rw [PhysicalRetryTail.padded_halted_result M out c p hp n hn (extend b) hh,he]
      exact le_rfl
  have upper (b : Bits n) : event P (execute M n c (extend b))≤
      ((p.run (extend b)).1.elim 0 (fun a => event P (out (some a))))+
        (if (p.run (extend b)).1=none then 1 else 0) := by
    cases he : (p.run (extend b)).1 with
    | none => simpa only [Option.elim_none,ite_true,zero_add] using event_le_one P _
    | some a =>
      have hh : (out (p.run (extend b)).1).state=none := by rw [he]; exact hhalt a
      rw [PhysicalRetryTail.padded_halted_result M out c p hp n hn (extend b) hh,he]
      simp only [Option.elim_some,Option.some_ne_none,ite_false,add_zero,le_refl]
  have hl := average_mono _ _ lower
  have hu := average_mono _ _ upper
  rw [physical_law,Experiment.average_run p
    (fun o => o.elim 0 (fun a => event P (out (some a)))) n hn] at hl
  rw [physical_law,average_add,Experiment.average_run p
    (fun o => o.elim 0 (fun a => event P (out (some a)))) n hn,
    Experiment.average_run p (fun o => if o=none then 1 else 0) n hn] at hu
  exact ⟨hl,hu⟩

lemma terminal_event_monotone (M : PhysicalPost.Table Γ Q) (c : Cfg Γ Q)
    (P : Cfg Γ Q → Prop) (hP : ∀ d,P d → d.state=none) :
    Monotone (fun n => (experiment M n c).mean (event P)) := by
  intro n m hnm
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hnm
  change (experiment M n c).mean (event P)≤(experiment M (n+k) c).mean (event P)
  rw [PhysicalRetryTail.experiment_mean_add]
  apply mean_mono
  intro d
  by_cases hd : P d
  · rw [PhysicalRetryTail.halted_mean M k d (hP d hd)]
  · have h := (experiment M k d).mean_nonneg (event P)
      ((Experiment.all_true _).mono (fun d _ => event_nonneg P d))
    simpa only [event,ite_eq_right hd] using h

/-- A terminal event absent at every successful endpoint is bounded by
prefix failure even at times earlier than the stopping-prefix budget. -/
theorem absent_event_bound (M : PhysicalPost.Table Γ Q) (out : Option A → Cfg Γ Q)
    (c : Cfg Γ Q) (p : Experiment (Option A)) (hp : Implements M out c p)
    (hhalt : ∀ a,(out (some a)).state=none) (P : Cfg Γ Q → Prop)
    (hP : ∀ d,P d → d.state=none) (habsent : ∀ a,¬P (out (some a))) (n : ℕ) :
    (experiment M n c).mean (event P)≤p.mean (fun o => if o=none then 1 else 0) := by
  have hu := (stopped_event_bounds M out c p hp hhalt P (max n p.cost) (le_max_right _ _)).2
  have hz : p.mean (fun o => o.elim 0 (fun a => event P (out (some a))))=0 := by
    have he : (fun o : Option A => o.elim 0 (fun a => event P (out (some a))))=
        (fun _ => (0:ℚ)) := by
      funext o; cases o with
      | none => rfl
      | some a => simp only [Option.elim_some,event,ite_eq_right (habsent a)]
    rw [he,PhysicalPartialSequence.mean_const]
  rw [hz,zero_add] at hu
  exact (terminal_event_monotone M c P hP (le_max_left _ _)).trans hu

/-- Prefix accuracy transfers to physical time without assuming a
uniform bound on the number of steps in the prefix. -/
lemma tendsto_of_prefix_bounds (f a b : ℕ → ℝ) (L : ℝ)
    (ha : Filter.Tendsto a Filter.atTop (nhds L))
    (hb : Filter.Tendsto b Filter.atTop (nhds 0))
    (h : ∀ N,∃ S,∀ t,S≤t → a N≤f t ∧ f t≤a N+b N) :
    Filter.Tendsto f Filter.atTop (nhds L) := by
  apply Metric.tendsto_atTop.2
  intro ε hε
  obtain ⟨Na,hNa⟩ := Metric.tendsto_atTop.1 ha (ε/2) (by linarith)
  obtain ⟨Nb,hNb⟩ := Metric.tendsto_atTop.1 hb (ε/2) (by linarith)
  obtain ⟨S,hS⟩ := h (max Na Nb)
  refine ⟨S,?_⟩
  intro t ht
  have h1 := hNa (max Na Nb) (le_max_left _ _)
  have h2 := hNb (max Na Nb) (le_max_right _ _)
  rw [Real.dist_eq] at h1 h2 ⊢
  have ha' := abs_lt.mp h1
  have hb' := abs_lt.mp h2
  have hh := hS t ht
  exact abs_lt.mpr ⟨by linarith,by linarith⟩

lemma mean_one_sub (p : Experiment A) (f : A → ℚ) :
    p.mean (fun a => 1-f a)=1-p.mean f := by
  induction p with
  | done a => rfl
  | read p ih => simp only [Experiment.mean,ih]; ring
  | delay n p ih => exact ih

lemma run_halted_iff (P : Program) (input : List Symbol) (n : ℕ) (b : Bits n) :
    (MatchingFPRAS.run P.machine input b).state=none ↔
      (execute P.table n (P.initial (Tape.mk₁ input)) (extend b)).state=none := by
  let : Inhabited {q //q∈P.states} := ⟨⟨P.entry,P.entry_mem⟩⟩
  have he := congrArg Cfg.state (execute_lift P.table P.states P.supported n
    ⟨some default,Tape.mk₁ input⟩ (extend b))
  rw [Program.machine,restrictedMachine_run]
  change ((execute (restrict P.table P.states P.supported) n
    ⟨some default,Tape.mk₁ input⟩ (extend b)).state.map enumeration)=none ↔ _
  change (execute P.table n (P.initial (Tape.mk₁ input)) (extend b)).state=_ at he
  rw [he]
  simp only [liftCfg,Option.map_eq_none_iff]

end
end ContingencyTables.PhysicalEventBounds

end OAI
