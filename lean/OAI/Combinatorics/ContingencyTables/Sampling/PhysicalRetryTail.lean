import OAI.Combinatorics.ContingencyTables.Sampling.PhysicalRetryIteration
import OAI.Combinatorics.ContingencyTables.Machines.GeometricRuntime

namespace OAI

/-! # Physical halting tails from finite rejection prefixes -/

namespace ContingencyTables.PhysicalRetryTail
open MatchingFPRAS MatchingFPRAS.PhysicalStream MatchingFPRAS.PhysicalPost
open scoped BigOperators Classical

variable {Γ Q B : Type} [Inhabited Γ]

def live (c : Cfg Γ Q) : ℚ := if c.state=none then 0 else 1

private lemma mean_mono {A : Type} (p : Experiment A) (f g : A → ℚ) (h : ∀ a,f a≤g a) :
    p.mean f≤p.mean g := by
  induction p with
  | done a => exact h a
  | read p ih => simp only [Experiment.mean]; linarith [ih false,ih true]
  | delay n p ih => exact ih

private lemma mean_const {A : Type} (p : Experiment A) (c : ℚ) : p.mean (fun _ => c)=c := by
  induction p with
  | done => rfl
  | read p ih => simp only [Experiment.mean,ih]; ring
  | delay n p ih => exact ih

lemma live_nonnegative (c : Cfg Γ Q) : 0≤live c := by unfold live; split_ifs <;> norm_num
lemma live_le_one (c : Cfg Γ Q) : live c≤1 := by unfold live; split_ifs <;> norm_num

lemma experiment_mean_add (M : Table Γ Q) (n m : ℕ) (c : Cfg Γ Q) (g : Cfg Γ Q → ℚ) :
    (experiment M (n+m) c).mean g=
      (experiment M n c).mean (fun d => (experiment M m d).mean g) := by
  induction n generalizing c with
  | zero => simp only [Nat.zero_add,experiment,Experiment.mean]
  | succ n ih => simp only [Nat.succ_add,experiment,Experiment.mean,ih]

lemma halted_mean (M : Table Γ Q) (n : ℕ) (c : Cfg Γ Q) (h : c.state=none)
    (g : Cfg Γ Q → ℚ) : (experiment M n c).mean g=g c := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have ht (b : Bool) : PhysicalPost.tick M c b=c := by simp [PhysicalPost.tick,h]
    simp only [experiment,Experiment.mean,ht,ih]
    ring

lemma future_live_le (M : Table Γ Q) (n : ℕ) (c : Cfg Γ Q) :
    (experiment M n c).mean live≤live c := by
  by_cases h : c.state=none
  · rw [halted_mean M n c h]
  · have hm:=mean_mono (experiment M n c) live (fun _ => 1) live_le_one
    rw [mean_const] at hm
    simpa only [live,ite_eq_right h] using hm

def tail (M : Table Γ Q) (c : Cfg Γ Q) (n : ℕ) : ℝ :=
  ((experiment M n c).mean live:ℝ)

lemma tail_nonnegative (M : Table Γ Q) (c : Cfg Γ Q) (n : ℕ) : 0≤tail M c n := by
  have hm:=mean_mono (experiment M n c) (fun _ => 0) live live_nonnegative
  rw [mean_const] at hm
  unfold tail
  exact_mod_cast hm

lemma tail_antitone (M : Table Γ Q) (c : Cfg Γ Q) : Antitone (tail M c) := by
  intro n m hnm
  obtain ⟨k,rfl⟩:=Nat.exists_eq_add_of_le hnm
  have hm : (experiment M (n+k) c).mean live≤(experiment M n c).mean live := by
    rw [experiment_mean_add]
    exact mean_mono _ _ _ (future_live_le M k)
  unfold tail
  exact_mod_cast hm

lemma padded_halted_result (M : Table Γ Q) (out : B → Cfg Γ Q) (c : Cfg Γ Q)
    (p : Experiment B) (hp : Implements M out c p) (n : ℕ) (hn : p.cost≤n)
    (b : Stream) (hhalt : (out (p.run b).1).state=none) :
    execute M n c b=out (p.run b).1 := by
  have hb : (p.run b).2≤n := (Experiment.run_cost p b).trans hn
  obtain ⟨k,hk⟩:=Nat.exists_eq_add_of_le hb
  rw [hk,execute_add,hp.execution b]
  have he : out (p.run b).1=⟨none,(out (p.run b).1).tape⟩ := by
    cases e:out (p.run b).1 with
    | mk state tape =>
      rw [e] at hhalt
      change state=none at hhalt
      subst state
      rfl
  rw [he,execute_halted]

/-- All successful prefix executions have halted by the prefix cost.
This implication is enough even though the failed endpoint is still live. -/
theorem tail_le_failure (M : Table Γ Q) (out : Option B → Cfg Γ Q) (c : Cfg Γ Q)
    (p : Experiment (Option B)) (hp : Implements M out c p)
    (hhalt : ∀ b,(out (some b)).state=none) (n : ℕ) (hn : p.cost≤n) :
    tail M c n≤(p.mean (fun b => if b=none then 1 else 0):ℚ) := by
  have hb : (experiment M n c).mean live≤p.mean (fun b => if b=none then 1 else 0) := by
    rw [←physical_law,←Experiment.average_run p _ n hn]
    unfold average
    apply div_le_div_of_nonneg_right _ (by positivity)
    apply Finset.sum_le_sum
    intro b _
    cases he:(p.run (extend b)).1 with
    | none => simp only [ite_true]; exact live_le_one _
    | some x =>
      have hh : (out (p.run (extend b)).1).state=none := by rw [he]; exact hhalt x
      rw [padded_halted_result M out c p hp n hn (extend b) hh]
      simp [he,live,hhalt]
  unfold tail
  exact_mod_cast hb

end ContingencyTables.PhysicalRetryTail

end OAI
