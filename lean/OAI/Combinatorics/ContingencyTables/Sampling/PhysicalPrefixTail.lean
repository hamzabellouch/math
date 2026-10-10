import OAI.Combinatorics.ContingencyTables.Sampling.PhysicalPartialSequence

namespace OAI

/-! # Future halting tails after a bounded stopping prefix -/

namespace ContingencyTables.PhysicalPrefixTail
open MatchingFPRAS MatchingFPRAS.PhysicalStream MatchingFPRAS.PhysicalPost Turing
open PhysicalRetryTail

variable {Γ Q A : Type} [Inhabited Γ]

lemma deterministic_mean (M : Table Γ Q) (c d : Cfg Γ Q) (k : ℕ)
    (h : ∀ b : Stream,execute M k c b=d) (f : Cfg Γ Q → ℚ) :
    (experiment M k c).mean f=f d := by
  rw [←physical_law]
  simp_rw [h]
  exact average_const _ _

/-- A prefix may end at different times on different tapes. After its
worst-case budget, the future live probability is bounded by the average
future live probability at its actual endpoints. -/
theorem after_prefix (M : Table Γ Q) (out : A → Cfg Γ Q) (c : Cfg Γ Q)
    (p : Experiment A) (h : Implements M out c p) (S n : ℕ) (hS : p.cost≤S) :
    (experiment M (S+n) c).mean live≤
      p.mean (fun a => (experiment M n (out a)).mean live) := by
  induction h generalizing S n with
  | done a =>
    have hm := tail_antitone M (out a) (show n≤S+n by omega)
    unfold tail at hm
    change (experiment M (S+n) (out a)).mean live≤(experiment M n (out a)).mean live
    exact_mod_cast hm
  | read c p h ih =>
    have hpos : 0<S := by simp only [Experiment.cost] at hS; omega
    obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_zero_of_lt hpos)
    have h0 : (p false).cost≤k := by simp only [Experiment.cost] at hS; omega
    have h1 : (p true).cost≤k := by simp only [Experiment.cost] at hS; omega
    have a := ih false k n h0
    have b := ih true k n h1
    simpa only [Nat.succ_add,experiment,Experiment.mean] using
      (div_le_div_of_nonneg_right (add_le_add a b) (by norm_num : (0:ℚ)≤2))
  | delay c d k p hs hp ih =>
    have hk : k≤S := by simp only [Experiment.cost] at hS; omega
    obtain ⟨r,hr⟩ := Nat.exists_eq_add_of_le hk
    have hpbound : p.cost≤r := by simp only [Experiment.cost] at hS; omega
    rw [hr,Nat.add_assoc,experiment_mean_add,deterministic_mean M c d k hs]
    exact ih r n hpbound

end ContingencyTables.PhysicalPrefixTail

end OAI
