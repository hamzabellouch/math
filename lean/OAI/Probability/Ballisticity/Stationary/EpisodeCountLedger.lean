import Mathlib
import OAI.Probability.Ballisticity.Stationary.EpisodeInjection
import OAI.Probability.Ballisticity.Stationary.EpisodeLength

namespace OAI

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal Classical
namespace DirectionalTransience

noncomputable def episodeStageIncomplete {d k : ℕ} (e f : Direction d) (r : ℝ → ℝ)
    (fexp g χ b : ℝ) (N : ℕ) (q : EpisodeState (k:=k) e f r) (ω : Environment d) : Prop :=
  ¬episodeStageGrows e f r fexp g χ b N q ω ∧ ¬episodeStageFails e f r fexp g χ b N q ω

namespace EpisodeLedger
variable {d k : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
  (r : ℝ → ℝ) (fexp g χ b sfloor : ℝ) (N : ℕ)
  (q : EpisodeState (k:=k) e f r) (ω : Environment d)
local notation "R" => episodeRun e f hef r fexp g χ b sfloor N q ω
local notation "Grow" => episodeStageGrows e f r fexp g χ b N
local notation "Fail" => episodeStageFails e f r fexp g χ b N
local notation "Inc" => episodeStageIncomplete e f r fexp g χ b N
local notation "Ready" => EpisodeReady e f r sfloor N
local notation "Count" => episodeCount e f hef r fexp g χ b sfloor N q ω
local notation "J" => episodeSteps e f hef r fexp g χ b sfloor N q ω

lemma counts_partition (n : ℕ) : J n=Count Grow n+Count Fail n+Count Inc n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [episodeSteps,episodeCount,episodeCount,episodeCount]
    by_cases hr : Ready (R n)
    · by_cases hg : Grow (R n) ω
      · have hf := ((episodeStage_grows_iff e f r fexp g χ b N (R n) ω).mp hg).2
        simp only [episodeStageIncomplete,hr,hg,hf,not_true_eq_false,false_and,and_self,
          true_and,ite_true,ite_false,add_zero]
        omega
      · by_cases hf : Fail (R n) ω
        · simp only [episodeStageIncomplete,hr,hg,hf,not_true_eq_false,not_false_eq_true,
            true_and,and_false,ite_true,ite_false,add_zero]
          omega
        · simp only [episodeStageIncomplete,hr,hg,hf,not_false_eq_true,true_and,
            and_true,ite_true,ite_false,add_zero]
          omega
    · simp only [hr,false_and,ite_false,add_zero]
      exact ih

lemma incomplete_count (n : ℕ) : Count Inc n ≤ 1 ∧ ((R n).height < N → Count Inc n=0) := by
  induction n with
  | zero => exact ⟨by simp only [episodeCount]; omega,fun _ => rfl⟩
  | succ n ih =>
    rw [episodeCount,episodeRun]
    by_cases hr : Ready (R n)
    · rw [ite_eq_left hr]
      by_cases hi : Inc (R n) ω
      · rw [ite_eq_left ⟨hr,hi⟩,ih.2 hr.1]
        refine ⟨by omega,?_⟩
        have ht := episodeStage_incomplete_terminal e f hef r fexp g χ b N (R n) ω hr.1.le hi.2 hi.1
        intro hn
        omega
      · rw [ite_eq_right (fun hh => hi hh.2),add_zero]
        exact ⟨ih.1,fun _ => ih.2 hr.1⟩
    · rw [ite_eq_right hr,ite_eq_right (fun hh => hr hh.1),add_zero]
      exact ih

lemma counts_le (n : ℕ) :
    J n ≤ Count Grow n+Count Fail n+1 ∧
      ((R n).height < N → J n=Count Grow n+Count Fail n) := by
  have hp := counts_partition e f hef r fexp g χ b sfloor N q ω n
  have hi := incomplete_count e f hef r fexp g χ b sfloor N q ω n
  constructor
  · omega
  · intro hn
    have hz := hi.2 hn
    omega

lemma nonterminal_ledger (hq : 0 < q.scale) (hqN : q.height ≤ N)
    (hqfloor : q.scale=sfloor)
    (hH : ∀ s, sfloor ≤ s → 0 < episodeStageH χ b s)
    (hn : (R N).height < N) :
    g*b*(Count Grow N : ℝ) ≤ fexp*b*(Count Fail N : ℝ) := by
  have ht := episodeRun_terminates e f hef r fexp g χ b sfloor N q ω hqN hH
  have hs : (R N).scale < sfloor := lt_of_not_ge (fun hh => ht ⟨hn,hh⟩)
  have ha := scale_agrees e f hef r fexp g χ b sfloor N q ω N hn
  have hl := log_scale e f hef r fexp g χ b sfloor N q ω hq N
  have hp := scale_pos e f hef r fexp g χ b sfloor N q ω hq N
  have hlog : Real.log (scale e f hef r fexp g χ b sfloor N q ω N) ≤ Real.log q.scale :=
    Real.log_le_log hp (by rw [ha,hqfloor]; exact hs.le)
  linarith only [hl,hlog]

lemma terminal_ledger (hq : 0 < q.scale) (hqfloor : q.scale=sfloor)
    (hqN : q.height ≤ N) (hN : sfloor ≤ (N:ℝ)) (hf : 0 ≤ fexp) (hb : 0 ≤ b)
    (hH : ∀ s, sfloor ≤ s → s*Real.exp (g*b) ≤ (episodeStageH χ b s : ℝ)) :
    g*b*(Count Grow N : ℝ)-fexp*b*(Count Fail N : ℝ) ≤ Real.log (N:ℝ)-Real.log sfloor := by
  have ha := scale_le e f hef r fexp g χ b sfloor N q ω hq
    (by rw [hqfloor]; exact le_max_left _ _) hqN hf hb hH N
  rw [max_eq_right hN] at ha
  have hlog := Real.log_le_log (scale_pos e f hef r fexp g χ b sfloor N q ω hq N) ha
  have hl := log_scale e f hef r fexp g χ b sfloor N q ω hq N
  rw [hqfloor] at hl
  linarith only [hl,hlog]

end EpisodeLedger
end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal Classical
namespace DirectionalTransience
namespace EpisodeChainLedger
variable {d k : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
  (r : ℝ → ℝ) (fexp g χ b sfloor : ℝ) (hR : 0 ≤ r sfloor) (N : ℕ)
  (ω : Environment d)

local notation "T" => episodeBoundary (k:=k) e f hef r fexp g χ b sfloor hR N ω
local notation "Q" => episodeInitial (k:=k) e f hef r sfloor hR
local notation "Run" => episodeRun e f hef r fexp g χ b sfloor N
local notation "Grow" => episodeStageGrows (k:=k) e f r fexp g χ b N
local notation "Fail" => episodeStageFails (k:=k) e f r fexp g χ b N
local notation "Inc" => episodeStageIncomplete (k:=k) e f r fexp g χ b N
local notation "LocalCount" => episodeCount e f hef r fexp g χ b sfloor N

noncomputable def count (test : EpisodeState (k:=k) e f r → Environment d → Prop) : ℕ → ℕ
  | 0 => 0
  | i+1 => count test i + if T i < N then LocalCount (Q (T i) ω) ω test N else 0

noncomputable def steps : ℕ → ℕ
  | 0 => 0
  | i+1 => steps i + if T i < N then episodeSteps e f hef r fexp g χ b sfloor N (Q (T i) ω) ω N else 0

local notation "C" => count e f hef r fexp g χ b sfloor hR N ω
local notation "J" => steps (k:=k) e f hef r fexp g χ b sfloor hR N ω

lemma partition (i : ℕ) : J i=C Grow i+C Fail i+C Inc i := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [steps,count,count,count]
    by_cases ht : T i < N
    · simp only [ite_eq_left ht]
      have hp := EpisodeLedger.counts_partition (k:=k) e f hef r fexp g χ b sfloor N (Q (T i) ω) ω N
      omega
    · simpa only [ite_eq_right ht,add_zero] using ih

lemma incomplete (i : ℕ) : C Inc i ≤ 1 ∧ (T i < N → C Inc i=0) := by
  induction i with
  | zero => exact ⟨by simp only [count]; omega,fun _ => rfl⟩
  | succ i ih =>
    rw [count,episodeBoundary]
    by_cases ht : T i < N
    · simp only [ite_eq_left ht]
      have hz := ih.2 ht
      rw [hz,zero_add]
      exact EpisodeLedger.incomplete_count e f hef r fexp g χ b sfloor N (Q (T i) ω) ω N
    · simpa only [ite_eq_right ht,add_zero] using ih

lemma counts_le (i : ℕ) : J i ≤ C Grow i+C Fail i+1 := by
  have hp := partition (k:=k) e f hef r fexp g χ b sfloor hR N ω i
  have hi := (incomplete (k:=k) e f hef r fexp g χ b sfloor hR N ω i).1
  omega

lemma balance (hs : 0 < sfloor) (hN : sfloor ≤ (N:ℝ))
    (hf : 0 ≤ fexp) (hb : 0 ≤ b)
    (hH : ∀ s, sfloor ≤ s → s*Real.exp (g*b) ≤ (episodeStageH χ b s : ℝ)) (i : ℕ) :
    g*b*(C Grow i : ℝ)-fexp*b*(C Fail i : ℝ) ≤ Real.log (N:ℝ)-Real.log sfloor ∧
      (T i < N → g*b*(C Grow i : ℝ)-fexp*b*(C Fail i : ℝ) ≤ 0) := by
  have hH0 : ∀ s, sfloor ≤ s → 0 < episodeStageH χ b s := by
    intro s h
    exact_mod_cast (mul_pos (hs.trans_le h) (Real.exp_pos (g*b))).trans_le (hH s h)
  have hL : 0 ≤ Real.log (N:ℝ)-Real.log sfloor := sub_nonneg.mpr (Real.log_le_log hs hN)
  induction i with
  | zero => simpa only [count,Nat.cast_zero,mul_zero,sub_self] using ⟨hL,fun _ => le_refl 0⟩
  | succ i ih =>
    rw [count,count,episodeBoundary]
    by_cases ht : T i < N
    · simp only [ite_eq_left ht,Nat.cast_add]
      have hqN : (Q (T i) ω).height ≤ N := Nat.succ_le_of_lt ht
      have hqpos : 0 < (Q (T i) ω).scale := hs
      have hqeq : (Q (T i) ω).scale=sfloor := rfl
      have hp := ih.2 ht
      have hu := EpisodeLedger.terminal_ledger e f hef r fexp g χ b sfloor N
        (Q (T i) ω) ω hqpos hqeq hqN hN hf hb hH
      constructor
      · nlinarith only [hp,hu]
      · intro hn
        have hh := EpisodeLedger.nonterminal_ledger e f hef r fexp g χ b sfloor N
          (Q (T i) ω) ω hqpos hqN hqeq hH0 hn
        nlinarith only [hp,hh]
    · simpa only [ite_eq_right ht,add_zero] using ih

theorem stage_count_bound (hs : 1 ≤ sfloor) (hN : sfloor ≤ (N:ℝ))
    (hf : 0 ≤ fexp) (hg : 0 < g) (hb : 0 < b)
    (hH : ∀ s, sfloor ≤ s → s*Real.exp (g*b) ≤ (episodeStageH χ b s : ℝ)) :
    (J N : ℝ) ≤ Real.log (N:ℝ)/(g*b)+(1+fexp/g)*(C Fail N : ℝ)+1 := by
  have hbal := (balance (k:=k) e f hef r fexp g χ b sfloor hR N ω
    (lt_of_lt_of_le (by norm_num : (0:ℝ)<1) hs) hN hf hb.le hH N).1
  have hlog : 0 ≤ Real.log sfloor := Real.log_nonneg hs
  have hcnt : (J N : ℝ) ≤ (C Grow N : ℝ)+(C Fail N : ℝ)+1 := by
    exact_mod_cast counts_le (k:=k) e f hef r fexp g χ b sfloor hR N ω N
  have hgb : 0 < g*b := mul_pos hg hb
  apply (mul_le_mul_iff_right₀ hgb).mp
  have he : (g*b)*(Real.log (N:ℝ)/(g*b)+(1+fexp/g)*(C Fail N : ℝ)+1) =
      Real.log (N:ℝ)+(g*b)*(C Fail N : ℝ)+(fexp*b)*(C Fail N : ℝ)+g*b := by
    field_simp
    ring
  rw [he]
  have hh := mul_le_mul_of_nonneg_right hcnt hgb.le
  nlinarith only [hh,hbal,hlog]

end EpisodeChainLedger
end DirectionalTransience

end

end OAI
