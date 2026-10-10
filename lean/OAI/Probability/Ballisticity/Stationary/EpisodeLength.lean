import Mathlib
import OAI.Probability.Ballisticity.Estimates.StageClassification

namespace OAI

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal Classical
namespace DirectionalTransience

lemma episodeStageScale_pos {d k : ℕ} (e f : Direction d) (r : ℝ → ℝ)
    (fexp g χ b : ℝ) (N : ℕ) (q : EpisodeState (k:=k) e f r) (ω : Environment d) (hs : 0 < q.scale) :
    0 < episodeStageScale e f r fexp g χ b N q ω := by
  unfold episodeStageScale
  split <;> positivity

lemma episodeStageScale_le {d k : ℕ} (e f : Direction d) (r : ℝ → ℝ)
    (fexp g χ b : ℝ) (N : ℕ) (q : EpisodeState (k:=k) e f r) (ω : Environment d)
    (hf : 0 ≤ fexp) (hg : 0 ≤ g) (hb : 0 ≤ b) (hs : 0 ≤ q.scale) :
    episodeStageScale e f r fexp g χ b N q ω ≤ q.scale*Real.exp (g*b) := by
  unfold episodeStageScale
  split
  · exact le_rfl
  · exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith)) hs

lemma episodeStageLength_le {d k : ℕ} (e f : Direction d) (r : ℝ → ℝ)
    (fexp g χ b : ℝ) (N : ℕ) (q : EpisodeState (k:=k) e f r) (ω : Environment d) (hs : 0 ≤ q.scale) :
    (episodeStageLength e f r fexp g χ b N q ω : ℝ) ≤ q.scale*Real.exp (χ*b) := by
  have hh := (stageStop_le e f q.height (r (q.scale*Real.exp (-fexp*b)))
    (r (q.scale*Real.exp (g*b))) ((k:ℝ)*b) (fun _ => q.profile.toLayerProfile)
    (episodeStageH χ b q.scale) (N-q.height) ω).trans (min_le_left _ _)
  exact (show (episodeStageLength e f r fexp g χ b N q ω : ℝ) ≤ (episodeStageH χ b q.scale : ℝ) by exact_mod_cast hh).trans
    (Nat.floor_le (mul_nonneg hs (Real.exp_pos _).le))

lemma episodeRun_length_scale {d k : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (r : ℝ → ℝ) (fexp g χ b sfloor : ℝ) (N : ℕ)
    (q : EpisodeState (k:=k) e f r) (ω : Environment d)
    (hf : 0 ≤ fexp) (hg : 0 ≤ g) (hb : 0 ≤ b) (hq : 0 < q.scale) (n : ℕ) :
    let p := episodeRun e f hef r fexp g χ b sfloor N q ω n
    let J := episodeSteps e f hef r fexp g χ b sfloor N q ω n
    0 < p.scale ∧ p.scale ≤ q.scale*Real.exp (g*b)^J ∧
      (p.height:ℝ) ≤ (q.height:ℝ)+(J:ℝ)*q.scale*Real.exp (g*b)^J*Real.exp (χ*b) := by
  induction n with
  | zero => simpa only [episodeRun,episodeSteps,pow_zero,mul_one,Nat.cast_zero,zero_mul,add_zero] using ⟨hq,le_rfl,le_rfl⟩
  | succ n ih =>
    dsimp only at ih ⊢
    rw [episodeRun,episodeSteps]
    by_cases hr : EpisodeReady e f r sfloor N (episodeRun e f hef r fexp g χ b sfloor N q ω n)
    · rw [ite_eq_left hr,ite_eq_left hr]
      let p := episodeRun e f hef r fexp g χ b sfloor N q ω n
      let J := episodeSteps e f hef r fexp g χ b sfloor N q ω n
      have hE : 1 ≤ Real.exp (g*b) := Real.one_le_exp_iff.mpr (mul_nonneg hg hb)
      have hpow : Real.exp (g*b)^J ≤ Real.exp (g*b)^(J+1) := by
        rw [pow_succ]
        exact le_mul_of_one_le_right (by positivity) hE
      refine ⟨episodeStageScale_pos e f r fexp g χ b N p ω ih.1,?_,?_⟩
      · change episodeStageScale e f r fexp g χ b N p ω ≤ _
        calc
          _ ≤ p.scale*Real.exp (g*b) := episodeStageScale_le e f r fexp g χ b N p ω hf hg hb ih.1.le
          _ ≤ (q.scale*Real.exp (g*b)^J)*Real.exp (g*b) := mul_le_mul_of_nonneg_right ih.2.1 (Real.exp_pos _).le
          _ = q.scale*Real.exp (g*b)^(J+1) := by rw [pow_succ,mul_assoc]
      · rw [episodeStageNext_height,Nat.cast_add]
        have hl := episodeStageLength_le e f r fexp g χ b N p ω ih.1.le
        have hlq := mul_le_mul_of_nonneg_right ih.2.1 (Real.exp_pos (χ*b)).le
        have hunit : (p.height:ℝ)+(episodeStageLength e f r fexp g χ b N p ω : ℝ) ≤
            (q.height:ℝ)+((J:ℝ)+1)*q.scale*Real.exp (g*b)^J*Real.exp (χ*b) := by
          dsimp only [p,J] at hl hlq ⊢
          nlinarith [ih.2.2]
        apply hunit.trans
        rw [Nat.cast_add,Nat.cast_one]
        exact add_le_add_right (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hpow (by positivity : 0 ≤ ((J:ℝ)+1)*q.scale))
          (Real.exp_pos _).le) _
    · simpa only [ite_eq_right hr,add_zero] using ih

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal Classical
namespace DirectionalTransience
namespace EpisodeLedger
variable {d k : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
  (r : ℝ → ℝ) (fexp g χ b sfloor : ℝ) (N : ℕ)
  (q : EpisodeState (k:=k) e f r) (ω : Environment d)

noncomputable def scale : ℕ → ℝ
  | 0 => q.scale
  | n+1 =>
    let p := episodeRun e f hef r fexp g χ b sfloor N q ω n
    if EpisodeReady e f r sfloor N p then
      if episodeStageGrows e f r fexp g χ b N p ω then
        scale n * Real.exp (g*b)
      else if episodeStageFails e f r fexp g χ b N p ω then
        scale n * Real.exp (-fexp*b)
      else scale n
    else scale n

local notation "R" => episodeRun e f hef r fexp g χ b sfloor N q ω
local notation "A" => scale e f hef r fexp g χ b sfloor N q ω
local notation "Grow" => episodeStageGrows e f r fexp g χ b N
local notation "Fail" => episodeStageFails e f r fexp g χ b N
local notation "Ready" => EpisodeReady e f r sfloor N

lemma scale_pos (hq : 0 < q.scale) (n : ℕ) : 0 < A n := by
  induction n with
  | zero => exact hq
  | succ n ih => dsimp only [scale]; split; split; positivity; split <;> positivity; exact ih

lemma scale_agrees (n : ℕ) (hn : (R n).height < N) : A n=(R n).scale := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [episodeRun] at hn ⊢
    rw [scale]
    by_cases hr : Ready (R n)
    · simp only [ite_eq_left hr] at hn ⊢
      rw [ih hr.1]
      change (if Grow (R n) ω then (R n).scale*Real.exp (g*b) else
        if Fail (R n) ω then (R n).scale*Real.exp (-fexp*b) else (R n).scale) =
          episodeStageScale e f r fexp g χ b N (R n) ω
      unfold episodeStageScale
      by_cases hg : Grow (R n) ω
      · simp only [ite_eq_left hg]
      · rw [ite_eq_right hg,ite_eq_right hg]
        by_cases hf : Fail (R n) ω
        · rw [ite_eq_left hf]
        · have ht := episodeStage_incomplete_terminal e f hef r fexp g χ b N (R n) ω hr.1.le hf hg
          omega
    · simp only [ite_eq_right hr] at hn ⊢
      exact ih hn

lemma scale_le (hq : 0 < q.scale) (hqcap : q.scale ≤ max sfloor (N:ℝ))
    (hqN : q.height ≤ N) (hf : 0 ≤ fexp) (hb : 0 ≤ b)
    (hH : ∀ s, sfloor ≤ s → s*Real.exp (g*b) ≤ (episodeStageH χ b s : ℝ)) (n : ℕ) :
    A n ≤ max sfloor (N:ℝ) := by
  induction n with
  | zero => exact hqcap
  | succ n ih =>
    rw [scale]
    by_cases hr : Ready (R n)
    · rw [ite_eq_left hr]
      by_cases hg : Grow (R n) ω
      · rw [ite_eq_left hg,scale_agrees e f hef r fexp g χ b sfloor N q ω n hr.1]
        have hl : episodeStageLength e f r fexp g χ b N (R n) ω ≤ N := by
          have hn := episodeStageNext_le e f hef r fexp g χ b N (R n) ω
            (episodeRun_le e f hef r fexp g χ b sfloor N q ω hqN n)
          rw [episodeStageNext_height] at hn
          omega
        apply (hH _ hr.2).trans
        have he := (episodeStage_grows_iff e f r fexp g χ b N (R n) ω).mp hg
        rw [←he.1]
        exact (show (episodeStageLength e f r fexp g χ b N (R n) ω : ℝ) ≤ (N:ℝ) by exact_mod_cast hl).trans
          (le_max_right _ _)
      · rw [ite_eq_right hg]
        split
        · apply le_trans _ ih
          exact mul_le_of_le_one_right (scale_pos e f hef r fexp g χ b sfloor N q ω hq n).le
            (Real.exp_le_one_iff.mpr (by nlinarith))
        · exact ih
    · rw [ite_eq_right hr]
      exact ih

lemma log_scale (hq : 0 < q.scale) (n : ℕ) :
    Real.log (A n)-Real.log q.scale =
      g*b*(episodeCount e f hef r fexp g χ b sfloor N q ω Grow n : ℝ) -
      fexp*b*(episodeCount e f hef r fexp g χ b sfloor N q ω Fail n : ℝ) := by
  induction n with
  | zero => simp only [scale,episodeCount,Nat.cast_zero,mul_zero,sub_self]
  | succ n ih =>
    rw [scale,episodeCount,episodeCount]
    by_cases hr : Ready (R n)
    · by_cases hg : Grow (R n) ω
      · have hf := ((episodeStage_grows_iff e f r fexp g χ b N (R n) ω).mp hg).2
        simp only [hr,hg,hf,and_self,and_false,ite_true,ite_false,
          Nat.cast_add,Nat.cast_one,add_zero]
        rw [Real.log_mul (ne_of_gt (scale_pos e f hef r fexp g χ b sfloor N q ω hq n)) (Real.exp_ne_zero _),Real.log_exp]
        linarith
      · by_cases hf : Fail (R n) ω
        · simp only [hr,hg,hf,and_self,and_false,ite_true,ite_false,
            Nat.cast_add,Nat.cast_one,add_zero]
          rw [Real.log_mul (ne_of_gt (scale_pos e f hef r fexp g χ b sfloor N q ω hq n)) (Real.exp_ne_zero _),Real.log_exp]
          linarith
        · simpa only [hr,hg,hf,and_false,ite_true,ite_false,add_zero] using ih
    · simpa only [hr,false_and,ite_false,add_zero] using ih

end EpisodeLedger
end DirectionalTransience

end

end OAI
