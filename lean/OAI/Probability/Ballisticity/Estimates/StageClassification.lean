import Mathlib
import OAI.Probability.Ballisticity.Stationary.EpisodeRetention

namespace OAI

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal Classical
namespace DirectionalTransience

noncomputable def episodeStageFails {d k : ℕ} (e f : Direction d)
    (r : ℝ → ℝ) (fexp g χ b : ℝ) (N : ℕ) (q : EpisodeState (k:=k) e f r) (ω : Environment d) : Prop :=
  stageTestMass e f q.height (r (q.scale*Real.exp (-fexp*b)))
    (r (q.scale*Real.exp (g*b))) (fun _ => q.profile.toLayerProfile)
    (episodeStageH χ b q.scale) (episodeStageLength e f r fexp g χ b N q ω) ω <
    ENNReal.ofReal (Real.exp (-((k:ℝ)*b)))

lemma episodeStage_grows_iff {d k : ℕ} (e f : Direction d)
    (r : ℝ → ℝ) (fexp g χ b : ℝ) (N : ℕ) (q : EpisodeState (k:=k) e f r) (ω : Environment d) :
    episodeStageGrows e f r fexp g χ b N q ω ↔
      episodeStageLength e f r fexp g χ b N q ω=episodeStageH χ b q.scale ∧
        ¬episodeStageFails e f r fexp g χ b N q ω := by
  simp only [episodeStageGrows,episodeStageFails,not_lt,neg_mul]

lemma episodeStage_not_fail_length {d k : ℕ} (e f : Direction d)
    (r : ℝ → ℝ) (fexp g χ b : ℝ) (N : ℕ) (q : EpisodeState (k:=k) e f r) (ω : Environment d)
    (hf : ¬episodeStageFails e f r fexp g χ b N q ω) :
    episodeStageLength e f r fexp g χ b N q ω = min (episodeStageH χ b q.scale) (N-q.height) := by
  have hu : episodeStageLength e f r fexp g χ b N q ω ≤ min (episodeStageH χ b q.scale) (N-q.height) :=
    hittingBtwn_le ω
  apply le_antisymm hu
  by_contra hn
  have hl := lt_of_not_ge hn
  exact hf (hittingBtwn_mem_set_of_hittingBtwn_lt hl)

lemma episodeStage_incomplete_terminal {d k : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (r : ℝ → ℝ) (fexp g χ b : ℝ) (N : ℕ) (q : EpisodeState (k:=k) e f r) (ω : Environment d)
    (hq : q.height ≤ N) (hf : ¬episodeStageFails e f r fexp g χ b N q ω)
    (hg : ¬episodeStageGrows e f r fexp g χ b N q ω) :
    (episodeStageNext e f hef r fexp g χ b N q ω).height=N := by
  have hl := episodeStage_not_fail_length e f r fexp g χ b N q ω hf
  have hn : episodeStageLength e f r fexp g χ b N q ω ≠ episodeStageH χ b q.scale := by
    intro he
    exact hg ((episodeStage_grows_iff e f r fexp g χ b N q ω).mpr ⟨he,hf⟩)
  rw [episodeStageNext_height]
  omega

noncomputable def episodeCount {d k : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (r : ℝ → ℝ) (fexp g χ b sfloor : ℝ) (N : ℕ)
    (q : EpisodeState (k:=k) e f r) (ω : Environment d)
    (test : EpisodeState (k:=k) e f r → Environment d → Prop) : ℕ → ℕ
  | 0 => 0
  | n+1 => episodeCount e f hef r fexp g χ b sfloor N q ω test n +
    if EpisodeReady e f r sfloor N (episodeRun e f hef r fexp g χ b sfloor N q ω n) ∧
      test (episodeRun e f hef r fexp g χ b sfloor N q ω n) ω then 1 else 0

lemma episodeSteps_le_height {d k : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (r : ℝ → ℝ) (fexp g χ b sfloor : ℝ) (N : ℕ)
    (q : EpisodeState (k:=k) e f r) (ω : Environment d)
    (hH : ∀ s, sfloor ≤ s → 0 < episodeStageH χ b s) (n : ℕ) :
    q.height+episodeSteps e f hef r fexp g χ b sfloor N q ω n ≤
      (episodeRun e f hef r fexp g χ b sfloor N q ω n).height := by
  induction n with
  | zero => simp only [episodeRun,episodeSteps,add_zero,le_refl]
  | succ n ih =>
    rw [episodeSteps,episodeRun]
    by_cases hp : EpisodeReady e f r sfloor N (episodeRun e f hef r fexp g χ b sfloor N q ω n)
    · rw [ite_eq_left hp,ite_eq_left hp]
      have hh := episodeStageNext_gt e f hef r fexp g χ b sfloor N _ ω hH hp
      omega
    · simpa only [ite_eq_right hp,add_zero] using ih

end DirectionalTransience

end

end OAI
