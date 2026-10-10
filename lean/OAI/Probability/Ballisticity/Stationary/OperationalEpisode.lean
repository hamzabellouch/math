import Mathlib
import OAI.Probability.Ballisticity.Estimates.StageRetention

namespace OAI

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal Classical
namespace DirectionalTransience

structure EpisodeState {d k : ℕ} (e f : Direction d) (r : ℝ  →  ℝ) where
  height : ℕ
  scale : ℝ
  profile : BudgetProfile (k:=k) e f height (r scale)

noncomputable def episodeStageH (χ b s : ℝ) : ℕ := ⌊s*Real.exp (χ*b)⌋₊

noncomputable def episodeStageLength {d k : ℕ} (e f : Direction d) (r : ℝ  →  ℝ)
    (fexp g χ b : ℝ) (N : ℕ) (q : EpisodeState (k:=k) e f r) (ω : Environment d) : ℕ :=
  stageStop e f q.height (r (q.scale*Real.exp (-fexp*b)))
    (r (q.scale*Real.exp (g*b))) ((k:ℝ)*b) (fun _ => q.profile.toLayerProfile)
    (episodeStageH χ b q.scale) (N-q.height) ω

def EpisodeReady {d k : ℕ} (e f : Direction d) (r : ℝ  →  ℝ)
    (sfloor : ℝ) (N : ℕ) (q : EpisodeState (k:=k) e f r) : Prop :=
  q.height<N ∧ sfloor ≤ q.scale

noncomputable def episodeStageGrows {d k : ℕ} (e f : Direction d) (r : ℝ  →  ℝ)
    (fexp g χ b : ℝ) (N : ℕ) (q : EpisodeState (k:=k) e f r) (ω : Environment d) : Prop :=
  episodeStageLength e f r fexp g χ b N q ω=episodeStageH χ b q.scale ∧
    ENNReal.ofReal (Real.exp (-(k:ℝ)*b))  ≤
      stageTestMass e f q.height (r (q.scale*Real.exp (-fexp*b)))
        (r (q.scale*Real.exp (g*b))) (fun _ => q.profile.toLayerProfile)
        (episodeStageH χ b q.scale) (episodeStageLength e f r fexp g χ b N q ω) ω

noncomputable def episodeStageScale {d k : ℕ} (e f : Direction d) (r : ℝ  →  ℝ)
    (fexp g χ b : ℝ) (N : ℕ) (q : EpisodeState (k:=k) e f r) (ω : Environment d) : ℝ :=
  if episodeStageGrows e f r fexp g χ b N q ω
  then q.scale*Real.exp (g*b) else q.scale*Real.exp (-fexp*b)

lemma episodeStageGap {d k : ℕ} (e f : Direction d) (r : ℝ  →  ℝ)
    (fexp g χ b : ℝ) (N : ℕ) (q : EpisodeState (k:=k) e f r) (ω : Environment d) :
    stageRetainedGap e f q.height (r (q.scale*Real.exp (-fexp*b)))
      (r (q.scale*Real.exp (g*b))) ((k:ℝ)*b) (fun _ => q.profile.toLayerProfile)
      (episodeStageH χ b q.scale) (N-q.height) ω=
      r (episodeStageScale e f r fexp g χ b N q ω) := by
  unfold stageRetainedGap episodeStageScale episodeStageGrows episodeStageLength
  dsimp only
  simp only [neg_mul]
  split <;> rfl

noncomputable def episodeStageNext {d k : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (r : ℝ  →  ℝ) (fexp g χ b : ℝ) (N : ℕ)
    (q : EpisodeState (k:=k) e f r) (ω : Environment d) : EpisodeState (k:=k) e f r := by
  let out := stageOutput e f hef q.height (r (q.scale*Real.exp (-fexp*b)))
    (r (q.scale*Real.exp (g*b))) ((k:ℝ)*b) (fun _ => q.profile.toLayerProfile)
    (episodeStageH χ b q.scale) (N-q.height) ω
  refine ⟨q.height+episodeStageLength e f r fexp g χ b N q ω,
    episodeStageScale e f r fexp g χ b N q ω, out.val, out.property.1, ?_⟩
  filter_upwards [out.property.2] with x hx
  constructor
  · simpa only [Nat.cast_add,episodeStageLength] using hx.1
  · have hh := hx.2
    rwa [episodeStageGap] at hh

lemma episodeStageNext_height {d k : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (r : ℝ  →  ℝ) (fexp g χ b : ℝ) (N : ℕ)
    (q : EpisodeState (k:=k) e f r) (ω : Environment d) :
    (episodeStageNext e f hef r fexp g χ b N q ω).height=
      q.height+episodeStageLength e f r fexp g χ b N q ω := rfl

lemma episodeStageNext_le {d k : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (r : ℝ  →  ℝ) (fexp g χ b : ℝ) (N : ℕ)
    (q : EpisodeState (k:=k) e f r) (ω : Environment d) (hq : q.height ≤ N) :
    (episodeStageNext e f hef r fexp g χ b N q ω).height ≤ N := by
  have hs := stageStop_le e f q.height (r (q.scale*Real.exp (-fexp*b)))
    (r (q.scale*Real.exp (g*b))) ((k:ℝ)*b) (fun _ => q.profile.toLayerProfile)
    (episodeStageH χ b q.scale) (N-q.height) ω
  change episodeStageLength e f r fexp g χ b N q ω  ≤  _ at hs
  rw [episodeStageNext_height]
  omega

lemma episodeStageNext_gt {d k : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (r : ℝ  →  ℝ) (fexp g χ b sfloor : ℝ) (N : ℕ)
    (q : EpisodeState (k:=k) e f r) (ω : Environment d)
    (hH : ∀ s, sfloor ≤ s  →  0 < episodeStageH χ b s)
    (hq : EpisodeReady e f r sfloor N q) :
    q.height<(episodeStageNext e f hef r fexp g χ b N q ω).height := by
  rw [episodeStageNext_height]
  exact Nat.lt_add_of_pos_right (stageStop_pos e f q.height _ _ _ _ _ _
    (hH q.scale hq.2) (Nat.sub_pos_of_lt hq.1) ω)

noncomputable def episodeRun {d k : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (r : ℝ  →  ℝ) (fexp g χ b sfloor : ℝ) (N : ℕ)
    (q : EpisodeState (k:=k) e f r) (ω : Environment d) : ℕ  →  EpisodeState (k:=k) e f r
  | 0 => q
  | n+1 => let p := episodeRun e f hef r fexp g χ b sfloor N q ω n
    if EpisodeReady e f r sfloor N p then episodeStageNext e f hef r fexp g χ b N p ω else p

lemma episodeRun_le {d k : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (r : ℝ  →  ℝ) (fexp g χ b sfloor : ℝ) (N : ℕ)
    (q : EpisodeState (k:=k) e f r) (ω : Environment d) (hq : q.height ≤ N) (n : ℕ) :
    (episodeRun e f hef r fexp g χ b sfloor N q ω n).height ≤ N := by
  induction n with
  | zero => exact hq
  | succ n ih =>
    rw [episodeRun]
    split
    · exact episodeStageNext_le e f hef r fexp g χ b N _ ω ih
    · exact ih

lemma episodeRun_progress {d k : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (r : ℝ  →  ℝ) (fexp g χ b sfloor : ℝ) (N : ℕ)
    (q : EpisodeState (k:=k) e f r) (ω : Environment d)
    (hH : ∀ s, sfloor ≤ s  →  0 < episodeStageH χ b s) (n : ℕ)
    (hready : EpisodeReady e f r sfloor N (episodeRun e f hef r fexp g χ b sfloor N q ω n)) :
    q.height+n ≤ (episodeRun e f hef r fexp g χ b sfloor N q ω n).height := by
  induction n with
  | zero => exact le_rfl
  | succ n ih =>
    simp only [episodeRun] at hready ⊢
    by_cases hp : EpisodeReady e f r sfloor N (episodeRun e f hef r fexp g χ b sfloor N q ω n)
    · rw [ite_eq_left hp] at hready ⊢
      have ht := episodeStageNext_gt e f hef r fexp g χ b sfloor N _ ω hH hp
      have hi := ih hp
      omega
    · rw [ite_eq_right hp] at hready
      exact False.elim (hp hready)

theorem episodeRun_terminates {d k : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (r : ℝ  →  ℝ) (fexp g χ b sfloor : ℝ) (N : ℕ)
    (q : EpisodeState (k:=k) e f r) (ω : Environment d) (hq : q.height ≤ N)
    (hH : ∀ s, sfloor ≤ s  →  0 < episodeStageH χ b s) :
    ¬EpisodeReady e f r sfloor N (episodeRun e f hef r fexp g χ b sfloor N q ω N) := by
  intro hr
  have hp := episodeRun_progress e f hef r fexp g χ b sfloor N q ω hH N hr
  have hu := episodeRun_le e f hef r fexp g χ b sfloor N q ω hq N
  have hn := hr.1
  omega

end DirectionalTransience

end

end OAI
