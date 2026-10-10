import Mathlib
import OAI.Probability.Ballisticity.Stationary.OperationalEpisode

namespace OAI

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Classical
namespace DirectionalTransience

lemma episodeStageNext_retained {d k : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (r : ℝ → ℝ) (hr : Monotone r) (fexp g χ b sfloor : ℝ) (N : ℕ)
    (hf : 0 ≤ fexp) (hb : 0 ≤ b) (hsfloor : 0 < sfloor)
    (q : EpisodeState (k:=k) e f r) (ω : Environment d)
    (hH : ∀ s, sfloor ≤ s → 0 < episodeStageH χ b s)
    (hq : EpisodeReady e f r sfloor N q)
    (κ : ℝ≥0) (hκ : ∀ y, κ ≤ (ω y).val e) :
    ((κ:ℝ≥0∞)^k * ENNReal.ofReal (Real.exp (-((k:ℝ)*b)))) •
      (episodeStageNext e f hef r fexp g χ b N q ω).profile.val ≤
      rawTupleMixture (realPosition (step e)) (episodeStageLength e f r fexp g χ b N q ω)
        q.profile.val ω := by
  have hs : 0 ≤ q.scale := hsfloor.le.trans hq.2
  have he : Real.exp (-fexp*b) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  have hg : r (q.scale*Real.exp (-fexp*b)) ≤ r q.scale :=
    hr (by simpa only [mul_one] using mul_le_mul_of_nonneg_left he hs)
  have hp : ∀ᵐ x ∂q.profile.val,TupleSeparated f (r (q.scale*Real.exp (-fexp*b))) x :=
    q.profile.property.2.mono fun x hx => tupleSeparated_mono f hg x hx.2
  have hm := stageRetainedMass_lower e f q.height (r (q.scale*Real.exp (-fexp*b)))
    (r (q.scale*Real.exp (g*b))) ((k:ℝ)*b) (fun _ => q.profile.toLayerProfile)
    (episodeStageH χ b q.scale) (N-q.height) (hH _ hq.2) (Nat.sub_pos_of_lt hq.1)
    (mul_nonneg (Nat.cast_nonneg _) hb) ω hp κ hκ
  have ho := stageOutput_retained_le e f hef q.height (r (q.scale*Real.exp (-fexp*b)))
    (r (q.scale*Real.exp (g*b))) ((k:ℝ)*b) (fun _ => q.profile.toLayerProfile)
    (episodeStageH χ b q.scale) (N-q.height) ω
  have hi : ((κ:ℝ≥0∞)^k * ENNReal.ofReal (Real.exp (-((k:ℝ)*b)))) •
      (episodeStageNext e f hef r fexp g χ b N q ω).profile.val ≤
      stageRetainedMass e f q.height (r (q.scale*Real.exp (-fexp*b)))
        (r (q.scale*Real.exp (g*b))) ((k:ℝ)*b) (fun _ => q.profile.toLayerProfile)
        (episodeStageH χ b q.scale) (N-q.height) ω •
        (episodeStageNext e f hef r fexp g χ b N q ω).profile.val := by
    intro U
    simpa only [Measure.smul_apply,smul_eq_mul,mul_comm] using
      mul_le_mul_right hm ((episodeStageNext e f hef r fexp g χ b N q ω).profile.val U)
  exact hi.trans ho

noncomputable def episodeSteps {d k : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (r : ℝ → ℝ) (fexp g χ b sfloor : ℝ) (N : ℕ)
    (q : EpisodeState (k:=k) e f r) (ω : Environment d) : ℕ → ℕ
  | 0 => 0
  | n+1 => episodeSteps e f hef r fexp g χ b sfloor N q ω n +
      if EpisodeReady e f r sfloor N (episodeRun e f hef r fexp g χ b sfloor N q ω n) then 1 else 0

lemma episodeRun_height_mono {d k : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (r : ℝ → ℝ) (fexp g χ b sfloor : ℝ) (N : ℕ)
    (q : EpisodeState (k:=k) e f r) (ω : Environment d) (n : ℕ) :
    q.height ≤ (episodeRun e f hef r fexp g χ b sfloor N q ω n).height := by
  induction n with
  | zero => exact le_rfl
  | succ n ih =>
    rw [episodeRun]
    split
    · rw [episodeStageNext_height]
      exact ih.trans (Nat.le_add_right _ _)
    · exact ih

def episodeMeasure {d k : ℕ} {e f : Direction d} {r : ℝ → ℝ}
    (q : EpisodeState (k:=k) e f r) : Measure (Fin k → Lattice d) := q.profile.val

theorem episodeRun_retained {d k : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (r : ℝ → ℝ) (hr : Monotone r) (fexp g χ b sfloor : ℝ) (N : ℕ)
    (hf : 0 ≤ fexp) (hb : 0 ≤ b) (hsfloor : 0 < sfloor)
    (q : EpisodeState (k:=k) e f r) (ω : Environment d)
    (hH : ∀ s, sfloor ≤ s → 0 < episodeStageH χ b s)
    (κ : ℝ≥0) (hκ : ∀ y, κ ≤ (ω y).val e) (n : ℕ) :
    ((κ:ℝ≥0∞)^k * ENNReal.ofReal (Real.exp (-((k:ℝ)*b))))^
        (episodeSteps e f hef r fexp g χ b sfloor N q ω n) •
      (episodeRun e f hef r fexp g χ b sfloor N q ω n).profile.val ≤
      rawTupleMixture (realPosition (step e))
        ((episodeRun e f hef r fexp g χ b sfloor N q ω n).height-q.height)
        q.profile.val ω := by
  change ((κ:ℝ≥0∞)^k * ENNReal.ofReal (Real.exp (-((k:ℝ)*b))))^
      (episodeSteps e f hef r fexp g χ b sfloor N q ω n) •
      episodeMeasure (episodeRun e f hef r fexp g χ b sfloor N q ω n) ≤ _
  induction n with
  | zero => simp only [episodeMeasure,episodeSteps,episodeRun,pow_zero,one_smul,Nat.sub_self,rawTupleMixture_zero,le_refl]
  | succ n ih =>
    rw [episodeSteps,episodeRun]
    by_cases hp : EpisodeReady e f r sfloor N (episodeRun e f hef r fexp g χ b sfloor N q ω n)
    · rw [ite_eq_left hp,ite_eq_left hp,pow_succ,mul_smul]
      have ht := episodeRun_height_mono e f hef r fexp g χ b sfloor N q ω n
      have hs := smul_le_smul_left
        (((κ:ℝ≥0∞)^k * ENNReal.ofReal (Real.exp (-((k:ℝ)*b))))^
          (episodeSteps e f hef r fexp g χ b sfloor N q ω n))
        (episodeStageNext_retained e f hef r hr fexp g χ b sfloor N hf hb hsfloor _ ω hH hp κ hκ)
      rw [←rawTupleMixture_smul] at hs
      have hm := rawTupleMixture_mono (realPosition (step e))
        (episodeStageLength e f r fexp g χ b N (episodeRun e f hef r fexp g χ b sfloor N q ω n) ω) ω ih
      have hc := rawTupleMixture_comp_le e
        ((episodeRun e f hef r fexp g χ b sfloor N q ω n).height-q.height)
        (episodeStageLength e f r fexp g χ b N (episodeRun e f hef r fexp g χ b sfloor N q ω n) ω)
        q.profile.val ω
      have he : (episodeStageNext e f hef r fexp g χ b N
          (episodeRun e f hef r fexp g χ b sfloor N q ω n) ω).height-q.height =
          (episodeRun e f hef r fexp g χ b sfloor N q ω n).height-q.height +
            episodeStageLength e f r fexp g χ b N (episodeRun e f hef r fexp g χ b sfloor N q ω n) ω := by
        rw [episodeStageNext_height]
        omega
      convert hs.trans (hm.trans hc) using 1
      · rfl
      · exact congrArg (fun h => rawTupleMixture (realPosition (step e)) h q.profile.val ω) he
    · simp only [ite_eq_right hp,add_zero]
      exact ih

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Classical
namespace DirectionalTransience

def StageRadiusOrder (r : ℝ → ℝ) (f b sfloor : ℝ) : Prop :=
  ∀ s, sfloor ≤ s → r (s*Real.exp (-f*b)) ≤ r s

lemma episodeStageNext_retained_local {d k : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (r : ℝ → ℝ) (fexp g χ b sfloor : ℝ) (hr : StageRadiusOrder r fexp b sfloor) (N : ℕ)
    (_ : 0 ≤ fexp) (hb : 0 ≤ b) (_ : 0 < sfloor)
    (q : EpisodeState (k:=k) e f r) (ω : Environment d)
    (hH : ∀ s, sfloor ≤ s → 0 < episodeStageH χ b s)
    (hq : EpisodeReady e f r sfloor N q)
    (κ : ℝ≥0) (hκ : ∀ y, κ ≤ (ω y).val e) :
    ((κ:ℝ≥0∞)^k * ENNReal.ofReal (Real.exp (-((k:ℝ)*b)))) •
      (episodeStageNext e f hef r fexp g χ b N q ω).profile.val ≤
      rawTupleMixture (realPosition (step e)) (episodeStageLength e f r fexp g χ b N q ω)
        q.profile.val ω := by
  have hg : r (q.scale*Real.exp (-fexp*b)) ≤ r q.scale := hr q.scale hq.2
  have hp : ∀ᵐ x ∂q.profile.val,TupleSeparated f (r (q.scale*Real.exp (-fexp*b))) x :=
    q.profile.property.2.mono fun x hx => tupleSeparated_mono f hg x hx.2
  have hm := stageRetainedMass_lower e f q.height (r (q.scale*Real.exp (-fexp*b)))
    (r (q.scale*Real.exp (g*b))) ((k:ℝ)*b) (fun _ => q.profile.toLayerProfile)
    (episodeStageH χ b q.scale) (N-q.height) (hH _ hq.2) (Nat.sub_pos_of_lt hq.1)
    (mul_nonneg (Nat.cast_nonneg _) hb) ω hp κ hκ
  have ho := stageOutput_retained_le e f hef q.height (r (q.scale*Real.exp (-fexp*b)))
    (r (q.scale*Real.exp (g*b))) ((k:ℝ)*b) (fun _ => q.profile.toLayerProfile)
    (episodeStageH χ b q.scale) (N-q.height) ω
  have hi : ((κ:ℝ≥0∞)^k * ENNReal.ofReal (Real.exp (-((k:ℝ)*b)))) •
      (episodeStageNext e f hef r fexp g χ b N q ω).profile.val ≤
      stageRetainedMass e f q.height (r (q.scale*Real.exp (-fexp*b)))
        (r (q.scale*Real.exp (g*b))) ((k:ℝ)*b) (fun _ => q.profile.toLayerProfile)
        (episodeStageH χ b q.scale) (N-q.height) ω •
        (episodeStageNext e f hef r fexp g χ b N q ω).profile.val := by
    intro U
    simpa only [Measure.smul_apply,smul_eq_mul,mul_comm] using
      mul_le_mul_right hm ((episodeStageNext e f hef r fexp g χ b N q ω).profile.val U)
  exact hi.trans ho

theorem episodeRun_retained_local {d k : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (r : ℝ → ℝ) (fexp g χ b sfloor : ℝ) (hr : StageRadiusOrder r fexp b sfloor) (N : ℕ)
    (hf : 0 ≤ fexp) (hb : 0 ≤ b) (hsfloor : 0 < sfloor)
    (q : EpisodeState (k:=k) e f r) (ω : Environment d)
    (hH : ∀ s, sfloor ≤ s → 0 < episodeStageH χ b s)
    (κ : ℝ≥0) (hκ : ∀ y, κ ≤ (ω y).val e) (n : ℕ) :
    ((κ:ℝ≥0∞)^k * ENNReal.ofReal (Real.exp (-((k:ℝ)*b))))^
        (episodeSteps e f hef r fexp g χ b sfloor N q ω n) •
      (episodeRun e f hef r fexp g χ b sfloor N q ω n).profile.val ≤
      rawTupleMixture (realPosition (step e))
        ((episodeRun e f hef r fexp g χ b sfloor N q ω n).height-q.height)
        q.profile.val ω := by
  change ((κ:ℝ≥0∞)^k * ENNReal.ofReal (Real.exp (-((k:ℝ)*b))))^
      (episodeSteps e f hef r fexp g χ b sfloor N q ω n) •
      episodeMeasure (episodeRun e f hef r fexp g χ b sfloor N q ω n) ≤ _
  induction n with
  | zero => simp only [episodeMeasure,episodeSteps,episodeRun,pow_zero,one_smul,Nat.sub_self,rawTupleMixture_zero,le_refl]
  | succ n ih =>
    rw [episodeSteps,episodeRun]
    by_cases hp : EpisodeReady e f r sfloor N (episodeRun e f hef r fexp g χ b sfloor N q ω n)
    · rw [ite_eq_left hp,ite_eq_left hp,pow_succ,mul_smul]
      have ht := episodeRun_height_mono e f hef r fexp g χ b sfloor N q ω n
      have hs := smul_le_smul_left
        (((κ:ℝ≥0∞)^k * ENNReal.ofReal (Real.exp (-((k:ℝ)*b))))^
          (episodeSteps e f hef r fexp g χ b sfloor N q ω n))
        (episodeStageNext_retained_local e f hef r fexp g χ b sfloor hr N hf hb hsfloor _ ω hH hp κ hκ)
      rw [←rawTupleMixture_smul] at hs
      have hm := rawTupleMixture_mono (realPosition (step e))
        (episodeStageLength e f r fexp g χ b N (episodeRun e f hef r fexp g χ b sfloor N q ω n) ω) ω ih
      have hc := rawTupleMixture_comp_le e
        ((episodeRun e f hef r fexp g χ b sfloor N q ω n).height-q.height)
        (episodeStageLength e f r fexp g χ b N (episodeRun e f hef r fexp g χ b sfloor N q ω n) ω)
        q.profile.val ω
      have he : (episodeStageNext e f hef r fexp g χ b N
          (episodeRun e f hef r fexp g χ b sfloor N q ω n) ω).height-q.height =
          (episodeRun e f hef r fexp g χ b sfloor N q ω n).height-q.height +
            episodeStageLength e f r fexp g χ b N (episodeRun e f hef r fexp g χ b sfloor N q ω n) ω := by
        rw [episodeStageNext_height]
        omega
      convert hs.trans (hm.trans hc) using 1
      · rfl
      · exact congrArg (fun h => rawTupleMixture (realPosition (step e)) h q.profile.val ω) he
    · simp only [ite_eq_right hp,add_zero]
      exact ih

end DirectionalTransience

end

end OAI
