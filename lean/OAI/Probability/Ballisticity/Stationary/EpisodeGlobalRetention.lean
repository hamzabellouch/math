import Mathlib
import OAI.Probability.Ballisticity.Stationary.EpisodeInjection

namespace OAI

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators Classical
namespace DirectionalTransience

noncomputable def episodeStageCount {d k : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (r : ℝ → ℝ) (fexp g χ b sfloor : ℝ) (hR : 0 ≤ r sfloor) (N t : ℕ)
    (ω : Environment d) : ℕ :=
  episodeSteps e f hef r fexp g χ b sfloor N (episodeInitial (k:=k) e f hef r sfloor hR t ω) ω N

theorem episodeFinal_global_retained {d k : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (r : ℝ → ℝ) (hr : Monotone r) (fexp g χ b sfloor : ℝ) (hR : 0 ≤ r sfloor) (N t : ℕ)
    (hf : 0 ≤ fexp) (hb : 0 ≤ b) (hsfloor : 0 < sfloor)
    (ω : Environment d) (hH : ∀ s, sfloor ≤ s → 0 < episodeStageH χ b s)
    (κ : ℝ≥0) (hκ1 : κ ≤ 1) (hκ : ∀ y u, κ ≤ (ω y).1 u) :
    ((crossingQuenched (realPosition (step e)) 0 t ω)^k *
      (κ : ℝ≥0∞)^(k*(BoundedInjection.injectionMultiplier (r sfloor)*k+1)) *
      ((κ:ℝ≥0∞)^k * ENNReal.ofReal (Real.exp (-((k:ℝ)*b))))^
        (episodeStageCount (k:=k) e f hef r fexp g χ b sfloor hR N t ω)) •
      episodeMeasure (episodeFinal (k:=k) e f hef r fexp g χ b sfloor hR N t ω) ≤
      rawTupleEndpointLaw (realPosition (step e))
        (episodeFinal (k:=k) e f hef r fexp g χ b sfloor hR N t ω).height ω (fun _ : Fin k => 0) := by
  let q := episodeInitial (k:=k) e f hef r sfloor hR t ω
  let p := episodeFinal (k:=k) e f hef r fexp g χ b sfloor hR N t ω
  let c := (crossingQuenched (realPosition (step e)) 0 t ω)^k *
      (κ : ℝ≥0∞)^(k*(BoundedInjection.injectionMultiplier (r sfloor)*k+1))
  have hi : c • episodeMeasure q ≤ rawTupleEndpointLaw (realPosition (step e)) (t+1) ω (fun _ : Fin k => 0) := by
    rw [mul_smul]
    exact episodeInitial_retained e f hef r sfloor hR t ω κ hκ1 hκ
  have hs := episodeRun_retained e f hef r hr fexp g χ b sfloor N hf hb hsfloor q ω hH κ (fun y => hκ y e) N
  have hs := smul_le_smul_left c hs
  rw [←rawTupleMixture_smul] at hs
  have hm := rawTupleMixture_mono (realPosition (step e)) (p.height-q.height) ω hi
  have hc := rawTupleEndpointLaw_comp_le e (t+1) (p.height-q.height) ω (fun _ : Fin k => 0)
  have ht : t+1 ≤ p.height := episodeRun_height_mono e f hef r fexp g χ b sfloor N q ω N
  have hh : (t+1)+(p.height-q.height)=p.height := by change (t+1)+(p.height-(t+1))=p.height; omega
  rw [hh] at hc
  simpa only [c,p,q,episodeStageCount,episodeFinal,episodeMeasure,mul_smul] using hs.trans (hm.trans hc)

lemma rawTupleEndpointLaw_origin_mass {d k : ℕ} (e : Direction d) (H : ℕ) (ω : Environment d) :
    rawTupleEndpointLaw (realPosition (step e)) H ω (fun _ : Fin k => 0) Set.univ =
      (crossingQuenched (realPosition (step e)) 0 H ω)^k := by
  have hh := congrArg (fun μ : Measure (Fin k → Lattice d) => μ Set.univ)
    (globalTupleProfile_mass (k:=k) e H ω)
  simpa only [Measure.smul_apply,smul_eq_mul,measure_univ,mul_one] using hh.symm

lemma episode_survival_lower {d k : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (r : ℝ → ℝ) (hr : Monotone r) (fexp g χ b sfloor : ℝ) (hR : 0 ≤ r sfloor) (N t : ℕ)
    (hf : 0 ≤ fexp) (hb : 0 ≤ b) (hsfloor : 0 < sfloor)
    (ω : Environment d) (hH : ∀ s, sfloor ≤ s → 0 < episodeStageH χ b s)
    (κ : ℝ≥0) (hκ1 : κ ≤ 1) (hκ : ∀ y u, κ ≤ (ω y).1 u) :
    (crossingQuenched (realPosition (step e)) 0 t ω)^k *
      (κ : ℝ≥0∞)^(k*(BoundedInjection.injectionMultiplier (r sfloor)*k+1)) *
      ((κ:ℝ≥0∞)^k * ENNReal.ofReal (Real.exp (-((k:ℝ)*b))))^
        (episodeStageCount (k:=k) e f hef r fexp g χ b sfloor hR N t ω) ≤
      (crossingQuenched (realPosition (step e)) 0
        (episodeFinal (k:=k) e f hef r fexp g χ b sfloor hR N t ω).height ω)^k := by
  have hh := episodeFinal_global_retained (k:=k) e f hef r hr fexp g χ b sfloor hR N t hf hb hsfloor ω hH κ hκ1 hκ Set.univ
  simpa only [Measure.smul_apply,smul_eq_mul,episodeMeasure,measure_univ,mul_one,
    rawTupleEndpointLaw_origin_mass] using hh

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Classical
namespace DirectionalTransience
theorem episodeFinal_global_retained_local {d k : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (r : ℝ → ℝ) (fexp g χ b sfloor : ℝ) (hr : StageRadiusOrder r fexp b sfloor) (hR : 0 ≤ r sfloor) (N t : ℕ)
    (hf : 0 ≤ fexp) (hb : 0 ≤ b) (hsfloor : 0 < sfloor)
    (ω : Environment d) (hH : ∀ s, sfloor ≤ s → 0 < episodeStageH χ b s)
    (κ : ℝ≥0) (hκ1 : κ ≤ 1) (hκ : ∀ y u, κ ≤ (ω y).1 u) :
    ((crossingQuenched (realPosition (step e)) 0 t ω)^k *
      (κ : ℝ≥0∞)^(k*(BoundedInjection.injectionMultiplier (r sfloor)*k+1)) *
      ((κ:ℝ≥0∞)^k * ENNReal.ofReal (Real.exp (-((k:ℝ)*b))))^
        (episodeStageCount (k:=k) e f hef r fexp g χ b sfloor hR N t ω)) •
      episodeMeasure (episodeFinal (k:=k) e f hef r fexp g χ b sfloor hR N t ω) ≤
      rawTupleEndpointLaw (realPosition (step e))
        (episodeFinal (k:=k) e f hef r fexp g χ b sfloor hR N t ω).height ω (fun _ : Fin k => 0) := by
  let q := episodeInitial (k:=k) e f hef r sfloor hR t ω
  let p := episodeFinal (k:=k) e f hef r fexp g χ b sfloor hR N t ω
  let c := (crossingQuenched (realPosition (step e)) 0 t ω)^k *
      (κ : ℝ≥0∞)^(k*(BoundedInjection.injectionMultiplier (r sfloor)*k+1))
  have hi : c • episodeMeasure q ≤ rawTupleEndpointLaw (realPosition (step e)) (t+1) ω (fun _ : Fin k => 0) := by
    rw [mul_smul]
    exact episodeInitial_retained e f hef r sfloor hR t ω κ hκ1 hκ
  have hs := episodeRun_retained_local e f hef r fexp g χ b sfloor hr N hf hb hsfloor q ω hH κ (fun y => hκ y e) N
  have hs := smul_le_smul_left c hs
  rw [←rawTupleMixture_smul] at hs
  have hm := rawTupleMixture_mono (realPosition (step e)) (p.height-q.height) ω hi
  have hc := rawTupleEndpointLaw_comp_le e (t+1) (p.height-q.height) ω (fun _ : Fin k => 0)
  have ht : t+1 ≤ p.height := episodeRun_height_mono e f hef r fexp g χ b sfloor N q ω N
  have hh : (t+1)+(p.height-q.height)=p.height := by change (t+1)+(p.height-(t+1))=p.height; omega
  rw [hh] at hc
  simpa only [c,p,q,episodeStageCount,episodeFinal,episodeMeasure,mul_smul] using hs.trans (hm.trans hc)

lemma episode_survival_lower_local {d k : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (r : ℝ → ℝ) (fexp g χ b sfloor : ℝ) (hr : StageRadiusOrder r fexp b sfloor) (hR : 0 ≤ r sfloor) (N t : ℕ)
    (hf : 0 ≤ fexp) (hb : 0 ≤ b) (hsfloor : 0 < sfloor)
    (ω : Environment d) (hH : ∀ s, sfloor ≤ s → 0 < episodeStageH χ b s)
    (κ : ℝ≥0) (hκ1 : κ ≤ 1) (hκ : ∀ y u, κ ≤ (ω y).1 u) :
    (crossingQuenched (realPosition (step e)) 0 t ω)^k *
      (κ : ℝ≥0∞)^(k*(BoundedInjection.injectionMultiplier (r sfloor)*k+1)) *
      ((κ:ℝ≥0∞)^k * ENNReal.ofReal (Real.exp (-((k:ℝ)*b))))^
        (episodeStageCount (k:=k) e f hef r fexp g χ b sfloor hR N t ω) ≤
      (crossingQuenched (realPosition (step e)) 0
        (episodeFinal (k:=k) e f hef r fexp g χ b sfloor hR N t ω).height ω)^k := by
  have hh := episodeFinal_global_retained_local (k:=k) e f hef r fexp g χ b sfloor hr hR N t hf hb hsfloor ω hH κ hκ1 hκ Set.univ
  simpa only [Measure.smul_apply,smul_eq_mul,episodeMeasure,measure_univ,mul_one,
    rawTupleEndpointLaw_origin_mass] using hh

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Classical
namespace DirectionalTransience

lemma coordinate_survival_lower {d : ℕ} (e : Direction d) (ω : Environment d)
    (κ : ℝ≥0) (hκ : ∀ y, κ ≤ (ω y).1 e) (H : ℕ) :
    (κ : ℝ≥0∞)^H ≤ crossingQuenched (realPosition (step e)) 0 H ω := by
  induction H with
  | zero => simp [crossingQuenched_zero]
  | succ H ih =>
    have hh := crossingQuenched_lower_step (realPosition (step e)) ω 0 e hκ (H:=H) (by positivity)
    rw [signed_direction_unit] at hh
    simpa only [Nat.cast_add,Nat.cast_one,pow_succ',Nat.succ_eq_add_one] using
      (mul_le_mul_right ih (κ : ℝ≥0∞)).trans hh

lemma episode_log_algebra {A C : ℝ≥0∞} (hA : A ≠ ⊤) (hC : C ≠ ⊤)
    (hA0 : A ≠ 0) (hC0 : C ≠ 0) (κ : ℝ≥0) (hκ : 0 < κ)
    (b : ℝ) (k L J : ℕ) (hk : 0 < k)
    (h : A^k*(κ:ℝ≥0∞)^(k*L)*
      ((κ:ℝ≥0∞)^k*ENNReal.ofReal (Real.exp (-((k:ℝ)*b))))^J ≤ C^k) :
    Real.log A.toReal-Real.log C.toReal ≤
      (L:ℝ)*(-Real.log κ)+(b-Real.log κ)*(J:ℝ) := by
  have hAf : 0 < A.toReal := ENNReal.toReal_pos hA0 hA
  have hCf : 0 < C.toReal := ENNReal.toReal_pos hC0 hC
  have hκf : 0 < (κ:ℝ) := hκ
  have ht := ENNReal.toReal_mono (ENNReal.pow_ne_top hC) h
  simp only [ENNReal.toReal_mul,ENNReal.toReal_pow,ENNReal.coe_toReal,
    ENNReal.toReal_ofReal (Real.exp_pos _).le] at ht
  have hl := Real.log_le_log (by positivity : 0 < A.toReal^k*(κ:ℝ)^(k*L)*
      ((κ:ℝ)^k*Real.exp (-((k:ℝ)*b)))^J) ht
  rw [Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity),Real.log_pow,Real.log_pow,Real.log_pow,
    Real.log_mul (by positivity) (Real.exp_ne_zero _),Real.log_pow,Real.log_exp,Real.log_pow] at hl
  have hkf : 0 < (k:ℝ) := Nat.cast_pos.mpr hk
  push_cast at hl
  nlinarith

theorem episode_log_bound {d k : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (r : ℝ → ℝ) (hr : Monotone r) (fexp g χ b sfloor : ℝ) (hR : 0 ≤ r sfloor) (N t : ℕ)
    (hf : 0 ≤ fexp) (hb : 0 ≤ b) (hsfloor : 0 < sfloor)
    (ω : Environment d) (hH : ∀ s, sfloor ≤ s → 0 < episodeStageH χ b s)
    (κ : ℝ≥0) (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) (hκ : ∀ y u, κ ≤ (ω y).1 u)
    (hk : 0 < k) (hbκ : -Real.log κ ≤ b) :
    0 ≤ Real.log (crossingQuenched (realPosition (step e)) 0 t ω).toReal -
      Real.log (crossingQuenched (realPosition (step e)) 0
        (episodeFinal (k:=k) e f hef r fexp g χ b sfloor hR N t ω).height ω).toReal ∧
    Real.log (crossingQuenched (realPosition (step e)) 0 t ω).toReal -
      Real.log (crossingQuenched (realPosition (step e)) 0
        (episodeFinal (k:=k) e f hef r fexp g χ b sfloor hR N t ω).height ω).toReal ≤
      (BoundedInjection.injectionMultiplier (r sfloor)*k+1:ℕ)*(-Real.log κ)+
      2*b*(episodeStageCount (k:=k) e f hef r fexp g χ b sfloor hR N t ω) := by
  let T := (episodeFinal (k:=k) e f hef r fexp g χ b sfloor hR N t ω).height
  have hpos (h : ℕ) : crossingQuenched (realPosition (step e)) 0 h ω ≠ 0 :=
    ne_of_gt ((ENNReal.pow_pos (ENNReal.coe_pos.mpr hκ0) h).trans_le
      (coordinate_survival_lower e ω κ (fun y => hκ y e) h))
  have hfinite (h : ℕ) := crossingQuenched_ne_top (realPosition (step e)) 0 h ω
  have hl := episode_log_algebra (hfinite t) (hfinite T) (hpos t) (hpos T) κ hκ0 b k
    (BoundedInjection.injectionMultiplier (r sfloor)*k+1)
    (episodeStageCount (k:=k) e f hef r fexp g χ b sfloor hR N t ω) hk
    (episode_survival_lower e f hef r hr fexp g χ b sfloor hR N t hf hb hsfloor ω hH κ hκ1 hκ)
  constructor
  · have hm := crossingQuenched_antitone (realPosition (step e)) 0 ω
      (a:= (t:ℝ)) (b:= (T:ℝ)) (by exact_mod_cast (episodeFinal_gt (k:=k) e f hef r fexp g χ b sfloor hR N t ω).le)
    exact sub_nonneg.mpr (Real.log_le_log (ENNReal.toReal_pos (hpos T) (hfinite T))
      (ENNReal.toReal_mono (hfinite t) hm))
  · have hj : 0 ≤ (episodeStageCount (k:=k) e f hef r fexp g χ b sfloor hR N t ω : ℝ) := by positivity
    dsimp only [T] at hl
    push_cast at hl ⊢
    nlinarith

end DirectionalTransience

end

end OAI
