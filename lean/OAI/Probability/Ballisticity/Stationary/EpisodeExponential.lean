import Mathlib
import OAI.Probability.Ballisticity.Estimates.CellBadEvent
import OAI.Probability.Ballisticity.Stationary.EpisodeFresh
import OAI.Probability.Ballisticity.Stationary.EpisodeRecordedAtlas

namespace OAI

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal Classical
namespace DirectionalTransience

noncomputable def stagePotential (t : ℝ) (j f : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (t*(f:ℝ)-Real.exp (-t)*(j:ℝ)))

lemma stagePotential_succ_le (t : ℝ) (j f : ℕ) (D : Prop) [Decidable D] :
    stagePotential t (j+1) (f+if D then 1 else 0) ≤
      stagePotential t j f * ENNReal.ofReal (Real.exp (-Real.exp (-t))) *
        (1+ENNReal.ofReal (Real.exp t)*(if D then 1 else 0)) := by
  unfold stagePotential
  have he (z : ℝ) : t*((f:ℝ)+z)-Real.exp (-t)*((j:ℝ)+1) =
      (t*(f:ℝ)-Real.exp (-t)*(j:ℝ))+(-Real.exp (-t))+t*z := by ring
  by_cases h : D
  · simp only [ite_eq_left h,Nat.cast_add,Nat.cast_one,he,Real.exp_add,mul_one]
    rw [ENNReal.ofReal_mul (by positivity),ENNReal.ofReal_mul (by positivity)]
    gcongr
    exact le_add_left (le_refl _)
  · simp only [ite_eq_right h,add_zero,Nat.cast_add,Nat.cast_one,mul_zero,add_zero]
    have he' : t*(f:ℝ)-Real.exp (-t)*((j:ℝ)+1) =
        (t*(f:ℝ)-Real.exp (-t)*(j:ℝ))+(-Real.exp (-t)) := by ring
    rw [he',Real.exp_add,ENNReal.ofReal_mul (Real.exp_nonneg _),mul_one]

lemma stage_exponential_factor (t : ℝ) :
    ENNReal.ofReal (Real.exp (-Real.exp (-t))) *
      (1+ENNReal.ofReal (Real.exp t)*ENNReal.ofReal (Real.exp (-2*t))) ≤ 1 := by
  have ht : Real.exp t*Real.exp (-2*t)=Real.exp (-t) := by rw [←Real.exp_add]; congr 1; ring
  rw [←ENNReal.ofReal_mul (Real.exp_nonneg _),ht,←ENNReal.ofReal_one,
    ←ENNReal.ofReal_add (by norm_num : (0:ℝ)≤1) (Real.exp_nonneg _),
    ←ENNReal.ofReal_mul (Real.exp_nonneg _)]
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ Real.exp (-Real.exp (-t))*Real.exp (Real.exp (-t)) :=
      mul_le_mul_of_nonneg_left (by linarith [Real.add_one_le_exp (Real.exp (-t))]) (by positivity)
    _ = 1 := by rw [←Real.exp_add,neg_add_cancel,Real.exp_zero]

lemma stagePotential_set_step {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (E D : Set Ω) (hE : MeasurableSet E) (t : ℝ) (j f : ℕ)
    (hD : P (E∩D) ≤ ENNReal.ofReal (Real.exp (-2*t))*P E) :
    ∫⁻ ω in E, stagePotential t (j+1) (f+if ω∈D then 1 else 0) ∂P ≤
      stagePotential t j f*P E := by
  let a := ENNReal.ofReal (Real.exp (-Real.exp (-t)))
  let c := ENNReal.ofReal (Real.exp t)
  let w := stagePotential t j f
  have hd : ∫⁻ ω in E, D.indicator (fun _ => (1:ℝ≥0∞)) ω ∂P ≤ P (E∩D) := by
    have h := lintegral_indicator_const_le (μ:=P.restrict E) D (1:ℝ≥0∞)
    simpa only [one_mul,Measure.restrict_apply' hE,Set.inter_comm] using h
  calc
    _ ≤ ∫⁻ ω in E, w*a*(1+c*D.indicator (fun _ => (1:ℝ≥0∞)) ω) ∂P := by
      apply lintegral_mono
      intro ω
      simpa only [Set.indicator_apply,Pi.one_apply] using stagePotential_succ_le t j f (ω∈D)
    _ = w*a*(P E+c*(∫⁻ ω in E, D.indicator (fun _ => (1:ℝ≥0∞)) ω ∂P)) := by
      rw [lintegral_const_mul' (w*a) _ (ENNReal.mul_ne_top (by simp [w,stagePotential]) (by simp [a])),
        lintegral_add_left measurable_const,lintegral_const_mul' c _ (by simp [c])]
      simp only [lintegral_const,Measure.restrict_apply_univ,one_mul]
    _ ≤ w*a*(P E+c*(ENNReal.ofReal (Real.exp (-2*t))*P E)) :=
      by gcongr; exact hd.trans hD
    _ = w*(a*(1+c*ENNReal.ofReal (Real.exp (-2*t))))*P E := by ring
    _ ≤ w*1*P E := by gcongr; exact stage_exponential_factor t
    _ = _ := by rw [mul_one]

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal Classical
namespace DirectionalTransience
namespace EpisodeRecordedAtlas
variable {d k : ℕ} {e f : Direction d} {r : ℝ → ℝ}
  {q : Environment d → EpisodeState (k:=k) e f r} {J F : Environment d → ℕ}

lemma integral_partition (A : EpisodeRecordedAtlas q J F) (hA : A.toEpisodeAtlas.IsPartition)
    (P : Measure (Environment d)) (W : Environment d → ℝ≥0∞) :
    ∫⁻ ω, W ω ∂P = ∑' l : A.Label, ∫⁻ ω in (A.chart l).event, W ω ∂P := by
  let := A.countable
  have hu : (⋃ l : A.Label, (A.chart l).event)=Set.univ :=
    Set.eq_univ_of_forall (fun ω => Set.mem_iUnion.mpr (A.cover ω))
  have hd : Pairwise (fun l m : A.Label => Disjoint (A.chart l).event (A.chart m).event) := by
    intro l m hne
    exact Set.disjoint_left.mpr (fun ω hl hm => hne (hA l m ω hl hm))
  simpa only [hu,Measure.restrict_univ] using
    lintegral_iUnion (μ:=P) (fun l => (rowSigma_le _) _ (A.chart l).measurable_event) hd W

lemma potential_advance (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (A : EpisodeRecordedAtlas q J F) (hA : A.toEpisodeAtlas.IsPartition)
    (fexp g χ b sfloor K : ℝ) (N : ℕ)
    (hH : ∀ s, sfloor ≤ s → 0 < episodeStageH χ b s)
    (hbound : ∀ s, sfloor ≤ s → ∀ a : ℝ, ∀ π : BudgetProfile (k:=k) e f a (r s),
      environmentLaw ν (stageBadEvent e f (episodeStageH χ b s)
        (r (s*Real.exp (-fexp*b))) (r (s*Real.exp (g*b))) π.val
        (ENNReal.ofReal (Real.exp (-((k:ℝ)*b))))) ≤ ENNReal.ofReal (Real.exp (-2*(K*b)))) :
    ∫⁻ ω, stagePotential (K*b)
      (J ω+if EpisodeReady e f r sfloor N (q ω) then 1 else 0)
      (F ω+if EpisodeReady e f r sfloor N (q ω) ∧ episodeStageFails e f r fexp g χ b N (q ω) ω then 1 else 0)
      ∂environmentLaw ν ≤
    ∫⁻ ω, stagePotential (K*b) (J ω) (F ω) ∂environmentLaw ν := by
  rw [A.integral_partition hA,A.integral_partition hA]
  apply ENNReal.tsum_le_tsum
  intro l
  let c := A.chart l
  have hc : MeasurableSet c.event := (rowSigma_le _) _ c.measurable_event
  have hold : (∫⁻ ω in c.event, stagePotential (K*b) (J ω) (F ω) ∂environmentLaw ν) =
      stagePotential (K*b) (A.stages l) (A.failures l)*environmentLaw ν c.event := by
    rw [setLIntegral_congr_fun hc (fun ω hω => by rw [A.stages_correct l ω hω,A.failures_correct l ω hω])]
    simp only [lintegral_const,Measure.restrict_apply_univ]
  rw [hold]
  by_cases hr : c.height<N ∧ sfloor ≤ c.scale
  · have he := c.actual_failure_bound ν fexp g χ b N hr.1 (hH _ hr.2)
      (ENNReal.ofReal (Real.exp (-2*(K*b)))) (hbound _ hr.2 _) c.event c.measurable_event
    calc
      _ = ∫⁻ ω in c.event, stagePotential (K*b) (A.stages l+1)
          (A.failures l+if episodeStageFails e f r fexp g χ b N (c.state ω) ω then 1 else 0)
          ∂environmentLaw ν := by
        apply setLIntegral_congr_fun hc
        intro ω hω
        dsimp only
        rw [A.stages_correct l ω hω,A.failures_correct l ω hω,A.correct l ω hω]
        change stagePotential (K*b)
          (A.stages l+if EpisodeReady e f r sfloor N (c.state ω) then 1 else 0)
          (A.failures l+if EpisodeReady e f r sfloor N (c.state ω) ∧ episodeStageFails e f r fexp g χ b N (c.state ω) ω then 1 else 0) = _
        have hready : EpisodeReady e f r sfloor N (c.state ω) := hr
        simp only [hready,ite_true,true_and]
      _ ≤ _ := stagePotential_set_step _ _ _ hc _ _ _ he
  · calc
      _ = ∫⁻ ω in c.event, stagePotential (K*b) (A.stages l) (A.failures l)
          ∂environmentLaw ν := by
        apply setLIntegral_congr_fun hc
        intro ω hω
        dsimp only
        rw [A.stages_correct l ω hω,A.failures_correct l ω hω,A.correct l ω hω]
        change stagePotential (K*b)
          (A.stages l+if EpisodeReady e f r sfloor N (c.state ω) then 1 else 0)
          (A.failures l+if EpisodeReady e f r sfloor N (c.state ω) ∧ episodeStageFails e f r fexp g χ b N (c.state ω) ω then 1 else 0) = _
        have hready : ¬EpisodeReady e f r sfloor N (c.state ω) := hr
        simp only [hready,ite_false,false_and,add_zero]
      _ ≤ _ := by simp only [lintegral_const,Measure.restrict_apply_univ,le_refl]

end EpisodeRecordedAtlas
end DirectionalTransience

end

end OAI
