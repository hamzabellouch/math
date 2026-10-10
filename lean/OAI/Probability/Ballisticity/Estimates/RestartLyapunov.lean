import Mathlib
import OAI.Probability.Ballisticity.Model

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

namespace DirectionalTransience

def observerRewardSum {Ω : Type*} (next : Ω → Ω) (reward : Ω → ℝ≥0∞) : ℕ → Ω → ℝ≥0∞
  | 0, _ => 0
  | N+1, ω => reward ω+observerRewardSum next reward N (next ω)

lemma measurable_observerRewardSum {Ω : Type*} [MeasurableSpace Ω]
    (next : Ω → Ω) (reward : Ω → ℝ≥0∞) (hn : Measurable next) (hr : Measurable reward)
    (N : ℕ) : Measurable (observerRewardSum next reward N) := by
  induction N with
  | zero => exact measurable_const
  | succ N ih => exact hr.add (ih.comp hn)

lemma observerRewardSum_mono {Ω : Type*} (next : Ω → Ω) (reward : Ω → ℝ≥0∞) :
    Monotone (observerRewardSum next reward) := by
  apply monotone_nat_of_le_succ
  intro N
  induction N with
  | zero => exact fun _ => zero_le
  | succ N ih => exact fun ω => add_le_add_right (ih (next ω)) _

lemma restart_lyapunov_finite {Ω I : Type*} [MeasurableSpace Ω] [MeasurableSpace I]
    [Countable I] [MeasurableSingletonClass I]
    (μ : I → Measure Ω) (state : Ω → I) (next : Ω → Ω) (good : I → Prop)
    (reward : Ω → ℝ≥0∞) (V : I → ℝ≥0∞)
    (hs : Measurable state) (hn : Measurable next) (hr : Measurable reward)
    (hrestart : ∀ i, good i → ∀ g : Ω → ℝ≥0∞, Measurable g →
      (∫⁻ ω, g (next ω) ∂μ i) = ∫⁻ ω, (∫⁻ η, g η ∂μ (state (next ω))) ∂μ i)
    (hgood : ∀ i, good i → ∀ᵐ ω ∂μ i, good (state (next ω)))
    (hdrift : ∀ i, good i → (∫⁻ ω, reward ω+V (state (next ω)) ∂μ i) ≤ V i)
    (N : ℕ) : ∀ i, good i → (∫⁻ ω, observerRewardSum next reward N ω ∂μ i) ≤ V i := by
  induction N with
  | zero => intro i hi; simp only [observerRewardSum,lintegral_zero]; exact zero_le
  | succ N ih =>
    intro i hi
    have hsum := measurable_observerRewardSum next reward hn hr N
    have hV : Measurable V := measurable_of_countable _
    calc
      (∫⁻ ω, observerRewardSum next reward (N+1) ω ∂μ i) =
          (∫⁻ ω, reward ω ∂μ i)+(∫⁻ ω, observerRewardSum next reward N (next ω) ∂μ i) :=
        lintegral_add_left hr _
      _ = (∫⁻ ω, reward ω ∂μ i)+
          (∫⁻ ω, (∫⁻ η, observerRewardSum next reward N η ∂μ (state (next ω))) ∂μ i) := by
        rw [hrestart i hi _ hsum]
      _ ≤ (∫⁻ ω, reward ω ∂μ i)+(∫⁻ ω, V (state (next ω)) ∂μ i) :=
        add_le_add_right (lintegral_mono_ae ((hgood i hi).mono fun ω hω => ih _ hω)) _
      _ = (∫⁻ ω, reward ω+V (state (next ω)) ∂μ i) :=
        (lintegral_add_right _ ((hV.comp hs).comp hn)).symm
      _ ≤ V i := hdrift i hi

lemma restart_lyapunov_total {Ω I : Type*} [MeasurableSpace Ω] [MeasurableSpace I]
    [Countable I] [MeasurableSingletonClass I]
    (μ : I → Measure Ω) (state : Ω → I) (next : Ω → Ω) (good : I → Prop)
    (reward : Ω → ℝ≥0∞) (V : I → ℝ≥0∞)
    (hs : Measurable state) (hn : Measurable next) (hr : Measurable reward)
    (hrestart : ∀ i, good i → ∀ g : Ω → ℝ≥0∞, Measurable g →
      (∫⁻ ω, g (next ω) ∂μ i) = ∫⁻ ω, (∫⁻ η, g η ∂μ (state (next ω))) ∂μ i)
    (hgood : ∀ i, good i → ∀ᵐ ω ∂μ i, good (state (next ω)))
    (hdrift : ∀ i, good i → (∫⁻ ω, reward ω+V (state (next ω)) ∂μ i) ≤ V i)
    (i : I) (hi : good i) :
    (∫⁻ ω, ⨆ N, observerRewardSum next reward N ω ∂μ i) ≤ V i := by
  rw [lintegral_iSup (fun N => measurable_observerRewardSum next reward hn hr N)
    (observerRewardSum_mono next reward)]
  exact iSup_le fun N => restart_lyapunov_finite μ state next good reward V hs hn hr
    hrestart hgood hdrift N i hi

lemma restart_bounded_potential_total {Ω I : Type*} [MeasurableSpace Ω] [MeasurableSpace I]
    [Countable I] [MeasurableSingletonClass I]
    (μ : I → Measure Ω) [∀ i, IsProbabilityMeasure (μ i)]
    (state : Ω → I) (next : Ω → Ω) (good : I → Prop)
    (potential gain : I → ℝ) (C : ℝ)
    (hs : Measurable state) (hn : Measurable next)
    (horigin : ∀ i, good i → ∀ᵐ ω ∂μ i, state ω=i)
    (hrestart : ∀ i, good i → ∀ g : Ω → ℝ≥0∞, Measurable g →
      (∫⁻ ω, g (next ω) ∂μ i) = ∫⁻ ω, (∫⁻ η, g η ∂μ (state (next ω))) ∂μ i)
    (hgood : ∀ i, good i → ∀ᵐ ω ∂μ i, good (state (next ω)))
    (hpot : ∀ i, 0≤potential i ∧ potential i≤C)
    (hgain : ∀ i, 0≤gain i)
    (hdrift : ∀ i, good i → gain i+potential i ≤ ∫ ω, potential (state (next ω)) ∂μ i)
    (i : I) (hi : good i) :
    (∫⁻ ω, ⨆ N, observerRewardSum next (fun η => ENNReal.ofReal (gain (state η))) N ω ∂μ i)
      ≤ ENNReal.ofReal (C-potential i) := by
  let reward := fun ω => ENNReal.ofReal (gain (state ω))
  let V := fun j => ENNReal.ofReal (C-potential j)
  have hp : Measurable potential := measurable_of_countable _
  have hg : Measurable gain := measurable_of_countable _
  have hV : Measurable (fun j => C-potential j) := measurable_const.sub hp
  have hr : Measurable reward := (hg.comp hs).ennreal_ofReal
  apply restart_lyapunov_total μ state next good reward V hs hn hr hrestart hgood
    (fun j hj => ?_) i hi
  have hiP : Integrable (fun ω => potential (state (next ω))) (μ j) := by
    apply Integrable.of_bound ((hp.comp hs).comp hn).aestronglyMeasurable C
    exact Eventually.of_forall fun ω => by
      change ‖potential (state (next ω))‖ ≤ C
      rw [Real.norm_eq_abs,abs_of_nonneg (hpot _).1]
      exact (hpot _).2
  have hiV : Integrable (fun ω => C-potential (state (next ω))) (μ j) :=
    (integrable_const C).sub hiP
  have hiG : Integrable (fun ω => gain (state ω)) (μ j) := by
    apply (integrable_const (gain j)).congr
    exact (horigin j hj).mono fun ω hω => (congrArg gain hω).symm
  have hh : (fun ω => reward ω+V (state (next ω))) =
      (fun ω => ENNReal.ofReal (gain (state ω)+(C-potential (state (next ω))))) := by
    funext ω
    exact (ENNReal.ofReal_add (hgain _) (sub_nonneg.mpr (hpot _).2)).symm
  have hsum : Integrable (fun ω => gain (state ω)+(C-potential (state (next ω)))) (μ j) := hiG.add hiV
  rw [hh,← ofReal_integral_eq_lintegral_ofReal hsum
    (Eventually.of_forall fun ω => add_nonneg (hgain _) (sub_nonneg.mpr (hpot _).2))]
  apply ENNReal.ofReal_le_ofReal
  rw [integral_add hiG hiV,integral_sub (integrable_const C) hiP]
  have he : (∫ ω, gain (state ω) ∂μ j)=gain j := by
    rw [integral_congr_ae ((horigin j hj).mono fun ω hω => congrArg gain hω),integral_const]
    simp
  rw [he,integral_const]
  simp only [probReal_univ,smul_eq_mul,one_mul]
  have hd := hdrift j hj
  linarith

lemma restart_reward_comparison_total {Ω I : Type*} [MeasurableSpace Ω] [MeasurableSpace I]
    [Countable I] [MeasurableSingletonClass I]
    (μ : I → Measure Ω) (state : Ω → I) (next : Ω → Ω) (good : I → Prop)
    (reward bound : Ω → ℝ≥0∞)
    (hn : Measurable next) (hr : Measurable reward) (hb : Measurable bound)
    (hrestart : ∀ i, good i → ∀ g : Ω → ℝ≥0∞, Measurable g →
      (∫⁻ ω, g (next ω) ∂μ i) = ∫⁻ ω, (∫⁻ η, g η ∂μ (state (next ω))) ∂μ i)
    (hgood : ∀ i, good i → ∀ᵐ ω ∂μ i, good (state (next ω)))
    (hmean : ∀ i, good i → (∫⁻ ω, reward ω ∂μ i) ≤ ∫⁻ ω, bound ω ∂μ i)
    (i : I) (hi : good i) :
    (∫⁻ ω, ⨆ N, observerRewardSum next reward N ω ∂μ i) ≤
      ∫⁻ ω, ⨆ N, observerRewardSum next bound N ω ∂μ i := by
  have hfin : ∀ N i, good i →
      (∫⁻ ω, observerRewardSum next reward N ω ∂μ i) ≤
      ∫⁻ ω, observerRewardSum next bound N ω ∂μ i := by
    intro N
    induction N with
    | zero => intro i hi; simp only [observerRewardSum,lintegral_zero,le_refl]
    | succ N ih =>
      intro i hi
      change (∫⁻ ω, reward ω+observerRewardSum next reward N (next ω) ∂μ i) ≤
        ∫⁻ ω, bound ω+observerRewardSum next bound N (next ω) ∂μ i
      rw [lintegral_add_left hr,lintegral_add_left hb,
        hrestart i hi _ (measurable_observerRewardSum next reward hn hr N),
        hrestart i hi _ (measurable_observerRewardSum next bound hn hb N)]
      exact add_le_add (hmean i hi)
        (lintegral_mono_ae ((hgood i hi).mono fun ω hω => ih _ hω))
  rw [lintegral_iSup (fun N => measurable_observerRewardSum next reward hn hr N)
    (observerRewardSum_mono next reward),
    lintegral_iSup (fun N => measurable_observerRewardSum next bound hn hb N)
    (observerRewardSum_mono next bound)]
  exact iSup_mono fun N => hfin N i hi

lemma observerRewardSum_mul {Ω : Type*} (next : Ω → Ω) (reward : Ω → ℝ≥0∞)
    (c : ℝ≥0∞) (N : ℕ) (ω : Ω) :
    observerRewardSum next (fun η => c*reward η) N ω=c*observerRewardSum next reward N ω := by
  induction N generalizing ω with
  | zero => simp only [observerRewardSum,mul_zero]
  | succ N ih => simp only [observerRewardSum,ih,mul_add]

end DirectionalTransience

end

end

end OAI
