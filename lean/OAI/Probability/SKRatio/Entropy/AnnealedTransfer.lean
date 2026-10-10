import Mathlib
import OAI.Probability.SKRatio.Gaussian.GaussianEvents
import OAI.Probability.SKRatio.Entropy.LogPartition

namespace OAI

section
noncomputable section
open scoped BigOperators Topology ENNReal NNReal
open MeasureTheory ProbabilityTheory Real Filter
namespace SKRatio.Planted
open Calculus
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

def badMass (B : Set (Disorder n)) (g : Disorder n) : ℝ :=
  FiniteLaw.mean (mass g 0) (fun x => if gauge x g ∈ B then 1 else 0)

lemma badMass_eq_div (B : Set (Disorder n)) (g : Disorder n) :
    badMass B g = badWeight B g / partition g 0 := by
  unfold badMass FiniteLaw.mean badWeight
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : gauge x g ∈ B <;> simp [hx,mass]

lemma badMass_nonneg (B : Set (Disorder n)) (g : Disorder n) : 0 ≤ badMass B g := by
  rw [badMass_eq_div]
  exact div_nonneg (badWeight_nonneg B g) (partition_pos g 0).le

lemma badWeight_measurable {B : Set (Disorder n)} (hB : MeasurableSet B) :
    Measurable (badWeight B) := by
  apply Finset.measurable_sum
  intro x _
  exact (continuous_weight 0 x).measurable.indicator
    (hB.preimage (gauge_continuous x).measurable)

lemma badMass_measurable {B : Set (Disorder n)} (hB : MeasurableSet B) :
    Measurable (badMass B) := by
  change Measurable (fun g => badMass B g)
  simp_rw [badMass_eq_div]
  exact (badWeight_measurable hB).div (continuous_partition 0).measurable

lemma badWeight_probability {β κ : ℝ} {B : Set (Disorder n)}
    (hB : MeasurableSet B)
    (hp : law β n B ≤ ENNReal.ofReal (exp (-κ*n))) :
    disorderLaw β n {g | ((2:ℝ)^n*exp (normalizingExponent β n))*
      exp (-(3*κ/4)*n) < badWeight B g} ≤ ENNReal.ofReal (exp (-(κ/4)*n)) := by
  let M := (2:ℝ)^n*exp (normalizingExponent β n)
  have hM : 0 < M := by dsimp [M]; positivity
  have hthreshold : 0 < M*exp (-(3*κ/4)*n) := mul_pos hM (exp_pos _)
  have hpR : (law β n).real B ≤ exp (-κ*n) := by
    have ht := ENNReal.toReal_mono (ENNReal.ofReal_ne_top) hp
    change (law β n B).toReal ≤ _
    simpa only [ENNReal.toReal_ofReal (exp_pos _).le] using ht
  have hi := mul_meas_ge_le_integral_of_nonneg
    (μ := disorderLaw β n) (f := badWeight B)
    (Eventually.of_forall (badWeight_nonneg B)) (badWeight_integrable β hB)
    (M*exp (-(3*κ/4)*n))
  have hs : {g : Disorder n | M*exp (-(3*κ/4)*n) < badWeight B g} ⊆
      {g | M*exp (-(3*κ/4)*n) ≤ badWeight B g} := by
    intro g hg
    exact (show M*exp (-(3*κ/4)*n) < badWeight B g from hg).le
  have hl := mul_le_mul_of_nonneg_left (measureReal_mono (μ := disorderLaw β n) hs)
    hthreshold.le
  rw [integral_badWeight β hB] at hi
  change _ ≤ M*(law β n).real B at hi
  have hb := hl.trans (hi.trans (mul_le_mul_of_nonneg_left hpR hM.le))
  have he : M*exp (-κ*n)/(M*exp (-(3*κ/4)*n)) = exp (-(κ/4)*n) := by
    rw [mul_div_mul_left _ _ hM.ne',←exp_sub]
    congr 1
    ring
  have hreal : (disorderLaw β n).real
      {g | M*exp (-(3*κ/4)*n) < badWeight B g} ≤ exp (-(κ/4)*n) := by
    rw [←he]
    apply (le_div_iff₀ hthreshold).mpr
    simpa only [mul_comm] using hb
  rw [←ENNReal.ofReal_toReal (measure_ne_top _ _)]
  exact ENNReal.ofReal_le_ofReal hreal

lemma badMass_event_subset (β κ : ℝ) (B : Set (Disorder n)) :
    {g : Disorder n | exp (-(κ/2)*n) < badMass B g} ⊆
      {g | partition g 0 < ((2:ℝ)^n*exp (normalizingExponent β n))*exp (-(κ/4)*n)} ∪
      {g | ((2:ℝ)^n*exp (normalizingExponent β n))*exp (-(3*κ/4)*n) < badWeight B g} := by
  intro g hg
  by_contra h
  simp only [Set.mem_union,Set.mem_ofPred_eq,not_or,not_lt] at h
  have he : (((2:ℝ)^n*exp (normalizingExponent β n))*exp (-(κ/4)*n))*
      exp (-(κ/2)*n) = ((2:ℝ)^n*exp (normalizingExponent β n))*exp (-(3*κ/4)*n) := by
    rw [mul_assoc,←exp_add]
    congr 2
    ring
  have hh := mul_le_mul_of_nonneg_right h.1 (exp_pos (-(κ/2)*n)).le
  rw [he] at hh
  have hb : badMass B g ≤ exp (-(κ/2)*n) := by
    rw [badMass_eq_div]
    apply (div_le_iff₀ (partition_pos g 0)).mpr
    simpa only [mul_comm] using h.2.trans hh
  exact not_le_of_gt hg hb

theorem annealed_transfer {β κ : ℝ} (hβ : β^2 ≤ 1/2) (hκ : 0 < κ)
    (B : ∀ n : ℕ, Set (Disorder n)) (hB : ∀ n, MeasurableSet (B n))
    (hp : ∀ᶠ n : ℕ in atTop, law β n (B n) ≤ ENNReal.ofReal (exp (-κ*n))) :
    Tendsto (fun n : ℕ => disorderLaw β n
      {g | exp (-(κ/2)*n) < badMass (B n) g}) atTop (𝓝 0) := by
  have hpart := partition_lower_high_probability hβ (show 0 < κ/4 by positivity)
  have he : Tendsto (fun n : ℕ => ENNReal.ofReal (exp (-(κ/4)*n))) atTop (𝓝 0) := by
    have hr := Gaussian.nat_pow_exp_neg_tendsto (show 0 < κ/4 by positivity) 0
    simp only [pow_zero,one_mul] at hr
    simpa only [Function.comp_def,ENNReal.ofReal_zero] using
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp hr
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds (by simpa only [add_zero] using hpart.add he)
    (Eventually.of_forall fun n => (show (0:ℝ≥0∞) ≤ disorderLaw β n
      {g | exp (-(κ/2)*n) < badMass (B n) g} from bot_le))
  filter_upwards [hp] with n hn
  exact (measure_mono (badMass_event_subset β κ (B n))).trans
    ((measure_union_le _ _).trans (add_le_add le_rfl (badWeight_probability (hB n) hn)))

theorem annealed_transfer_events {β κ : ℝ} (hβ : β^2 ≤ 1/2) (hκ : 0 < κ)
    (B : ∀ n : ℕ, Set (Disorder n)) (hB : ∀ n, MeasurableSet (B n))
    (hp : ∀ᶠ n : ℕ in atTop, law β n (B n) ≤ ENNReal.ofReal (exp (-κ*n))) :
    ∃ G : ∀ n : ℕ, Set (Disorder n),
      (∀ n, MeasurableSet (G n)) ∧
      Tendsto (fun n => disorderLaw β n (G n)ᶜ) atTop (𝓝 0) ∧
      ∀ n, ∀ g ∈ G n, badMass (B n) g ≤ exp (-(κ/2)*n) := by
  refine ⟨fun n => {g | badMass (B n) g ≤ exp (-(κ/2)*n)},?_,?_,?_⟩
  · intro n
    exact measurableSet_le (badMass_measurable (hB n)) measurable_const
  · simpa only [Set.compl_ofPred,not_le] using annealed_transfer hβ hκ B hB hp
  · intro n g hg
    exact hg

end SKRatio.Planted

end
end

end OAI
