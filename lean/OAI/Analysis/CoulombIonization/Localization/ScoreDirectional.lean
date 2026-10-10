import Mathlib
import OAI.Analysis.CoulombIonization.Localization.WeightedMoments
import OAI.Analysis.CoulombIonization.Localization.ObservationScoreMoments

namespace OAI

noncomputable section

namespace CoulombObservation

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_ScoreDirectional_scope

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal NNReal BigOperators

lemma compactNoiseScore_memLp {k : ℕ} (hk : 0 < k) :
    MemLp compactNoiseScore (2*k : ℕ) compactNoiseLaw := by
  apply (integrable_norm_rpow_iff compactNoiseScore_measurable.aestronglyMeasurable
    (show (2*k : ℕ) ≠ (0:ℝ≥0∞) by exact_mod_cast (by omega : 2*k ≠ 0))
    (by finiteness)).mp
  simpa only [ENNReal.toReal_natCast, Real.rpow_natCast, Real.norm_eq_abs, pow_mul, sq_abs]
    using compactNoiseScore_moment_integrable k

def observationMomentConstant : ℝ := 8 * Real.exp 1 * compactScoreConstant^2

lemma observationMomentConstant_pos : 0 < observationMomentConstant := by
  unfold observationMomentConstant
  have := compactScoreConstant_pos
  positivity

theorem compactNoiseScore_directional_moment {ι : Type*} [Fintype ι]
    (a : ι → ℝ) {k : ℕ} (hk : 0 < k) :
    (∫ u : ι → ℝ, (∑ i, a i * compactNoiseScore (u i))^(2*k)
      ∂Measure.pi (fun _ => compactNoiseLaw)) ≤
      (observationMomentConstant * (k:ℝ)^5 * (∑ i, a i^2))^k := by
  have hh := symmetric_directional_moment_le (fun _ : ι => compactNoiseLaw)
    (fun _ => compactNoiseLaw_neg_preserving) (fun _ => compactNoiseScore)
    (fun _ => compactNoiseScore_measurable) (fun _ => compactNoiseScore_odd) a hk
    (fun _ => compactNoiseScore_memLp hk) (compactScoreConstant*(k:ℝ)^2)
    (fun _ => compactNoiseScore_moment_le hk)
  refine hh.trans_eq ?_
  rw [pow_mul (compactScoreConstant*(k:ℝ)^2) 2 k, ← mul_pow, ← mul_pow]
  congr 1
  dsimp [observationMomentConstant]
  ring

end Work_ScoreDirectional_scope

open MeasureTheory Set Finset
open scoped ENNReal NNReal BigOperators

lemma integral_even_pow_le_mass {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] (f : Ω → ℝ) {k : ℕ} (hk : 0 < k)
    (hf : Integrable f μ) (hpow : Integrable (fun x => f x^(2*k)) μ)
    (hp : 0 < μ.real univ) :
    (∫ x, f x ∂μ)^(2*k) ≤ (μ.real univ)^(2*k-1) * ∫ x, f x^(2*k) ∂μ := by
  have : NeZero μ := ⟨fun hz => by simp [hz] at hp⟩
  have hev : Even (2*k) := ⟨k, by omega⟩
  have hh := hev.convexOn_pow (𝕜 := ℝ) |>.map_average_le
    (continuous_pow (2*k)).continuousOn isClosed_univ (ae_of_all _ (fun _ => mem_univ _)) hf hpow
  simp only [average_eq, smul_eq_mul] at hh
  have he : (μ.real univ)^(2*k) = (μ.real univ)^(2*k-1) * μ.real univ := by
    rw [← pow_succ]; congr 1; omega
  calc
    _ = (μ.real univ)^(2*k) * ((μ.real univ)⁻¹ * ∫ x, f x ∂μ)^(2*k) := by
      rw [← mul_pow, mul_inv_cancel_left₀ (ne_of_gt hp)]
    _ ≤ (μ.real univ)^(2*k) * ((μ.real univ)⁻¹ * ∫ x, f x^(2*k) ∂μ) :=
      mul_le_mul_of_nonneg_left hh (pow_nonneg hp.le _)
    _ = _ := by rw [he]; field_simp

lemma event_even_moment_le {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] (f : Ω → ℝ) {k : ℕ} (hk : 0 < k)
    (hf : Integrable f μ) (hpow : Integrable (fun x => f x^(2*k)) μ)
    (s : Set Ω) (hp : 0 < μ.real s) :
    (∫ x in s, f x ∂μ)^(2*k) ≤ (μ.real s)^(2*k-1) * ∫ x, f x^(2*k) ∂μ := by
  have hh := integral_even_pow_le_mass f hk hf.integrableOn hpow.integrableOn
    (by simpa only [measureReal_restrict_apply_univ] using hp : 0 < (μ.restrict s).real univ)
  rw [measureReal_restrict_apply_univ] at hh
  refine hh.trans (mul_le_mul_of_nonneg_left ?_ (pow_nonneg hp.le _))
  exact setIntegral_le_integral hpow (ae_of_all _ (fun x => by change 0 ≤ f x^(2*k); rw [pow_mul]; positivity))

theorem compactNoiseScore_event_moment {ι : Type*} [Fintype ι]
    (a : ι → ℝ) {k : ℕ} (hk : 0 < k) (s : Set (ι → ℝ))
    (hp : 0 < (Measure.pi (fun _ : ι => compactNoiseLaw)).real s) :
    (∫ u in s, (∑ i, a i * compactNoiseScore (u i))
      ∂Measure.pi (fun _ => compactNoiseLaw))^(2*k) ≤
      ((Measure.pi (fun _ : ι => compactNoiseLaw)).real s)^(2*k-1) *
        (observationMomentConstant * (k:ℝ)^5 * (∑ i, a i^2))^k := by
  classical
  have hm : MemLp (fun u : ι → ℝ => ∑ i, a i * compactNoiseScore (u i))
      (2*k : ℕ) (Measure.pi (fun _ => compactNoiseLaw)) := by
    apply memLp_finsetSum
    intro i _
    exact ((compactNoiseScore_memLp hk).comp_measurePreserving
      (measurePreserving_eval (fun _ : ι => compactNoiseLaw) i)).const_mul (a i)
  have hf := hm.integrable (by exact_mod_cast (show 1 ≤ 2*k by omega))
  have hpow := coordinate_sum_even_integrable (fun _ : ι => compactNoiseLaw)
    (fun _ => compactNoiseScore) a hk (fun _ => compactNoiseScore_memLp hk)
  exact (event_even_moment_le _ hk hf hpow s hp).trans
    (mul_le_mul_of_nonneg_left (compactNoiseScore_directional_moment a hk) (by positivity))

open MeasureTheory Set Finset
open scoped ENNReal NNReal BigOperators

lemma compactNoiseScore_eval_integrable {ι : Type*} [Fintype ι] (i : ι) :
    Integrable (fun u : ι → ℝ => compactNoiseScore (u i))
      (Measure.pi (fun _ => compactNoiseLaw)) := by
  exact ((compactNoiseScore_memLp (by decide : 0 < 1)).comp_measurePreserving
    (measurePreserving_eval (fun _ : ι => compactNoiseLaw) i)).integrable (by norm_num)

def eventScore {J I : Type*} [Fintype J] [Fintype I] (b : J → ℝ)
    (s : Set (J × I → ℝ)) (i : I) : ℝ :=
  ∫ u in s, (∑ j, b j * compactNoiseScore (u (j,i)))
    ∂Measure.pi (fun _ : J × I => compactNoiseLaw)

lemma eventScore_direction {J I : Type*} [Fintype J] [Fintype I]
    (b : J → ℝ) (s : Set (J × I → ℝ)) (v : I → ℝ) :
    (∫ u in s, (∑ q : J × I, (b q.1 * v q.2) * compactNoiseScore (u q))
      ∂Measure.pi (fun _ => compactNoiseLaw)) = ∑ i, v i * eventScore b s i := by
  classical
  simp only [Fintype.sum_prod_type]
  rw [integral_finsetSum _ (fun j _ => integrable_finsetSum _ (fun i _ =>
    ((compactNoiseScore_eval_integrable (j,i)).const_mul (b j * v i)).integrableOn))]
  simp_rw [integral_finsetSum _ (fun i _ =>
    ((compactNoiseScore_eval_integrable (_,i)).const_mul _).integrableOn)]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simp only [eventScore]
  rw [integral_finsetSum _ (fun j _ =>
    ((compactNoiseScore_eval_integrable (j,i)).const_mul _).integrableOn), mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp only [integral_const_mul]
  ring

theorem compactNoise_eventScore_pow {J I : Type*} [Fintype J] [Fintype I]
    (b : J → ℝ) (s : Set (J × I → ℝ)) {k : ℕ} (hk : 0 < k)
    (hp : 0 < (Measure.pi (fun _ : J × I => compactNoiseLaw)).real s) :
    (∑ i, (eventScore b s i)^2)^k ≤
      ((Measure.pi (fun _ : J × I => compactNoiseLaw)).real s)^(2*k-1) *
        (observationMomentConstant * (k:ℝ)^5 * (∑ j, (b j)^2))^k := by
  classical
  let v := eventScore b s
  let W : ℝ := ∑ i, (v i)^2
  have hW : 0 ≤ W := sum_nonneg (fun _ _ => sq_nonneg _)
  by_cases hzero : W = 0
  · change W^k ≤ _
    rw [hzero, zero_pow (by omega)]
    have hC := observationMomentConstant_pos
    positivity
  have hWp : 0 < W := lt_of_le_of_ne hW (Ne.symm hzero)
  have hh := compactNoiseScore_event_moment (fun q : J × I => b q.1 * v q.2) hk s hp
  rw [eventScore_direction] at hh
  have hid : (∑ i, v i * eventScore b s i) = W := by
    dsimp [W, v]; congr 1; funext i; ring
  rw [hid] at hh
  have ha : (∑ q : J × I, (b q.1 * v q.2)^2) = (∑ j, (b j)^2) * W := by
    simp only [Fintype.sum_prod_type, mul_pow]
    simp only [← mul_sum, W, sum_mul]
  rw [ha, ← mul_assoc _ _ W, mul_pow, pow_mul, pow_two] at hh
  change W^k ≤ _
  exact (mul_le_mul_iff_left₀ (pow_pos hWp k)).mp
    (by simpa only [mul_pow, mul_assoc, mul_comm, mul_left_comm] using hh)

theorem compactNoise_eventScore_sq {J I : Type*} [Fintype J] [Fintype I]
    (b : J → ℝ) (s : Set (J × I → ℝ)) {k : ℕ} (hk : 0 < k)
    (hp : 0 < (Measure.pi (fun _ : J × I => compactNoiseLaw)).real s) :
    (∑ i, (eventScore b s i)^2) ≤
      observationMomentConstant * (k:ℝ)^5 * (∑ j, (b j)^2) *
      ((Measure.pi (fun _ : J × I => compactNoiseLaw)).real s) ^
        (2 - (k:ℝ)⁻¹) := by
  let p := (Measure.pi (fun _ : J × I => compactNoiseLaw)).real s
  have hkR : (0:ℝ) < k := by exact_mod_cast hk
  have he : (2 - (k:ℝ)⁻¹) * k = (2*k-1 : ℕ) := by
    rw [Nat.cast_sub (by omega : 1 ≤ 2*k), Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
    field_simp
  apply (pow_le_pow_iff_left₀ (sum_nonneg (fun _ _ => sq_nonneg _))
    (by have hC := observationMomentConstant_pos; positivity) (by omega : k ≠ 0)).mp
  rw [mul_pow, ← Real.rpow_natCast (p ^ (2 - (k:ℝ)⁻¹)), ← Real.rpow_mul hp.le, he,
    Real.rpow_natCast, mul_comm]
  exact compactNoise_eventScore_pow b s hk hp

end CoulombObservation

end

end OAI
