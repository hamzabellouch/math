import Mathlib
import OAI.Probability.ThreeStateClauses.RegularStatistics
import OAI.Probability.ThreeStateClauses.InformationLoss

namespace OAI

/-! Regular Reconstruction. -/

open scoped BigOperators ENNReal NNReal Topology
open Filter
noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators Topology
namespace ThreeState.TreeClauses.Tree
open ThreeState.TreeClauses.Experiment

def ksConstant (b : ℕ) (lam : ℝ) : ℝ := 4*((b:ℝ)*lam^2)/((b:ℝ)*lam^2-1)

lemma ksConstant_pos {b : ℕ} {lam : ℝ} (hKS : 1 < (b:ℝ)*lam^2) : 0 < ksConstant b lam := by
  unfold ksConstant; positivity

lemma ksConstant_ge_four {b : ℕ} {lam : ℝ} (hKS : 1 < (b:ℝ)*lam^2) : 4 ≤ ksConstant b lam := by
  rw [ksConstant, le_div_iff₀ (by linarith)]
  linarith

lemma ksConstant_identity {b : ℕ} {lam : ℝ} (hKS : 1 < (b:ℝ)*lam^2) :
    ksConstant b lam*((b:ℝ)*lam^2-1) = 4*((b:ℝ)*lam^2) := by
  rw [ksConstant, div_mul_cancel₀ _ (by linarith)]

lemma regularStatistic_second (b : ℕ) (lam : ℝ) (hlam : Admissible lam)
    (hKS : 1 < (b:ℝ)*lam^2) (ℓ : ℕ) (i : Spin) :
    (∫ v, regularStatistic b lam ℓ v^2 ∂(regularLaw b lam hlam ℓ i).toMeasure) ≤ ksConstant b lam := by
  have hb : 0 < b := by
    by_contra h
    have hb0 : b = 0 := by omega
    norm_num [hb0] at hKS
  have hb' : (0:ℝ) < b := Nat.cast_pos.mpr hb
  have hl : lam ≠ 0 := by intro h; norm_num [h] at hKS
  have hden : 0 < ((b:ℝ)*lam)^2 := sq_pos_of_ne_zero (mul_ne_zero (ne_of_gt hb') hl)
  have hC := ksConstant_pos hKS
  induction ℓ generalizing i with
  | zero =>
    change (∫ v : Spin, spinScore v^2 ∂(PMF.pure i).toMeasure) ≤ _
    rw [PMF.toMeasure_pure, integral_dirac]
    exact (spinScore_square i).trans (ksConstant_ge_four hKS)
  | succ ℓ ih =>
    have hmean : (∫ v, regularStatistic b lam ℓ v
        ∂((channel lam hlam i).bind (regularLaw b lam hlam ℓ)).toMeasure) = lam*spinScore i := by
      rw [integral_pmf_bind_finite]
      simp_rw [regularStatistic_mean b hb lam hlam hl ℓ]
      exact channel_spinScore lam hlam i
    have hsecond : (∫ v, regularStatistic b lam ℓ v^2
        ∂((channel lam hlam i).bind (regularLaw b lam hlam ℓ)).toMeasure) ≤ ksConstant b lam := by
      rw [integral_pmf_bind_finite]
      exact (integral_mono Integrable.of_finite (integrable_const _) (ih)).trans_eq (by simp)
    change (∫ v : Fin b → RegularObservation b ℓ,
      ((∑ j, regularStatistic b lam ℓ (v j))/((b:ℝ)*lam))^2
      ∂(productPMF (fun _ ↦ (channel lam hlam i).bind (regularLaw b lam hlam ℓ))).toMeasure) ≤ _
    simp_rw [div_pow]
    rw [integral_div, integral_product_sq_sum, hmean]
    apply (div_le_iff₀ hden).2
    have hb1 : (1:ℝ) ≤ b := by exact_mod_cast hb
    have hn : 0 ≤ (b:ℝ)^2-b := by nlinarith
    have hs := mul_le_mul_of_nonneg_left (spinScore_square i) (sq_nonneg lam)
    have hp := mul_le_mul_of_nonneg_left hs hn
    have hi := congrArg (fun x : ℝ ↦ x*(b:ℝ)) (ksConstant_identity hKS)
    have hm := mul_le_mul_of_nonneg_left hsecond hb'.le
    nlinarith [mul_nonneg hb'.le (sq_nonneg lam)]

lemma regular_estimator_advantage (b : ℕ) (lam : ℝ) (hlam : Admissible lam)
    (hKS : 1 < (b:ℝ)*lam^2) (ℓ : ℕ) :
    1/(3*ksConstant b lam) ≤ advantage lam hlam (PMF.pure b) ℓ := by
  have hb : 0 < b := by
    by_contra h
    have hb0 : b = 0 := by omega
    norm_num [hb0] at hKS
  have hl : lam ≠ 0 := by intro h; norm_num [h] at hKS
  let p := observationLaw lam hlam (PMF.pure b) ℓ
  let f := observedRegularStatistic b lam ℓ
  obtain ⟨B,hB0,hB⟩ := observedRegularStatistic_bound b lam ℓ
  have hmean (i : Spin) : (∫ o, f o ∂(p i).toMeasure) = spinScore i := by
    dsimp [p, f]
    rw [← regularLaw_forget b lam hlam ℓ i, integral_pmf_map]
    simp_rw [observedRegularStatistic_forget]
    exact regularStatistic_mean b hb lam hlam hl ℓ i
  have hsecond (i : Spin) : (∫ o, f o^2 ∂(p i).toMeasure) ≤ ksConstant b lam := by
    dsimp [p, f]
    rw [← regularLaw_forget b lam hlam ℓ i, integral_pmf_map]
    simp_rw [observedRegularStatistic_forget]
    exact regularStatistic_second b lam hlam hKS ℓ i
  rw [advantage_eq_integral]
  apply estimator_tv_lower (p := p) hB (ksConstant_pos hKS)
  · rw [integral_discreteMarginal p hB, hmean 0, hmean 1, hmean 2]
    norm_num [spinScore, show (1:Spin) ≠ 0 by decide, show (2:Spin) ≠ 0 by decide]
  · exact hmean 0
  · have hB₂ (o : Observation ℓ) : |f o^2| ≤ B^2 := by
      rw [abs_of_nonneg (sq_nonneg _)]
      have hh : |f o| ≤ B := hB o
      nlinarith [hh, sq_abs (f o), abs_nonneg (f o)]
    rw [integral_discreteMarginal p hB₂]
    linarith [hsecond 0, hsecond 1, hsecond 2]

theorem regular_reconstructs_above_KS (b : ℕ) (lam : ℝ) (hlam : Admissible lam)
    (hKS : 1 < (b:ℝ)*lam^2) : Reconstructs lam hlam (PMF.pure b) := by
  refine ⟨⨅ ℓ, advantage lam hlam (PMF.pure b) ℓ, ?_, advantage_tendsto _ _ _⟩
  have he : 1/(3*ksConstant b lam) ≤ ⨅ ℓ, advantage lam hlam (PMF.pure b) ℓ := by
    exact le_ciInf (fun ℓ ↦ regular_estimator_advantage b lam hlam hKS ℓ)
  exact (div_pos (by norm_num) (mul_pos (by norm_num) (ksConstant_pos hKS))).trans_le he

end ThreeState.TreeClauses.Tree

end

end OAI
