import Mathlib
import OAI.Probability.ThreeStateClauses.RegularStatistics
import OAI.Probability.ThreeStateClauses.OffspringLaws
import OAI.Probability.ThreeStateClauses.PoissonMoments
import OAI.Probability.ThreeStateClauses.CountableStatistics

namespace OAI

/-! Poisson Reconstruction. -/

open scoped BigOperators ENNReal NNReal Topology
open Filter
noncomputable section
open Set MeasureTheory
open scoped BigOperators NNReal
namespace ThreeState.TreeClauses.Tree
open ThreeState.TreeClauses.Experiment ThreeState.TreeClauses.Probability

def orderedStatistic (d lam : ℝ) : (ℓ : ℕ) → OrderedObservation ℓ → ℝ
  | 0, i => spinScore i
  | ℓ+1, ⟨_,v⟩ => (∑ j, orderedStatistic d lam ℓ (v j))/(d*lam)

def observedStatistic (d lam : ℝ) : (ℓ : ℕ) → Observation ℓ → ℝ
  | 0, i => spinScore i
  | ℓ+1, s => (s.map (observedStatistic d lam ℓ)).sum/(d*lam)

lemma observedStatistic_forget (d lam : ℝ) (ℓ : ℕ) (v : OrderedObservation ℓ) :
    observedStatistic d lam ℓ (forgetOrdered ℓ v) = orderedStatistic d lam ℓ v := by
  induction ℓ with
  | zero => rfl
  | succ ℓ ih =>
    rcases v with ⟨n,v⟩
    simp only [forgetOrdered, observedStatistic, orderedStatistic]
    congr 1
    simp only [Multiset.map_coe, Multiset.sum_coe, List.map_ofFn, Function.comp_def, ih, List.sum_ofFn]

lemma poissonStatistic_square_integrable (d : ℝ≥0) (lam : ℝ) (hlam : Admissible lam)
    (ℓ : ℕ) (i : Spin) :
    Integrable (fun v ↦ orderedStatistic d lam ℓ v^2)
      (orderedLaw (poissonPMF d) lam hlam ℓ i).toMeasure := by
  induction ℓ generalizing i with
  | zero => exact Integrable.of_finite
  | succ ℓ ih =>
    let p := (channel lam hlam i).bind (orderedLaw (poissonPMF d) lam hlam ℓ)
    have hp : Integrable (fun v ↦ orderedStatistic d lam ℓ v^2) p.toMeasure :=
      pmf_integrable_bind_finite _ _ ih
    change Integrable (fun z : Σ n, Fin n → OrderedObservation ℓ ↦
      ((∑ j, orderedStatistic d lam ℓ (z.2 j))/((d:ℝ)*lam))^2)
      (sigmaPMF (poissonPMF d) (fun n ↦ productPMF (fun _ : Fin n ↦ p))).toMeasure
    apply sigmaPMF_integrable
    · intro n
      simpa only [div_pow] using (product_square_sum_integrable p hp n).div_const (((d:ℝ)*lam)^2)
    · change Integrable (fun n ↦ ∫ v : Fin n → OrderedObservation ℓ,
        |((∑ j, orderedStatistic d lam ℓ (v j))/((d:ℝ)*lam))^2|
        ∂(productPMF (fun _ : Fin n ↦ p)).toMeasure) (poissonPMF d).toMeasure
      have hab (x : ℝ) : |x^2| = x^2 := abs_of_nonneg (sq_nonneg x)
      simp_rw [hab, div_pow, integral_div,
        integral_product_sq_sum_integrable p hp]
      exact (((poisson_integrable_first d).mul_const _).add
        (((poisson_integrable_second d).sub (poisson_integrable_first d)).mul_const _)).div_const _

lemma poissonStatistic_mean (d : ℝ≥0) (hd : (d:ℝ) ≠ 0) (lam : ℝ) (hlam : Admissible lam)
    (hl : lam ≠ 0) (ℓ : ℕ) (i : Spin) :
    (∫ v, orderedStatistic d lam ℓ v
      ∂(orderedLaw (poissonPMF d) lam hlam ℓ i).toMeasure) = spinScore i := by
  induction ℓ generalizing i with
  | zero =>
    change (∫ v : Spin, spinScore v ∂(PMF.pure i).toMeasure) = spinScore i
    rw [PMF.toMeasure_pure, integral_dirac]
  | succ ℓ ih =>
    let p := (channel lam hlam i).bind (orderedLaw (poissonPMF d) lam hlam ℓ)
    have hp₂ : Integrable (fun v ↦ orderedStatistic d lam ℓ v^2) p.toMeasure :=
      pmf_integrable_bind_finite _ _ (poissonStatistic_square_integrable d lam hlam ℓ)
    have hp := pmf_integrable_of_square p hp₂
    have hi := pmf_integrable_of_square _ (poissonStatistic_square_integrable d lam hlam (ℓ+1) i)
    change (∫ z : Σ n, Fin n → OrderedObservation ℓ,
      (∑ j, orderedStatistic d lam ℓ (z.2 j))/((d:ℝ)*lam)
      ∂(sigmaPMF (poissonPMF d) (fun n ↦ productPMF (fun _ : Fin n ↦ p))).toMeasure) = _
    change Integrable (fun z : Σ n, Fin n → OrderedObservation ℓ ↦
      (∑ j, orderedStatistic d lam ℓ (z.2 j))/((d:ℝ)*lam))
      (sigmaPMF (poissonPMF d) (fun n ↦ productPMF (fun _ : Fin n ↦ p))).toMeasure at hi
    rw [integral_sigmaPMF_integrable _ _ hi]
    simp_rw [integral_div, integral_product_sum_integrable p hp]
    have hm : (∫ v, orderedStatistic d lam ℓ v ∂p.toMeasure) = lam*spinScore i := by
      rw [integral_pmf_bind_integrable _ _ hp]
      simp_rw [ih]
      exact channel_spinScore lam hlam i
    rw [hm, integral_mul_const, poisson_integral_first]
    field_simp

end ThreeState.TreeClauses.Tree

end 

noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators Topology NNReal
namespace ThreeState.TreeClauses.Tree
open ThreeState.TreeClauses.Experiment ThreeState.TreeClauses.Probability

def poissonKSConstant (d lam : ℝ) : ℝ := 4*(d*lam^2)/(d*lam^2-1)

lemma poissonKSConstant_pos {d lam : ℝ} (hKS : 1 < d*lam^2) : 0 < poissonKSConstant d lam := by
  unfold poissonKSConstant; positivity

lemma poissonKSConstant_ge_four {d lam : ℝ} (hKS : 1 < d*lam^2) : 4 ≤ poissonKSConstant d lam := by
  rw [poissonKSConstant, le_div_iff₀ (by linarith)]
  linarith

lemma poissonKSConstant_identity {d lam : ℝ} (hKS : 1 < d*lam^2) :
    poissonKSConstant d lam*(d*lam^2-1) = 4*(d*lam^2) := by
  rw [poissonKSConstant, div_mul_cancel₀ _ (by linarith)]

lemma poissonStatistic_second (d : ℝ≥0) (lam : ℝ) (hlam : Admissible lam)
    (hKS : 1 < (d:ℝ)*lam^2) (ℓ : ℕ) (i : Spin) :
    (∫ v, orderedStatistic d lam ℓ v^2
      ∂(orderedLaw (poissonPMF d) lam hlam ℓ i).toMeasure) ≤ poissonKSConstant d lam := by
  have hd : 0 < (d:ℝ) := by
    by_contra h
    have he : (d:ℝ) = 0 := le_antisymm (not_lt.mp h) d.coe_nonneg
    norm_num [he] at hKS
  have hl : lam ≠ 0 := by intro h; norm_num [h] at hKS
  have hden : 0 < ((d:ℝ)*lam)^2 := sq_pos_of_ne_zero (mul_ne_zero hd.ne' hl)
  induction ℓ generalizing i with
  | zero =>
    change (∫ v : Spin, spinScore v^2 ∂(PMF.pure i).toMeasure) ≤ _
    rw [PMF.toMeasure_pure, integral_dirac]
    exact (spinScore_square i).trans (poissonKSConstant_ge_four hKS)
  | succ ℓ ih =>
    let p := (channel lam hlam i).bind (orderedLaw (poissonPMF d) lam hlam ℓ)
    have hp₂ : Integrable (fun v ↦ orderedStatistic d lam ℓ v^2) p.toMeasure :=
      pmf_integrable_bind_finite _ _ (poissonStatistic_square_integrable d lam hlam ℓ)
    have hp := pmf_integrable_of_square p hp₂
    have hmean : (∫ v, orderedStatistic d lam ℓ v ∂p.toMeasure) = lam*spinScore i := by
      rw [integral_pmf_bind_integrable _ _ hp]
      simp_rw [poissonStatistic_mean d hd.ne' lam hlam hl ℓ]
      exact channel_spinScore lam hlam i
    have hsecond : (∫ v, orderedStatistic d lam ℓ v^2 ∂p.toMeasure) ≤ poissonKSConstant d lam := by
      rw [integral_pmf_bind_integrable _ _ hp₂]
      exact (integral_mono Integrable.of_finite (integrable_const _) ih).trans_eq (by simp)
    have hi := poissonStatistic_square_integrable d lam hlam (ℓ+1) i
    change (∫ z : Σ n, Fin n → OrderedObservation ℓ,
      ((∑ j, orderedStatistic d lam ℓ (z.2 j))/((d:ℝ)*lam))^2
      ∂(sigmaPMF (poissonPMF d) (fun n ↦ productPMF (fun _ : Fin n ↦ p))).toMeasure) ≤ _
    change Integrable (fun z : Σ n, Fin n → OrderedObservation ℓ ↦
      ((∑ j, orderedStatistic d lam ℓ (z.2 j))/((d:ℝ)*lam))^2)
      (sigmaPMF (poissonPMF d) (fun n ↦ productPMF (fun _ : Fin n ↦ p))).toMeasure at hi
    rw [integral_sigmaPMF_integrable _ _ hi]
    simp_rw [div_pow, integral_div, integral_product_sq_sum_integrable p hp₂]
    rw [hmean, integral_add
      (f := fun n : ℕ ↦ (n:ℝ)*(∫ v, orderedStatistic d lam ℓ v^2 ∂p.toMeasure))
      (g := fun n : ℕ ↦ ((n:ℝ)^2-n)*(lam*spinScore i)^2)
      ((poisson_integrable_first d).mul_const _)
      (((poisson_integrable_second d).sub (poisson_integrable_first d)).mul_const _),
      integral_mul_const, integral_mul_const, poisson_integral_first, poisson_integral_factorial_second]
    apply (div_le_iff₀ hden).2
    have hs := mul_le_mul_of_nonneg_left (spinScore_square i) (sq_nonneg ((d:ℝ)*lam))
    have hm := mul_le_mul_of_nonneg_left hsecond hd.le
    have hid := congrArg (fun x : ℝ ↦ x*(d:ℝ)) (poissonKSConstant_identity hKS)
    nlinarith only [hs,hm,hid]

lemma poisson_estimator_advantage (d : ℝ≥0) (lam : ℝ) (hlam : Admissible lam)
    (hKS : 1 < (d:ℝ)*lam^2) (ℓ : ℕ) :
    1/(3*poissonKSConstant d lam) ≤ advantage lam hlam (poissonPMF d) ℓ := by
  have hd : (d:ℝ) ≠ 0 := by intro h; norm_num [h] at hKS
  have hl : lam ≠ 0 := by intro h; norm_num [h] at hKS
  let p := observationLaw lam hlam (poissonPMF d) ℓ
  let f := observedStatistic d lam ℓ
  have hInt (i : Spin) : Integrable (fun o ↦ f o^2) (p i).toMeasure := by
    dsimp [p, f]
    rw [← orderedLaw_forget _ lam hlam ℓ i, pmf_integrable_map_iff]
    simpa only [observedStatistic_forget] using poissonStatistic_square_integrable d lam hlam ℓ i
  have hmean (i : Spin) : (∫ o, f o ∂(p i).toMeasure) = spinScore i := by
    dsimp [p, f]
    rw [← orderedLaw_forget _ lam hlam ℓ i, integral_pmf_map]
    simp_rw [observedStatistic_forget]
    exact poissonStatistic_mean d hd lam hlam hl ℓ i
  have hsecond (i : Spin) : (∫ o, f o^2 ∂(p i).toMeasure) ≤ poissonKSConstant d lam := by
    dsimp [p, f]
    rw [← orderedLaw_forget _ lam hlam ℓ i, integral_pmf_map]
    simp_rw [observedStatistic_forget]
    exact poissonStatistic_second d lam hlam hKS ℓ i
  rw [advantage_eq_integral]
  apply estimator_tv_lower_integrable (p := p) hInt (poissonKSConstant_pos hKS)
  · rw [integral_discreteMarginal_integrable p (fun i ↦ pmf_integrable_of_square _ (hInt i)),
      hmean 0, hmean 1, hmean 2]
    norm_num [spinScore, show (1:Spin) ≠ 0 by decide, show (2:Spin) ≠ 0 by decide]
  · exact hmean 0
  · rw [integral_discreteMarginal_integrable p hInt]
    linarith [hsecond 0, hsecond 1, hsecond 2]

theorem poisson_reconstructs_above_KS (d : ℝ≥0) (lam : ℝ) (hlam : Admissible lam)
    (hKS : 1 < (d:ℝ)*lam^2) : Reconstructs lam hlam (poissonPMF d) := by
  refine ⟨⨅ ℓ, advantage lam hlam (poissonPMF d) ℓ, ?_, advantage_tendsto _ _ _⟩
  have he : 1/(3*poissonKSConstant d lam) ≤ ⨅ ℓ, advantage lam hlam (poissonPMF d) ℓ := by
    exact le_ciInf (fun ℓ ↦ poisson_estimator_advantage d lam hlam hKS ℓ)
  exact (div_pos (by norm_num) (mul_pos (by norm_num) (poissonKSConstant_pos hKS))).trans_le he

end ThreeState.TreeClauses.Tree

end

end OAI
