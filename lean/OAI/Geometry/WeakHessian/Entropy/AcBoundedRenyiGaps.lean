import Mathlib
import OAI.Geometry.WeakHessian.Entropy.FiniteEntropy
import OAI.Geometry.WeakHessian.Entropy.RenyiKernel

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open Set Filter
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter Topology Bornology
open scoped InnerProductSpace
open Filter

attribute [local instance] Classical.propDecidable
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology
open Set Filter MeasureTheory InformationTheory
open scoped Topology

namespace WeakHessian
open InformationTheory

variable {X : Type*} [MeasurableSpace X]

lemma ac_of_bounded_renyi_gaps {m μ : Measure X} [IsFiniteMeasure m] [IsProbabilityMeasure μ]
    {a B : ℕ → ℝ} {L : ℝ} (ha : ∀ n, 0 < a n) (ha1 : ∀ n, a n < 1)
    (halim : Tendsto a atTop (𝓝 0)) (hB : Tendsto B atTop (𝓝 L))
    (hb : ∀ n, (1-∫ x, (μ.rnDeriv m x).toReal^(1-a n) ∂m)/(a n) ≤ B n) : μ ≪ m := by
  have hi : Integrable (fun x => (μ.rnDeriv m x).toReal) m := Measure.integrable_toReal_rnDeriv
  have hn : ∀ᵐ x ∂m, 0 ≤ (μ.rnDeriv m x).toReal := Eventually.of_forall fun x => ENNReal.toReal_nonneg
  have H := tendsto_integral_rpow_sub hi hn (fun n => (ha n).le) ha1 halim
  have Hm : 1 ≤ ∫ x, (μ.rnDeriv m x).toReal ∂m := by
    have Hl : Tendsto (fun n => 1-a n*B n) atTop (𝓝 (1:ℝ)) := by
      simpa using tendsto_const_nhds.sub (halim.mul hB)
    apply le_of_tendsto_of_tendsto' Hl H
    intro n
    have HH := (div_le_iff₀ (ha n)).mp (hb n)
    nlinarith
  rw [Measure.integral_toReal_rnDeriv',probReal_univ (μ := μ)] at Hm
  have hz : (μ.singularPart m).real Set.univ = 0 := by
    have hnn := measureReal_nonneg (μ := μ.singularPart m) (s := Set.univ)
    linarith
  have hzero : μ.singularPart m = 0 := by
    apply Measure.measure_univ_eq_zero.mp
    exact (measureReal_eq_zero_iff (measure_ne_top _ _)).mp hz
  exact (Measure.singularPart_eq_zero μ m).mp hzero

lemma finiteEntropy_of_renyi_gaps {m μ : Measure X} [IsFiniteMeasure m] [IsProbabilityMeasure μ]
    {a B : ℕ → ℝ} {L : ℝ} (ha : ∀ n, 0 < a n) (ha1 : ∀ n, a n < 1)
    (halim : Tendsto a atTop (𝓝 0)) (hB : Tendsto B atTop (𝓝 L))
    (hb : ∀ n, (1-∫ x, (μ.rnDeriv m x).toReal^(1-a n) ∂m)/(a n) ≤ B n) :
    FiniteEntropy m μ ∧ entropyReal m μ ≤ L := by
  have hac := ac_of_bounded_renyi_gaps ha ha1 halim hB hb
  have hi : Integrable (fun x => (μ.rnDeriv m x).toReal) m := Measure.integrable_toReal_rnDeriv
  have hn : ∀ᵐ x ∂m, 0 ≤ (μ.rnDeriv m x).toReal := Eventually.of_forall fun x => ENNReal.toReal_nonneg
  have hh : ∀ n, (∫ x, renyiKernel (a n) (μ.rnDeriv m x).toReal ∂m) ≤ B n+m.real Set.univ-1 := by
    intro n
    simp only [renyiKernel]
    rw [integral_sub,integral_add,integral_div,integral_sub,
      Measure.integral_toReal_rnDeriv hac,probReal_univ (μ := μ),integral_const,smul_eq_mul,mul_one]
    · linarith [hb n]
    · exact hi
    · exact integrable_rpow_sub hi hn (ha n).le (ha1 n)
    · exact (hi.sub (integrable_rpow_sub hi hn (ha n).le (ha1 n))).div_const _
    · exact integrable_const 1
    · exact ((hi.sub (integrable_rpow_sub hi hn (ha n).le (ha1 n))).div_const _).add (integrable_const 1)
    · exact hi
  obtain ⟨hki,hkl⟩ := integral_klFun_le_of_renyi_bounds hi hn ha ha1 halim hh
    ((hB.add_const _).sub_const _)
  have hll := (integrable_klFun_rnDeriv_iff hac).mp hki
  refine ⟨⟨hac,hll⟩,?_⟩
  rw [integral_klFun_rnDeriv hac hll,probReal_univ (μ := μ)] at hkl
  change (∫ x, llr μ m x ∂μ) ≤ L
  linarith


lemma density_mul_neg_rpow {a r : ℝ} (ha : a < 1) (hr : 0 ≤ r) :
    r*r^(-a) = r^(1-a) := by
  rw [sub_eq_add_neg,Real.rpow_add' hr (by linarith : 1 + -a ≠ 0),Real.rpow_one]

lemma integral_density_neg_rpow {m μ : Measure X} [IsFiniteMeasure m] [IsFiniteMeasure μ]
    (hac : μ ≪ m) {a : ℝ} (ha : a < 1) :
    (∫ x, (μ.rnDeriv m x).toReal^(-a) ∂μ) =
      ∫ x, (μ.rnDeriv m x).toReal^(1-a) ∂m := by
  rw [← integral_toReal_rnDeriv_mul hac]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => density_mul_neg_rpow ha ENNReal.toReal_nonneg

lemma integrable_density_neg_rpow {m μ : Measure X} [IsFiniteMeasure m] [IsFiniteMeasure μ]
    (hac : μ ≪ m) {a : ℝ} (ha : 0 ≤ a) (ha1 : a < 1) :
    Integrable (fun x => (μ.rnDeriv m x).toReal^(-a)) μ := by
  apply (integrable_toReal_rnDeriv_mul_iff hac).mp
  exact (integrable_rpow_sub Measure.integrable_toReal_rnDeriv
    (Eventually.of_forall fun x => ENNReal.toReal_nonneg) ha ha1).congr
      (Eventually.of_forall fun x => (density_mul_neg_rpow ha1 ENNReal.toReal_nonneg).symm)

lemma integrable_inverse_density {m μ : Measure X} [IsFiniteMeasure m] [IsFiniteMeasure μ]
    (hac : μ ≪ m) : Integrable (fun x => ((μ.rnDeriv m x).toReal)⁻¹) μ := by
  apply (integrable_toReal_rnDeriv_mul_iff hac).mp
  apply (integrable_const (1:ℝ)).mono'
  · exact ((Measure.measurable_rnDeriv μ m).ennreal_toReal.mul
      (Measure.measurable_rnDeriv μ m).ennreal_toReal.inv).aestronglyMeasurable
  · exact Eventually.of_forall fun x => by
      by_cases hz : (μ.rnDeriv m x).toReal = 0
      · simp [hz]
      · simp [hz]

lemma density_pos_ae {m μ : Measure X} [SigmaFinite m] [IsFiniteMeasure μ]
    (hac : μ ≪ m) : ∀ᵐ x ∂μ, 0 < (μ.rnDeriv m x).toReal := by
  filter_upwards [Measure.rnDeriv_pos hac, hac.ae_le (Measure.rnDeriv_lt_top μ m)] with x hp ht
  exact ENNReal.toReal_pos hp.ne' ht.ne

lemma tendsto_integral_weighted_density_neg_rpow {Y : Type*} [MeasurableSpace Y]
    {m μ : Measure X} [IsFiniteMeasure m] [IsFiniteMeasure μ]
    {π : Measure Y} [IsFiniteMeasure π] (hac : μ ≪ m) {e : Y → X} (he : Measurable e)
    (hmap : Measure.map e π = μ) {ψ : Y → ℝ} (hψ : AEStronglyMeasurable ψ π)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ᵐ y ∂π, |ψ y| ≤ C)
    {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) (ha1 : ∀ n, a n ≤ 1)
    (halim : Tendsto a atTop (𝓝 0)) :
    Tendsto (fun n => ∫ y, ψ y*(μ.rnDeriv m (e y)).toReal^(-a n) ∂π) atTop
      (𝓝 (∫ y, ψ y ∂π)) := by
  have hi : Integrable (fun y => ((μ.rnDeriv m (e y)).toReal)⁻¹) π := by
    have H := integrable_inverse_density hac
    have H' : Integrable (fun x => ((μ.rnDeriv m x).toReal)⁻¹) (Measure.map e π) := by
      simpa only [hmap] using H
    exact H'.comp_measurable he
  have hp : ∀ᵐ y ∂π, 0 < (μ.rnDeriv m (e y)).toReal := by
    have H := density_pos_ae hac
    have H' : ∀ᵐ x ∂Measure.map e π, 0 < (μ.rnDeriv m x).toReal := by
      simpa only [hmap] using H
    exact ae_of_ae_map he.aemeasurable H'
  apply tendsto_integral_of_dominated_convergence (fun y => C*(1+((μ.rnDeriv m (e y)).toReal)⁻¹))
  · intro n
    exact hψ.mul (((Measure.measurable_rnDeriv μ m).comp he).ennreal_toReal.pow_const _).aestronglyMeasurable
  · exact ((integrable_const 1).add hi).const_mul C
  · intro n
    filter_upwards [hb,hp] with y hby hpy
    rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (Real.rpow_nonneg hpy.le _)]
    apply (mul_le_mul_of_nonneg_right hby (Real.rpow_nonneg hpy.le _)).trans
    apply mul_le_mul_of_nonneg_left _ hC
    rw [Real.rpow_neg_eq_inv_rpow]
    have H := rpow_sub_le_add_one (show 0 ≤ 1-a n by linarith [ha1 n])
      (show 1-a n ≤ 1 by linarith [ha n]) (inv_nonneg.mpr hpy.le)
    simpa only [sub_sub_cancel,add_comm] using H
  · filter_upwards [hp] with y hy
    have H := (Real.continuous_const_rpow hy.ne').tendsto 0
    have H' := H.comp (by simpa using halim.neg)
    simpa only [neg_zero,Real.rpow_zero,mul_one,Function.comp_def] using
      tendsto_const_nhds.mul H'
end WeakHessian

open Set Filter
open scoped Topology

end

end OAI
