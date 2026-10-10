import Mathlib
import OAI.Probability.GaussianInformation.Dyadic.SmallBalls

namespace OAI
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
open MeasureTheory Metric Set
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace RepeatedLocalization
open Metric

noncomputable def tubeWeightConstant (n : ℕ) (B : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (B * tubeConstant^n) ^ (1/2 : ℝ)

lemma tubeWeightConstant_ne_top (n : ℕ) (B : ℝ) : tubeWeightConstant n B ≠ ∞ := by
  exact ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top

lemma weighted_dyadic_tube_tail {n : ℕ} (hn : 0 < n) (Q : Cell n)
    (μ : Measure (Coordinate n)) (hsupport : μ (cellSet Q)ᶜ = 0)
    {B : ℝ} (hB : 0 ≤ B) (hspread : DyadicSpread μ Q B)
    (h : Coordinate n → ℝ) (hh : Measurable h) (hnorm : eLpNorm h 2 μ ≤ 1)
    (V : AffineSubspace ℝ (EuclideanSpace ℝ (Fin (n+1))))
    (hV : (V : Set (EuclideanSpace ℝ (Fin (n+1)))).Nonempty)
    (k : ℕ) (he : Module.finrank ℝ V.direction + 2*(k+1) ≤ n/2) (j : ℕ) :
    (μ.withDensity (fun z => ENNReal.ofReal |h z|))
      {z | infDist (normalizedChart Q z) (V : Set (EuclideanSpace ℝ (Fin (n+1)))) ≤ (1/2:ℝ)^j}
      ≤ tubeWeightConstant n B * ENNReal.ofReal ((1/2:ℝ)^((k+1)*j)) := by
  have hmeas := (continuous_infDist_pt (V : Set (EuclideanSpace ℝ (Fin (n+1))))).measurable.comp
    (normalizedChart_measurable Q)
  refine (weightedMeasure_apply_le_sqrt μ h hh hnorm _
    (measurableSet_le hmeas measurable_const)).trans ?_
  refine (ENNReal.rpow_le_rpow (dyadic_tube_tail hn Q μ hsupport hB hspread V hV _ he j)
    (by norm_num : (0:ℝ) ≤ 1/2)).trans_eq ?_
  rw [ENNReal.ofReal_mul (mul_nonneg hB (pow_nonneg (le_trans (by norm_num) tubeConstant_ge_one) _)),
    ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 1/2)]
  congr 1
  have hp : (1/2:ℝ)^(2*(k+1)*j) = ((1/2:ℝ)^((k+1)*j))^2 := by
    rw [← pow_mul]
    congr 1
    ring
  rw [hp, ENNReal.ofReal_pow (by positivity), ← ENNReal.rpow_natCast,
    ← ENNReal.rpow_mul]
  norm_num

lemma weighted_affine_inverseMoment {n : ℕ} (hn : 0 < n) (Q : Cell n)
    (μ : Measure (Coordinate n)) [IsProbabilityMeasure μ]
    (hsupport : μ (cellSet Q)ᶜ = 0) {B : ℝ} (hB : 0 ≤ B) (hspread : DyadicSpread μ Q B)
    (h : Coordinate n → ℝ) (hh : Measurable h) (hnorm : eLpNorm h 2 μ ≤ 1)
    (V : AffineSubspace ℝ (EuclideanSpace ℝ (Fin (n+1))))
    (hV : (V : Set (EuclideanSpace ℝ (Fin (n+1)))).Nonempty)
    (k : ℕ) (hk : 0 < k) (he : Module.finrank ℝ V.direction + 2*(k+1) ≤ n/2) :
    (∫⁻ z, ENNReal.ofReal ((infDist (normalizedChart Q z)
      (V : Set (EuclideanSpace ℝ (Fin (n+1)))))⁻¹ ^ k)
      ∂(μ.withDensity (fun z => ENNReal.ofReal |h z|))) ≤
      1 + tubeWeightConstant n B * ENNReal.ofReal ((2:ℝ)^(k+1)) := by
  refine (inverseMoment_of_dyadic_tails _ _
    ((continuous_infDist_pt _).measurable.comp (normalizedChart_measurable Q))
    (fun _ => infDist_nonneg) k hk _
    (weighted_dyadic_tube_tail hn Q μ hsupport hB hspread h hh hnorm V hV k he)).trans ?_
  gcongr
  exact weightedMeasure_mass_le_one μ h hh hnorm

lemma weighted_affine_zero_null {n : ℕ} (hn : 0 < n) (Q : Cell n)
    (μ : Measure (Coordinate n)) (hsupport : μ (cellSet Q)ᶜ = 0)
    {B : ℝ} (hB : 0 ≤ B) (hspread : DyadicSpread μ Q B)
    (h : Coordinate n → ℝ) (hh : Measurable h) (hnorm : eLpNorm h 2 μ ≤ 1)
    (V : AffineSubspace ℝ (EuclideanSpace ℝ (Fin (n+1))))
    (hV : (V : Set (EuclideanSpace ℝ (Fin (n+1)))).Nonempty)
    (k : ℕ) (he : Module.finrank ℝ V.direction + 2*(k+1) ≤ n/2) :
    (μ.withDensity (fun z => ENNReal.ofReal |h z|))
      {z | infDist (normalizedChart Q z) (V : Set (EuclideanSpace ℝ (Fin (n+1)))) = 0} = 0 := by
  exact zeroSet_null_of_dyadic_tails _ _ k _ (tubeWeightConstant_ne_top n B)
    (weighted_dyadic_tube_tail hn Q μ hsupport hB hspread h hh hnorm V hV k he)

lemma weighted_affine_inverseMoment_ennreal {n : ℕ} (hn : 0 < n) (Q : Cell n)
    (μ : Measure (Coordinate n)) [IsProbabilityMeasure μ]
    (hsupport : μ (cellSet Q)ᶜ = 0) {B : ℝ} (hB : 0 ≤ B) (hspread : DyadicSpread μ Q B)
    (h : Coordinate n → ℝ) (hh : Measurable h) (hnorm : eLpNorm h 2 μ ≤ 1)
    (V : AffineSubspace ℝ (EuclideanSpace ℝ (Fin (n+1))))
    (hV : (V : Set (EuclideanSpace ℝ (Fin (n+1)))).Nonempty)
    (k : ℕ) (hk : 0 < k) (he : Module.finrank ℝ V.direction + 2*(k+1) ≤ n/2) :
    (∫⁻ z, (ENNReal.ofReal (infDist (normalizedChart Q z)
      (V : Set (EuclideanSpace ℝ (Fin (n+1))))))⁻¹ ^ k
      ∂(μ.withDensity (fun z => ENNReal.ofReal |h z|))) ≤
      1 + tubeWeightConstant n B * ENNReal.ofReal ((2:ℝ)^(k+1)) := by
  have hzero : ∀ᵐ z ∂(μ.withDensity (fun z => ENNReal.ofReal |h z|)),
      infDist (normalizedChart Q z) (V : Set (EuclideanSpace ℝ (Fin (n+1)))) ≠ 0 := by
    apply ae_iff.mpr
    simpa only [not_not] using weighted_affine_zero_null hn Q μ hsupport hB hspread h hh hnorm V hV k he
  have heq : (fun z => (ENNReal.ofReal (infDist (normalizedChart Q z)
      (V : Set (EuclideanSpace ℝ (Fin (n+1))))))⁻¹ ^ k) =ᵐ[μ.withDensity (fun z => ENNReal.ofReal |h z|)]
      (fun z => ENNReal.ofReal ((infDist (normalizedChart Q z)
      (V : Set (EuclideanSpace ℝ (Fin (n+1)))))⁻¹ ^ k)) := by
    filter_upwards [hzero] with z hz
    rw [ENNReal.ofReal_pow (inv_nonneg.mpr infDist_nonneg),
      ENNReal.ofReal_inv_of_pos (lt_of_le_of_ne infDist_nonneg hz.symm)]
  rw [lintegral_congr_ae heq]
  exact weighted_affine_inverseMoment hn Q μ hsupport hB hspread h hh hnorm V hV k hk he

end RepeatedLocalization

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology

end OAI
