import OAI.Analysis.IrrationalRotation.Sampling.CircleDigitDensity
import OAI.Analysis.IrrationalRotation.Sampling.CircleDigitDisintegration

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace Invariant233.CircleDigitCoupling
open CouplingMarginalBounds CouplingMixture OneCoordinateCoupling

lemma baseLaw_le_intervalLaw_of_subset {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1)
    {s : Set ℝ} (hs : s ⊆ Ico a b) : baseLaw s ≤ intervalLaw a b s := by
  rw [intervalLaw_eq_base_cond ha hb, ProbabilityTheory.cond_apply measurableSet_Ico,
    inter_eq_right.mpr hs]
  have hmass : baseLaw (Ico a b) ≤ 1 := by
    simpa using (measure_mono (subset_univ (Ico a b)) : baseLaw (Ico a b) ≤ baseLaw univ)
  simpa only [one_mul, mul_one, mul_comm] using
    mul_le_mul_right (ENNReal.one_le_inv.mpr hmass) (baseLaw s)

variable {κ m a b t : ℝ}
    (hκ0 : 0 ≤ κ) (hκ : κ ≤ 1 / 100) (hm : 100 ≤ m)
    (ha : 1 / m ≤ a) (ha' : a ≤ 1 / 4)
    (hb : 1 / m ≤ b) (hb' : b ≤ 1 / 4)
    (ht0 : 0 ≤ t) (ht : t ≤ 1)
include hκ0 hκ hm ha ha' hb hb' ht0 ht

lemma label_posterior_lower_of_bin (side : Bool) (r : ℕ) [NeZero r]
    (d : Fin r) (l : Label)
    (hbin : baseLaw (bin r d) ≤ endpointLaw side m a b l (bin r d)) :
    labelMass κ m a b t l / 10 ≤ labelsGivenDigit side r κ m a b t d {l} := by
  rw [labelsGivenDigit_singleton]
  have h0 : baseLaw (bin r d) ≠ 0 := by rw [baseLaw_bin]; simp
  have hfin : baseLaw (bin r d) ≠ ∞ := measure_ne_top _ _
  calc
    _ = (labelMass κ m a b t l * baseLaw (bin r d)) /
      (10 * baseLaw (bin r d)) := (ENNReal.mul_div_mul_right _ _ h0 hfin).symm
    _ ≤ _ := ENNReal.div_le_div (mul_le_mul_right hbin _)
      (digitWeight_total_le_ten hκ0 hκ hm ha ha' hb hb' ht0 ht side r d)

lemma top_posterior_lower (r : ℕ) [NeZero r] (d : Fin r) (which : Bool)
    {z u : ℝ} (hz : z ∈ bin r d) (hzu : z < u)
    (hu : u ≤ 1 - width a b which) (hsmall : 1 / (r : ℝ) < width a b which / 2) :
    ENNReal.ofReal (rho κ m (width a b which)) / 10 ≤
      labelsGivenDigit false r κ m a b t d {topLabel which} := by
  have hm0 : 0 < m := by linarith
  have ha0 := width_pos hm0 ha
  have hb0 := width_pos hm0 hb
  have hsubset := bin_subset_top_left d hz hzu hu hsmall
  have hlike : baseLaw (bin r d) ≤ endpointLaw false m a b (topLabel which) (bin r d) := by
    cases which <;> simp only [topLabel, endpointLaw, Bool.false_eq_true, ite_false,
      ite_true, leftLaw] <;> simp only [width, Bool.false_eq_true, ite_false, ite_true] at hsubset <;> apply baseLaw_le_intervalLaw_of_subset
    all_goals solve | norm_num | linarith | exact hsubset
  have hpost := label_posterior_lower_of_bin hκ0 hκ hm ha ha' hb hb' ht0 ht false r d (topLabel which) hlike
  cases which <;> simpa [labelMass, topLabel, componentProbabilities, width] using hpost

lemma bottom_posterior_lower (r : ℕ) [NeZero r] (d : Fin r) (which : Bool)
    {z u : ℝ} (hz : z ∈ bin r d) (hzu : u ≤ z)
    (hu : width a b which ≤ u) (hsmall : 1 / (r : ℝ) < width a b which / 2) :
    ENNReal.ofReal (rho κ m (width a b which)) / 10 ≤
      labelsGivenDigit true r κ m a b t d {bottomLabel which} := by
  have hm0 : 0 < m := by linarith
  have ha0 := width_pos hm0 ha
  have hb0 := width_pos hm0 hb
  have hsubset := bin_subset_bottom_right d hz hzu hu hsmall
  have hlike : baseLaw (bin r d) ≤ endpointLaw true m a b (bottomLabel which) (bin r d) := by
    cases which <;> simp only [bottomLabel, endpointLaw, Bool.false_eq_true, ite_false,
      ite_true, rightLaw] <;> simp only [width, Bool.false_eq_true, ite_false, ite_true] at hsubset <;> apply baseLaw_le_intervalLaw_of_subset
    all_goals solve | norm_num | linarith | exact hsubset
  have hpost := label_posterior_lower_of_bin hκ0 hκ hm ha ha' hb hb' ht0 ht true r d (bottomLabel which) hlike
  cases which <;> simpa [labelMass, bottomLabel, componentProbabilities, width] using hpost

end Invariant233.CircleDigitCoupling

end

end OAI
