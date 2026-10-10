import OAI.NumberTheory.CubicMoment.Estimates.HuxleyGaussianKernel
import OAI.NumberTheory.CubicMoment.Estimates.HuxleyPhaseAlgebra
import OAI.NumberTheory.CubicMoment.Estimates.HuxleySchur

namespace OAI

/-! Expansion and Schur bound for the actual Gaussian-weighted dual polynomial. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

def huxleyDualPolynomial (P : Finset HuxleyLift) (v : HuxleyLift → ℂ) (n : ℤ × ℤ) : ℂ :=
  ∑ p ∈ P, v p*huxleyFrequencyPhase p.frequency (ofCoords n.1 n.2)

lemma huxley_weighted_phase_summable {a : ℝ} (ha : 0 < a) (x : ℂ) :
    Summable (fun n : ℤ × ℤ => (huxleyCoordinateWeight a n:ℂ)*
      huxleyFrequencyPhase x (ofCoords n.1 n.2)) := by
  simp_rw [huxleyCoordinateWeight_phase]
  exact summable_mul_of_summable_norm (summable_norm_huxleyGaussianFactor ha _)
    (summable_norm_huxleyGaussianFactor ha _)

lemma huxleyGaussianEnergy_expansion (a : ℝ) (P : Finset HuxleyLift)
    (v : HuxleyLift → ℂ) (n : ℤ × ℤ) :
    ((huxleyCoordinateWeight a n*‖huxleyDualPolynomial P v n‖^2:ℝ):ℂ) =
      ∑ p ∈ P, ∑ q ∈ P, (v p*star (v q))*
        ((huxleyCoordinateWeight a n:ℂ)*
          huxleyFrequencyPhase (p.frequency-q.frequency) (ofCoords n.1 n.2)) := by
  rw [Complex.ofReal_mul,Complex.ofReal_pow,← Complex.mul_conj']
  unfold huxleyDualPolynomial
  simp only [map_sum,map_mul,Finset.sum_mul,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_congr rfl
  intro q hq
  rw [huxleyFrequencyPhase_sub]
  simp only [starRingEnd_apply]
  ring

lemma huxleyGaussianEnergy_summable {a : ℝ} (ha : 0 < a) (P : Finset HuxleyLift)
    (v : HuxleyLift → ℂ) :
    Summable (fun n : ℤ × ℤ => huxleyCoordinateWeight a n*‖huxleyDualPolynomial P v n‖^2) := by
  have hs : Summable (fun n : ℤ × ℤ => ∑ p ∈ P, ∑ q ∈ P,
      (v p*star (v q))*((huxleyCoordinateWeight a n:ℂ)*
        huxleyFrequencyPhase (p.frequency-q.frequency) (ofCoords n.1 n.2))) :=
    summable_sum (fun p hp => summable_sum (fun q hq =>
      (huxley_weighted_phase_summable ha _).mul_left _))
  convert (Complex.hasSum_re hs.hasSum).summable using 1
  ext n
  rw [← huxleyGaussianEnergy_expansion]
  rfl

lemma huxleyGaussianEnergy_sum {a : ℝ} (ha : 0 < a) (P : Finset HuxleyLift)
    (v : HuxleyLift → ℂ) :
    Complex.ofReal (∑' n : ℤ × ℤ, huxleyCoordinateWeight a n*‖huxleyDualPolynomial P v n‖^2) =
      ∑ p ∈ P, ∑ q ∈ P, (v p*star (v q))*
        huxleyGaussianKernel a (p.frequency-q.frequency) := by
  rw [Complex.ofReal_tsum]
  simp_rw [huxleyGaussianEnergy_expansion]
  rw [Summable.tsum_finsetSum (fun p hp => summable_sum (fun q hq =>
    (huxley_weighted_phase_summable ha _).mul_left _))]
  apply Finset.sum_congr rfl
  intro p hp
  rw [Summable.tsum_finsetSum (fun q hq =>
    (huxley_weighted_phase_summable ha _).mul_left _)]
  apply Finset.sum_congr rfl
  intro q hq
  rw [tsum_mul_left]
  congr 1
  simp_rw [huxleyCoordinateWeight_phase]
  rfl

lemma huxleyGaussianEnergy_bound {a : ℝ} (ha : 0 < a) (Q : ℝ) (hQ : 0 < Q)
    (P : Finset HuxleyLift) (hred : ∀ p ∈ P, p.reduced Q)
    (hzero : ∀ p ∈ P, p.shift = 0) (v : HuxleyLift → ℂ) :
    (∑' n : ℤ × ℤ, huxleyCoordinateWeight a n*‖huxleyDualPolynomial P v n‖^2) ≤
      ((1/a)*huxleyGaussianConstant*(1+Q^2/((2/3:ℝ)*(Real.pi/a))))*
        ∑ p ∈ P, ‖v p‖^2 := by
  let t := (2/3:ℝ)*(Real.pi/a)
  have ht : 0 < t := by dsimp [t]; positivity
  have hs : 0 ≤ ∑' n : ℤ × ℤ,
      huxleyCoordinateWeight a n*‖huxleyDualPolynomial P v n‖^2 :=
    tsum_nonneg (fun n => mul_nonneg (Real.exp_pos _).le (sq_nonneg _))
  calc
    _ = ‖Complex.ofReal (∑' n : ℤ × ℤ,
        huxleyCoordinateWeight a n*‖huxleyDualPolynomial P v n‖^2)‖ := by
      rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hs]
    _ ≤ ∑ p ∈ P, ∑ q ∈ P,
        ‖v p‖*‖v q‖*‖huxleyGaussianKernel a (p.frequency-q.frequency)‖ := by
      rw [huxleyGaussianEnergy_sum ha]
      apply (norm_sum_le P (fun p => ∑ q ∈ P,
        (v p*star (v q))*huxleyGaussianKernel a (p.frequency-q.frequency))).trans
      apply Finset.sum_le_sum
      intro p hp
      simpa only [norm_mul,norm_star] using norm_sum_le P (fun q =>
        (v p*star (v q))*huxleyGaussianKernel a (p.frequency-q.frequency))
    _ ≤ ∑ p ∈ P, ∑ q ∈ P, ‖v p‖*‖v q‖*
        ((1/a)*huxleyPeriodizedGaussian t (p.frequency-q.frequency)) := by
      apply Finset.sum_le_sum
      intro p hp
      apply Finset.sum_le_sum
      intro q hq
      exact mul_le_mul_of_nonneg_left (huxleyGaussianKernel_norm_bound ha _)
        (mul_nonneg (_root_.norm_nonneg _) (_root_.norm_nonneg _))
    _ ≤ _ := by
      apply huxley_finite_schur
      · intro p hp q hq
        exact mul_nonneg (by positivity) (huxleyPeriodizedGaussian_nonneg _ _)
      · intro p hp q hq
        rw [show q.frequency-p.frequency = -(p.frequency-q.frequency) by ring,
          huxleyPeriodizedGaussian_neg]
      · intro p hp
        rw [← Finset.mul_sum]
        exact (mul_le_mul_of_nonneg_left
          (huxleyPeriodizedGaussian_row_bound Q hQ ht P hred hzero p.frequency)
          (by positivity)).trans_eq (by ring)

end CubicFirstMoment

end

end OAI
