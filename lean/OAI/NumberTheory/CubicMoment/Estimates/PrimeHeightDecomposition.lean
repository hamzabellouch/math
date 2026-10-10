import OAI.NumberTheory.CubicMoment.Estimates.PrimeModelTail
import OAI.NumberTheory.CubicMoment.Estimates.PrimeMellinTransfer

namespace OAI

/-! Exact low-height and dyadic-window decomposition of the sharp prime
comparison. The large-height model is controlled before any factorization
of the Gauss sum is used. -/
noncomputable section
open MeasureTheory Filter
open scoped BigOperators
namespace CubicFirstMoment

def finiteHeightLow (P : Finset Eisenstein) (c : Eisenstein → ℂ)
    (H T X₀ : ℝ) : ℂ :=
  ∑ p ∈ P, c p*heightFourierIntegral
    (fun t => cutoffHeightMultiplier H t*(heightPartitionBump (t/T):ℂ))
      (Real.log (norm p)-Real.log X₀)

def finiteHeightTail (P : Finset Eisenstein) (c : Eisenstein → ℂ)
    (H T X₀ : ℝ) : ℂ :=
  ∑ j ∈ Finset.range (heightWindowCount H T),
    ∑ p ∈ P, c p*heightFourierIntegral
      (fun t => cutoffHeightMultiplier H t*heightWindow (T*(3/2:ℝ)^j) t)
        (Real.log (norm p)-Real.log X₀)

lemma heightFourierIntegral_partition {H T : ℝ} (hH : 0 < H) (hT : 0 < T)
    (x : ℝ) :
    heightFourierIntegral (cutoffHeightMultiplier H) x =
      heightFourierIntegral
        (fun t => cutoffHeightMultiplier H t*(heightPartitionBump (t/T):ℂ)) x +
      ∑ j ∈ Finset.range (heightWindowCount H T), heightFourierIntegral
        (fun t => cutoffHeightMultiplier H t*heightWindow (T*(3/2:ℝ)^j) t) x := by
  simp only [heightFourierIntegral_eq]
  apply cutoffHeightMultiplier_integral_partition (B := 1) hH hT _
    (heightWindowCount_covers hH hT)
  · fun_prop
  · intro t
    simp only [Complex.norm_exp,Complex.mul_re,Complex.ofReal_re,
      Complex.ofReal_im,Complex.I_re,Complex.I_im,mul_zero,zero_mul,
      sub_self,Real.exp_zero]
    exact le_rfl

lemma finite_height_partition (P : Finset Eisenstein) (c : Eisenstein → ℂ)
    {H T : ℝ} (hH : 0 < H) (hT : 0 < T) (X₀ : ℝ) :
    (∑ p ∈ P, c p*heightFourierIntegral (cutoffHeightMultiplier H)
      (Real.log (norm p)-Real.log X₀)) =
      finiteHeightLow P c H T X₀ + finiteHeightTail P c H T X₀ := by
  simp_rw [heightFourierIntegral_partition hH hT]
  simp only [mul_add,Finset.mul_sum,Finset.sum_add_distrib,
    finiteHeightLow,finiteHeightTail]
  rw [Finset.sum_comm]

lemma finite_smooth_low_tail (P : Finset Eisenstein) (c : Eisenstein → ℂ)
    {H T X : ℝ} (hH : 0 < H) (hT : 0 < T) (hX : 0 < X)
    (hP : ∀ p ∈ P, p ≠ 0) :
    (∑ p ∈ P, c p*smoothLogInterval H (norm p/X)) =
      ((2*Real.pi:ℝ):ℂ)⁻¹*(finiteHeightLow P c H T X + finiteHeightTail P c H T X) := by
  rw [← finite_height_partition P c hH hT X,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  rw [smoothLogInterval_eq_height hH,
    Real.log_div (norm_pos_of_ne_zero (hP p hp)).ne' hX.ne']
  ring

lemma finiteHeightTail_linear (P : Finset Eisenstein) (c d : Eisenstein → ℂ)
    (z : ℂ) (H T X : ℝ) :
    finiteHeightTail P (fun p => c p-z*d p) H T X =
      finiteHeightTail P c H T X-z*finiteHeightTail P d H T X := by
  simp only [finiteHeightTail,sub_mul,Finset.sum_sub_distrib,
    Finset.mul_sum,mul_assoc]

def primeComparisonLowHeight (ℓ : ℤ) (H T X : ℝ) : ℂ :=
  finiteHeightLow (primeCutoff (4*X)) (primeComparisonCoefficient ℓ) H T X

def primeGaussHeightTail (ℓ : ℤ) (H T X : ℝ) : ℂ :=
  finiteHeightTail (primeCutoff (4*X)) (fun p => theta ℓ p*gaussAtPrime p) H T X

lemma sharp_prime_comparison_low_tail (ℓ : ℤ) {H T X : ℝ}
    (hH : 0 < H) (hT : 0 < T) (hX : 0 < X) :
    sharpDyadicPrimeComparison ℓ X =
      ((2*Real.pi:ℝ):ℂ)⁻¹*(primeComparisonLowHeight ℓ H T X +
        primeGaussHeightTail ℓ H T X - (cStar:ℂ)*
          primeModelWindowSum (primeCutoff (4*X)) (fun _ => 1) ℓ H T X) +
      ∑ p ∈ primeCutoff (4*X), primeComparisonCoefficient ℓ p*
        sharpIntervalError X H (norm p) := by
  have he (p : Eisenstein) : primeComparisonCoefficient ℓ p =
      theta ℓ p*gaussAtPrime p - (cStar:ℂ)*
        (theta ℓ p*((norm p^(-1/6:ℝ):ℝ):ℂ)) := by
    unfold primeComparisonCoefficient
    push_cast
    ring
  have hs : sharpDyadicPrimeComparison ℓ X =
      (∑ p ∈ primeCutoff (4*X), primeComparisonCoefficient ℓ p*smoothLogInterval H (norm p/X)) +
      ∑ p ∈ primeCutoff (4*X), primeComparisonCoefficient ℓ p*sharpIntervalError X H (norm p) := by
    rw [←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p hp
    unfold sharpIntervalError
    ring
  rw [hs,finite_smooth_low_tail _ _ hH hT hX
    (fun p hp => (mem_primeCutoff.mp hp).1.2.ne_zero)]
  have htail : finiteHeightTail (primeCutoff (4*X)) (primeComparisonCoefficient ℓ) H T X =
      primeGaussHeightTail ℓ H T X-(cStar:ℂ)*
        primeModelWindowSum (primeCutoff (4*X)) (fun _ => 1) ℓ H T X := by
    have hc : primeComparisonCoefficient ℓ = fun p =>
        theta ℓ p*gaussAtPrime p - (cStar:ℂ)*
          (theta ℓ p*((norm p^(-1/6:ℝ):ℝ):ℂ)) := funext he
    rw [hc]
    rw [finiteHeightTail_linear]
    simp only [primeGaussHeightTail,primeModelWindowSum,finiteHeightTail,one_mul]
  rw [htail]
  dsimp only [primeComparisonLowHeight]
  ring

theorem actual_prime_model_height_tail_isLittleO {C a δ : ℝ}
    (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (ha : 0 < a) (ha1 : a < 1) (hδ : 0 < δ) (ℓ : ℤ) :
    (fun X : ℝ => primeModelWindowSum (primeCutoff (4*X)) (fun _ => 1)
      ℓ (X^a) (X^δ) X) =o[atTop] firstMomentScale := by
  apply prime_model_large_height_isLittleO hMV hC (by norm_num : (0:ℝ) ≤ 1)
    ha ha1 hδ
  · intro X hX p hp
    exact mem_primeCutoff.mp hp
  · intro X hX p hp
    norm_num

theorem sharp_prime_comparison_sub_low_and_gauss_tail {C ρ δ : ℝ}
    (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hρ : 0 < ρ) (hρ1 : ρ < 5/6) (hδ : 0 < δ) (ℓ : ℤ) :
    (fun X : ℝ => sharpDyadicPrimeComparison ℓ X -
      ((2*Real.pi:ℝ):ℂ)⁻¹*(primeComparisonLowHeight ℓ (X^(1/6+ρ:ℝ)) (X^δ) X +
        primeGaussHeightTail ℓ (X^(1/6+ρ:ℝ)) (X^δ) X))
      =o[atTop] firstMomentScale := by
  have hm := actual_prime_model_height_tail_isLittleO hMV hC
    (show 0 < (1/6:ℝ)+ρ by linarith) (show (1/6:ℝ)+ρ < 1 by linarith) hδ ℓ
  have he := prime_sharp_interval_error_isLittleO hρ hρ1.le
    (show 0 ≤ 1+cStar by linarith [cStar_pos])
    (fun X => primeCutoff (4*X)) (fun _ => primeComparisonCoefficient ℓ)
    (fun X _ p hp => mem_primeCutoff.mp hp)
    (fun X _ p hp => primeComparisonCoefficient_bound ℓ (mem_primeCutoff.mp hp).1)
  apply (he.sub (hm.const_mul_left (((2*Real.pi:ℝ):ℂ)⁻¹*(cStar:ℂ)))).congr'
    _ Filter.EventuallyEq.rfl
  filter_upwards [eventually_gt_atTop (0:ℝ)] with X hX
  rw [sharp_prime_comparison_low_tail ℓ (Real.rpow_pos_of_pos hX _)
    (Real.rpow_pos_of_pos hX _) hX]
  ring

end CubicFirstMoment

end

end OAI
