import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTExtraFactorization
import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTExtraBinCost

namespace OAI

/-! Finite Cauchy summation of the actual additional logarithmic bins.
The two per-bin estimates retain their separate small- and large-value
costs, and the full bin count is absorbed by the proved power saving. -/

namespace TwoPointCorrelations

open Finset MeasureTheory
open scoped Classical

lemma mrt_product_energy_split (Q R : ℝ → ℂ) (hQ : Continuous Q) (hR : Continuous R)
    {T θ A B : ℝ} (hT : 0 ≤ T) {E : Set ℝ} (hET : E ⊆ Set.Ioc (-T) T)
    (hsmall : (∫ t in E \ {t | θ ≤ ‖Q t‖}, ‖Q t*R t‖^2) ≤ A)
    (hlarge : (∫ t in E ∩ {t | θ ≤ ‖Q t‖}, ‖Q t*R t‖^2) ≤ B) :
    (∫ t in E, ‖Q t*R t‖^2) ≤ A+B := by
  have hset : MeasurableSet {t | θ ≤ ‖Q t‖} :=
    (isClosed_le continuous_const hQ.norm).measurableSet
  have hi := mrt_continuous_square_integrable (hQ.mul hR) hT hET
  have he := integral_inter_add_sdiff hset hi
  simp only [Pi.mul_apply] at he
  linarith

lemma mrt_bin_sum_energy {ι : Type*} (K : Finset ι) (G : ι → ℝ → ℂ)
    (hG : ∀ k ∈ K, Continuous (G k)) {T : ℝ} (hT : 0 ≤ T)
    {E : Set ℝ} (hET : E ⊆ Set.Ioc (-T) T) :
    (∫ t in E, ‖∑ k ∈ K, G k t‖^2) ≤
      (K.card:ℝ)*∑ k ∈ K, (∫ t in E, ‖G k t‖^2) := by
  have hh := mrt_restricted_product_sum_energy_local K (fun _ _ => (1:ℂ)) G hG
    (fun _ => (1:ℝ)) hT hET (by intros; simp)
  simpa only [one_mul,one_pow] using hh

lemma mrt_extra_small_bin_cost {L : ℝ} (hL : 1 ≤ L) (hlog : 1 ≤ Real.log L) :
    (((mrtLogBins (mrtExtraPrimeResolution L) (mrtExtraPrimeLower L)
      (mrtExtraPrimeUpper L)).card:ℝ)^2)*(L^(-100:ℝ))^2 ≤ 4*L^(-1/80:ℝ) := by
  have hL0 : 0 < L := by linarith
  have hH : mrtExtraPrimeResolution L ≤ L := by
    exact (Real.rpow_le_rpow_of_exponent_le hL (show (1/80:ℝ) ≤ 1 by norm_num)).trans_eq
      (Real.rpow_one L)
  have hc := mrt_extra_bin_card hL hlog
  have hratio : L/Real.log L ≤ L := div_le_self hL0.le hlog
  have hcard : ((mrtLogBins (mrtExtraPrimeResolution L) (mrtExtraPrimeLower L)
      (mrtExtraPrimeUpper L)).card:ℝ) ≤ 2*L^2 := by
    calc
      _ ≤ 2*mrtExtraPrimeResolution L*(L/Real.log L) := by simpa only [mul_div_assoc] using hc
      _ ≤ 2*L*L := mul_le_mul (by linarith) hratio (by positivity) (by positivity)
      _ = _ := by ring
  have hs := mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (Nat.cast_nonneg _) hcard 2) (sq_nonneg (L^(-100:ℝ)))
  have he : (2*L^2)^2*(L^(-100:ℝ))^2 = 4*L^(-196:ℝ) := by
    have hpow : (L^(-100:ℝ))^2 = L^(-200:ℝ) := by
      rw [← Real.rpow_natCast,← Real.rpow_mul hL0.le]
      norm_num
    rw [show (2*L^2)^2=4*L^4 by ring]
    rw [hpow]
    rw [show L^(4:ℕ)=L^(4:ℝ) from (Real.rpow_natCast L 4).symm]
    rw [mul_assoc,← Real.rpow_add hL0]
    norm_num
  rw [he] at hs
  exact hs.trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hL (show (-196:ℝ) ≤ -1/80 by norm_num))
    (by norm_num))

theorem mrt_extra_coarse_energy {ι : Type*} {L T C₀ C₁ : ℝ}
    (hL : 1 ≤ L) (hlog : 1 ≤ Real.log L) (hT : 0 ≤ T)
    (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁)
    (J : Finset ι) (P : ι → Finset ℕ) (F : ℕ → ℂ) (N : ℕ)
    {E : Set ℝ} (hET : E ⊆ Set.Ioc (-T) T)
    (hlow : ∀ k ∈ mrtLogBins (mrtExtraPrimeResolution L) (mrtExtraPrimeLower L)
      (mrtExtraPrimeUpper L), L^(79/80:ℝ) ≤ Real.log (mrtPrimeLogLower (mrtExtraPrimeResolution L) k))
    (hbin : ∀ k ∈ mrtLogBins (mrtExtraPrimeResolution L) (mrtExtraPrimeLower L)
      (mrtExtraPrimeUpper L),
      (∫ t in E, ‖mrtLogPrimePolynomial
        (mrtPrimeBand (mrtExtraPrimeLower L) (mrtExtraPrimeUpper L)) F
          (mrtExtraPrimeResolution L) k t *
        mrtCofactorPolynomial (mrtPrimeBand (mrtExtraPrimeLower L) (mrtExtraPrimeUpper L))
          (mrtTypicalCoefficient J P F) N (mrtPrimeLogLower (mrtExtraPrimeResolution L) k) t‖^2) ≤
        C₀*(L^(-100:ℝ))^2 + C₁*(L^(-1/40:ℝ))^2 /
          (mrtExtraPrimeResolution L*(Real.log (mrtPrimeLogLower (mrtExtraPrimeResolution L) k))^2)) :
    (∫ t in E, ‖mrtExtraCoarsePolynomial L J P F N t‖^2) ≤
      (4*C₀+4*C₁)*L^(-1/80:ℝ) := by
  let K := mrtLogBins (mrtExtraPrimeResolution L) (mrtExtraPrimeLower L) (mrtExtraPrimeUpper L)
  let A := mrtPrimeBand (mrtExtraPrimeLower L) (mrtExtraPrimeUpper L)
  let H := mrtExtraPrimeResolution L
  let G := fun k t => mrtLogPrimePolynomial A F H k t *
    mrtCofactorPolynomial A (mrtTypicalCoefficient J P F) N (mrtPrimeLogLower H k) t
  have hL0 : 0 < L := by linarith
  have hH0 : 0 < H := Real.rpow_pos_of_pos hL0 _
  have hg := mrt_bin_sum_energy K G (fun k _ =>
    (mrt_log_prime_polynomial_continuous _ _ _ _).mul
      (mrtCofactorPolynomial_continuous _ _ _ _)) hT hET
  change (∫ t in E, ‖mrtExtraCoarsePolynomial L J P F N t‖^2) ≤ _ at hg
  have hb : ∀ k ∈ K, (∫ t in E, ‖G k t‖^2) ≤
      C₀*(L^(-100:ℝ))^2 + C₁*(L^(-1/40:ℝ))^2/(H*(L^(79/80:ℝ))^2) := by
    intro k hk
    apply (hbin k hk).trans
    apply add_le_add le_rfl
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    apply mul_le_mul_of_nonneg_left _ hH0.le
    exact pow_le_pow_left₀ (Real.rpow_nonneg hL0.le _) (hlow k hk) 2
  have hsum := mul_le_mul_of_nonneg_left (sum_le_sum hb) (Nat.cast_nonneg K.card)
  have hs := mrt_extra_small_bin_cost hL hlog
  have hl := mrt_extra_bin_saved_cost hL hlog
  have hcs := mul_le_mul_of_nonneg_left hs hC₀
  have hcl := mul_le_mul_of_nonneg_left hl hC₁
  calc
    _ ≤ (K.card:ℝ)*∑ k ∈ K, (∫ t in E, ‖G k t‖^2) := hg
    _ ≤ (K.card:ℝ)*∑ _k ∈ K,
        (C₀*(L^(-100:ℝ))^2+C₁*(L^(-1/40:ℝ))^2/(H*(L^(79/80:ℝ))^2)) := hsum
    _ = C₀*((K.card:ℝ)^2*(L^(-100:ℝ))^2)+
        C₁*((L^(-1/40:ℝ))^2*((K.card:ℝ)^2/(H*(L^(79/80:ℝ))^2))) := by
      simp only [sum_const,nsmul_eq_mul]
      ring
    _ ≤ C₀*(4*L^(-1/80:ℝ))+C₁*(4*L^(-1/80:ℝ)) := add_le_add hcs hcl
    _ = _ := by ring

end TwoPointCorrelations

end OAI
