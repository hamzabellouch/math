import OAI.NumberTheory.DirichletL.Mellin.InverseContour

namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid

namespace CubicReflectionKernel
open scoped Classical FourierTransform SchwartzMap ContDiff Topology
open MeasureTheory Filter Set

theorem compact_family_mul_fourier_power_source_bound (F : ℝ → ℝ → ℂ)
    (hF : ContDiff ℝ ∞ (Function.uncurry F)) (K : Set ℝ) (hK : IsCompact K)
    (hsupp : ∀ σ, Function.support (F σ) ⊆ K) (J : Set ℝ) (hJ : IsCompact J)
    (j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ W : SchwartzMap ℝ ℂ, ∀ σ ∈ J, ∀ w : ℝ,
      |w| ^ j * ‖𝓕 (fun u => F σ u * W u) w‖ ≤
        C * (Finset.Iic (0, j)).sup (schwartzSeminormFamily ℝ ℝ ℂ) W := by
  obtain ⟨C, hC, hb⟩ := compact_family_mul_deriv_L1_source_bound F hF K hK hsupp J hJ j
  refine ⟨C / (2 * Real.pi) ^ j, by positivity, ?_⟩
  intro W σ hσ w
  have hFW : ContDiff ℝ ∞ (Function.uncurry (fun σ u => F σ u * W u)) :=
    hF.mul ((W.smooth ⊤).comp contDiff_snd)
  have hsupport : ∀ σ, Function.support (fun u => F σ u * W u) ⊆ K := by
    intro σ u hu
    exact hsupp σ (mul_ne_zero_iff.mp hu).1
  have hs : ContDiff ℝ ∞ (fun u => F σ u * W u) :=
    hFW.comp (contDiff_const.prodMk contDiff_id)
  have hfour := Real.fourier_iteratedDeriv (N := (⊤ : ℕ∞)) hs
    (fun k _ => compact_family_deriv_integrable (fun σ u => F σ u * W u) hFW K hK hsupport σ k)
    (by simp : (j : ℕ∞) ≤ ⊤)
  have hid : (2 * Real.pi) ^ j * (|w| ^ j * ‖𝓕 (fun u => F σ u * W u) w‖) =
      ‖𝓕 (iteratedDeriv j (fun u => F σ u * W u)) w‖ := by
    rw [hfour]
    simp only [norm_smul, norm_pow, norm_mul, Complex.norm_I, mul_one,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    norm_num
    ring
  have hn : ‖𝓕 (iteratedDeriv j (fun u => F σ u * W u)) w‖ ≤
      C * (Finset.Iic (0, j)).sup (schwartzSeminormFamily ℝ ℝ ℂ) W := by
    apply (VectorFourier.norm_fourierIntegral_le_integral_norm
      Real.fourierChar volume (innerₗ ℝ) (iteratedDeriv j (fun u => F σ u * W u)) w).trans
    exact hb W σ hσ
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ (by positivity : 0 < (2 * Real.pi) ^ j)).mpr
  rw [← hid] at hn
  calc
    _ = (2 * Real.pi) ^ j * (|w| ^ j * ‖𝓕 (fun u => F σ u * W u) w‖) := mul_comm _ _
    _ ≤ _ := hn

theorem compact_family_mul_fourier_weighted_source_bound (F : ℝ → ℝ → ℂ)
    (hF : ContDiff ℝ ∞ (Function.uncurry F)) (K : Set ℝ) (hK : IsCompact K)
    (hsupp : ∀ σ, Function.support (F σ) ⊆ K) (J : Set ℝ) (hJ : IsCompact J)
    (j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ W : SchwartzMap ℝ ℂ, ∀ σ ∈ J, ∀ w : ℝ,
      (1 + |w|) ^ j * ‖𝓕 (fun u => F σ u * W u) w‖ ≤
        C * (Finset.Iic (0, j)).sup (schwartzSeminormFamily ℝ ℝ ℂ) W := by
  obtain ⟨C₀, hC₀, h0⟩ := compact_family_mul_fourier_power_source_bound F hF K hK hsupp J hJ 0
  obtain ⟨Cj, hCj, hj⟩ := compact_family_mul_fourier_power_source_bound F hF K hK hsupp J hJ j
  refine ⟨2 ^ j * (C₀ + Cj), by positivity, ?_⟩
  intro W σ hσ w
  let S := (Finset.Iic (0, j)).sup (schwartzSeminormFamily ℝ ℝ ℂ) W
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hsubset : Finset.Iic (0, 0) ⊆ Finset.Iic (0, j) := by
    intro p hp
    exact Finset.mem_Iic.mpr ((Finset.mem_Iic.mp hp).trans (by simp))
  have hseminorm : (Finset.Iic (0, 0)).sup (schwartzSeminormFamily ℝ ℝ ℂ) W ≤ S :=
    Seminorm.le_def.mp (Finset.sup_mono hsubset) W
  have hbase : ‖𝓕 (fun u => F σ u * W u) w‖ ≤ C₀ * S := by
    have hh : ‖𝓕 (fun u => F σ u * W u) w‖ ≤ C₀ * (Finset.Iic (0, 0)).sup (schwartzSeminormFamily ℝ ℝ ℂ) W := by
      simpa using h0 W σ hσ w
    exact hh.trans (mul_le_mul_of_nonneg_left hseminorm hC₀.le)
  have hpower : |w| ^ j * ‖𝓕 (fun u => F σ u * W u) w‖ ≤ Cj * S := hj W σ hσ w
  by_cases hw : |w| ≤ 1
  · calc
      _ ≤ 2 ^ j * ‖𝓕 (fun u => F σ u * W u) w‖ :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) (by linarith) j) (norm_nonneg _)
      _ ≤ 2 ^ j * (C₀ * S) := mul_le_mul_of_nonneg_left hbase (by positivity)
      _ ≤ 2 ^ j * ((C₀ + Cj) * S) := by gcongr; linarith
      _ = _ := by dsimp [S]; ring
  · have hw' : 1 ≤ |w| := le_of_lt (lt_of_not_ge hw)
    calc
      _ ≤ (2 * |w|) ^ j * ‖𝓕 (fun u => F σ u * W u) w‖ :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) (by linarith) j) (norm_nonneg _)
      _ = 2 ^ j * (|w| ^ j * ‖𝓕 (fun u => F σ u * W u) w‖) := by rw [mul_pow, mul_assoc]
      _ ≤ 2 ^ j * (Cj * S) := mul_le_mul_of_nonneg_left hpower (by positivity)
      _ ≤ 2 ^ j * ((C₀ + Cj) * S) := by gcongr; linarith
      _ = _ := by dsimp [S]; ring

def negativeLogPullbackCLM (a b : ℝ) : SchwartzMap ℝ ℂ →L[ℝ] SchwartzMap ℝ ℂ :=
  (SchwartzMap.compCLMOfContinuousLinearEquiv ℝ
    (LinearIsometryEquiv.neg ℝ).toContinuousLinearEquiv).comp (logPullbackCLM a b)

theorem negativeLogPullbackCLM_eq_actual (a b : ℝ) (ha : 0 < a) (W : SchwartzMap ℝ ℂ)
    (hsupp : Function.support (W : ℝ → ℂ) ⊆ Set.Icc a b) (u : ℝ) :
    negativeLogPullbackCLM a b W u = W (Real.exp (-u)) := by
  change logPullbackCLM a b W (-u) = _
  exact logPullbackCLM_eq_actual a b ha W hsupp (-u)

def logWeight (a b σ u : ℝ) : ℂ := (Real.exp (-σ * u) * logCutoff a b (-u) : ℝ)

theorem logWeight_smooth (a b : ℝ) : ContDiff ℝ ∞ (Function.uncurry (logWeight a b)) := by
  change ContDiff ℝ ∞ (fun p : ℝ × ℝ => ((Real.exp (-p.1 * p.2) * logCutoff a b (-p.2) : ℝ) : ℂ))
  exact Complex.ofRealCLM.contDiff.comp
    ((Real.contDiff_exp.comp (contDiff_fst.neg.mul contDiff_snd)).mul
      ((logCutoff a b).contDiff.comp contDiff_snd.neg))

theorem logWeight_support (a b σ : ℝ) :
    Function.support (logWeight a b σ) ⊆ Metric.closedBall 0 (logRadius a b + 1) := by
  intro u hu
  have hc : logCutoff a b (-u) ≠ 0 := by
    intro hc
    exact hu (by simp [logWeight, hc])
  have hm : -u ∈ Function.support (logCutoff a b) := hc
  rw [(logCutoff a b).support_eq] at hm
  change dist (-u) 0 < logRadius a b + 1 at hm
  change dist u 0 ≤ logRadius a b + 1
  simpa only [dist_zero_right, norm_neg] using hm.le

theorem logWeight_mul_pullback (a b : ℝ) (ha : 0 < a) (W : SchwartzMap ℝ ℂ)
    (hsupp : Function.support (W : ℝ → ℂ) ⊆ Set.Icc a b) (σ u : ℝ) :
    logWeight a b σ u * negativeLogPullbackCLM a b W u = mellinLogFamily W σ u := by
  rw [negativeLogPullbackCLM_eq_actual a b ha W hsupp]
  by_cases hW : W (Real.exp (-u)) = 0
  · simp [logWeight, mellinLogFamily, hW]
  · have hc := logCutoff_eq_one_of_source a b ha (-u) (hsupp hW)
    simp [logWeight, mellinLogFamily, hc]

theorem mellin_strip_source_bound (a b : ℝ) (ha : 0 < a) (lo hi : ℝ) (j : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ W : SchwartzMap ℝ ℂ, Function.support (W : ℝ → ℂ) ⊆ Set.Icc a b →
      ∀ σ ∈ Set.Icc lo hi, ∀ t : ℝ,
        (1 + |t|) ^ j * ‖mellin W ((σ : ℂ) + t * Complex.I)‖ ≤
          C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W := by
  obtain ⟨C, hC, hb⟩ := compact_family_mul_fourier_weighted_source_bound
    (logWeight a b) (logWeight_smooth a b) (Metric.closedBall 0 (logRadius a b + 1))
    (isCompact_closedBall _ _) (logWeight_support a b) (Set.Icc lo hi) isCompact_Icc j
  obtain ⟨s, D, hD, hDbd⟩ := EisensteinSchwartzPoisson.schwartzCLM_finite_seminorm_control
    (negativeLogPullbackCLM a b) (Finset.Iic (0, j))
  refine ⟨s, (1 + 2 * Real.pi) ^ j * C * D, by positivity, ?_⟩
  intro W hsupp σ hσ t
  have hfun : (fun u => logWeight a b σ u * negativeLogPullbackCLM a b W u) = mellinLogFamily W σ :=
    funext (logWeight_mul_pullback a b ha W hsupp σ)
  have hfour := hb (negativeLogPullbackCLM a b W) σ hσ (t / (2 * Real.pi))
  rw [hfun] at hfour
  have ht : |t| = (2 * Real.pi) * |t / (2 * Real.pi)| := by
    rw [abs_div, abs_of_pos (by positivity : 0 < 2 * Real.pi)]
    field_simp
  have hbase : 1 + |t| ≤ (1 + 2 * Real.pi) * (1 + |t / (2 * Real.pi)|) := by
    rw [ht]
    nlinarith [Real.pi_pos, abs_nonneg (t / (2 * Real.pi))]
  rw [mellin_eq_logFamily_fourier]
  calc
    _ ≤ ((1 + 2 * Real.pi) * (1 + |t / (2 * Real.pi)|)) ^ j *
        ‖𝓕 (mellinLogFamily W σ) (t / (2 * Real.pi))‖ :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hbase j) (norm_nonneg _)
    _ = (1 + 2 * Real.pi) ^ j * ((1 + |t / (2 * Real.pi)|) ^ j *
        ‖𝓕 (mellinLogFamily W σ) (t / (2 * Real.pi))‖) := by rw [mul_pow, mul_assoc]
    _ ≤ (1 + 2 * Real.pi) ^ j * (C *
        (D * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)) :=
      mul_le_mul_of_nonneg_left (hfour.trans (mul_le_mul_of_nonneg_left (hDbd W) hC.le)) (by positivity)
    _ = _ := by ring

theorem mellinData_strip_source_bound (a b : ℝ) (ha : 0 < a) (A j : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ W : SchwartzMap ℝ ℂ, Function.support (W : ℝ → ℂ) ⊆ Set.Icc a b →
      ∀ σ ∈ Set.Icc (-(1 / 4 : ℝ)) (A : ℝ), ∀ t : ℝ,
        (1 + |t|) ^ j * ‖mellinData W ((σ : ℂ) + t * Complex.I)‖ ≤
          C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W := by
  let g : ℕ := 4 * A + 4
  obtain ⟨Cγ, hCγ, hγ⟩ := gammaMultiplier_strip_bound A
  obtain ⟨s, CV, hCV, hVb⟩ := mellin_strip_source_bound a b ha (-(A : ℝ)) (1 / 4) (g + j)
  refine ⟨s, Cγ * CV, mul_pos hCγ hCV, ?_⟩
  intro W hsupp σ hσ t
  have hσ' : -σ ∈ Set.Icc (-(A : ℝ)) (1 / 4) := by constructor <;> linarith [hσ.1, hσ.2]
  have hmb := hVb W hsupp (-σ) hσ' (-t)
  have heq : (-σ : ℝ) + (-t : ℝ) * Complex.I = -((σ : ℂ) + t * Complex.I) := by
    push_cast
    ring
  rw [heq, abs_neg] at hmb
  have hgb : ‖gammaMultiplier ((σ : ℂ) + t * Complex.I)‖ ≤ Cγ * (1 + |t|) ^ g := hγ σ hσ t
  rw [mellinData, norm_mul]
  calc
    _ = ((1 + |t|) ^ j * ‖mellin W (-((σ : ℂ) + t * Complex.I))‖) *
        ‖gammaMultiplier ((σ : ℂ) + t * Complex.I)‖ := by ring
    _ ≤ ((1 + |t|) ^ j * ‖mellin W (-((σ : ℂ) + t * Complex.I))‖) *
        (Cγ * (1 + |t|) ^ g) := mul_le_mul_of_nonneg_left hgb (by positivity)
    _ = Cγ * ((1 + |t|) ^ (g + j) * ‖mellin W (-((σ : ℂ) + t * Complex.I))‖) := by
      rw [pow_add]
      ring
    _ ≤ Cγ * (CV * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) := mul_le_mul_of_nonneg_left hmb hCγ.le
    _ = _ := by ring

theorem mellinEulerData_strip_source_bound (a b : ℝ) (ha : 0 < a) (A j : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ W : SchwartzMap ℝ ℂ, Function.support (W : ℝ → ℂ) ⊆ Set.Icc a b →
      ∀ σ ∈ Set.Icc (-(1 / 4 : ℝ)) (A : ℝ), ∀ t : ℝ,
        ‖mellinEulerData W j ((σ : ℂ) + t * Complex.I)‖ ≤
          C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W / (1 + t ^ 2) := by
  obtain ⟨s, C, hC, hb⟩ := mellinData_strip_source_bound a b ha A (j + 2)
  refine ⟨s, ((A : ℝ) + 2) ^ j * C, by positivity, ?_⟩
  intro W hsupp σ hσ t
  apply weighted_two_to_cauchy (norm_nonneg _) t
  have hσabs : |σ| ≤ (A : ℝ) + 1 := by
    apply abs_le.mpr
    constructor <;> linarith [hσ.1, hσ.2, (Nat.cast_nonneg A : (0 : ℝ) ≤ A)]
  have hz : ‖(σ : ℂ) + t * Complex.I‖ ≤ ((A : ℝ) + 2) * (1 + |t|) := by
    have hnorm := norm_add_le (σ : ℂ) ((t : ℂ) * Complex.I)
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I, mul_one] at hnorm
    nlinarith [abs_nonneg t, (Nat.cast_nonneg A : (0 : ℝ) ≤ A)]
  rw [mellinEulerData, norm_mul, norm_pow, norm_neg]
  calc
    _ ≤ (1 + |t|) ^ 2 * ((((A : ℝ) + 2) * (1 + |t|)) ^ j *
        ‖mellinData W ((σ : ℂ) + t * Complex.I)‖) := by gcongr
    _ = ((A : ℝ) + 2) ^ j * ((1 + |t|) ^ (j + 2) *
        ‖mellinData W ((σ : ℂ) + t * Complex.I)‖) := by rw [mul_pow, pow_add]; ring
    _ ≤ ((A : ℝ) + 2) ^ j * (C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) :=
      mul_le_mul_of_nonneg_left (hb W hsupp σ hσ t) (by positivity)
    _ = _ := by ring

theorem mellinInv_euler_line_source_bound (a b : ℝ) (ha : 0 < a) (A j : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ W : SchwartzMap ℝ ℂ, Function.support (W : ℝ → ℂ) ⊆ Set.Icc a b →
      ∀ σ ∈ Set.Icc (-(1 / 4 : ℝ)) (A : ℝ), ∀ y : ℝ, 0 < y →
        ‖mellinInv σ (mellinEulerData W j) y‖ ≤
          C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W * y ^ (-σ) := by
  obtain ⟨s, C, hC, hb⟩ := mellinEulerData_strip_source_bound a b ha A j
  refine ⟨s, C / 2, by positivity, ?_⟩
  intro W hsupp σ hσ y hy
  let Q := s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W
  have hint : ‖∫ t : ℝ, (y : ℂ) ^ (-((σ : ℂ) + t * Complex.I)) *
        mellinEulerData W j ((σ : ℂ) + t * Complex.I)‖ ≤
      (y ^ (-σ) * (C * Q)) * Real.pi := by
    calc
      _ ≤ ∫ t : ℝ, (y ^ (-σ) * (C * Q)) * (1 + t ^ 2)⁻¹ := by
        apply norm_integral_le_of_norm_le (integrable_inv_one_add_sq.const_mul _)
        filter_upwards [] with t
        rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hy]
        simp only [Complex.neg_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
          Complex.ofReal_im, Complex.I_re, mul_zero, zero_mul, sub_zero, add_zero]
        simpa only [div_eq_mul_inv, mul_assoc] using
          mul_le_mul_of_nonneg_left (hb W hsupp σ hσ t) (Real.rpow_nonneg hy.le (-σ))
      _ = _ := by rw [integral_const_mul, integral_univ_inv_one_add_sq]
  rw [mellinInv, norm_smul, Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / (2 * Real.pi))]
  simp only [smul_eq_mul]
  calc
    _ ≤ (1 / (2 * Real.pi)) * ((y ^ (-σ) * (C * Q)) * Real.pi) :=
      mul_le_mul_of_nonneg_left hint (by positivity)
    _ = _ := by dsimp [Q]; field_simp

theorem paperKernel_euler_source_power_decay (a b : ℝ) (ha : 0 < a) (A j : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ W : SchwartzMap ℝ ℂ, Function.support (W : ℝ → ℂ) ⊆ Set.Icc a b →
      ∀ x : ℝ, 0 < x →
        (‖LocalLogFourier.eulerDeriv (paperKernel W) j x‖ ≤
          C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W * x ^ (1 / 4 : ℝ)) ∧
        (‖LocalLogFourier.eulerDeriv (paperKernel W) j x‖ ≤
          C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W * x ^ (-(A : ℝ))) := by
  obtain ⟨s, C, hC, hb⟩ := mellinInv_euler_line_source_bound a b ha A j
  let B := max (paperScale ^ (1 / 4 : ℝ)) (paperScale ^ (-(A : ℝ)))
  have hB : 0 < B := lt_of_lt_of_le (Real.rpow_pos_of_pos paperScale_pos _) (le_max_left _ _)
  refine ⟨s, C * B, mul_pos hC hB, ?_⟩
  intro W hsupp x hx
  let Q := s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hline (σ : ℝ) (hσ : σ ∈ Set.Icc (-(1 / 4 : ℝ)) (A : ℝ)) :
      ‖LocalLogFourier.eulerDeriv (paperKernel W) j x‖ ≤
        C * Q * (paperScale * x) ^ (-σ) := by
    rw [← paperEulerKernel_eq_euler W (logPullbackCLM a b W)
      (logPullbackCLM_eq_actual a b ha W hsupp) j x hx]
    unfold paperEulerKernel
    rw [mellinInv_euler_shift W a b ha hsupp (W.smooth ⊤) A j σ hσ _ (mul_pos paperScale_pos hx)]
    exact hb W hsupp σ hσ (paperScale * x) (mul_pos paperScale_pos hx)
  have hleft : -(1 / 4 : ℝ) ∈ Set.Icc (-(1 / 4 : ℝ)) (A : ℝ) := by
    constructor
    · rfl
    · linarith [show (0 : ℝ) ≤ A from Nat.cast_nonneg A]
  have hright : (A : ℝ) ∈ Set.Icc (-(1 / 4 : ℝ)) (A : ℝ) := by
    constructor
    · linarith [show (0 : ℝ) ≤ A from Nat.cast_nonneg A]
    · rfl
  constructor
  · have hh := hline _ hleft
    rw [neg_neg, Real.mul_rpow paperScale_pos.le hx.le] at hh
    calc
      _ ≤ C * Q * (paperScale ^ (1 / 4 : ℝ) * x ^ (1 / 4 : ℝ)) := hh
      _ = (C * paperScale ^ (1 / 4 : ℝ)) * Q * x ^ (1 / 4 : ℝ) := by ring
      _ ≤ (C * B) * Q * x ^ (1 / 4 : ℝ) := by
        gcongr
        exact le_max_left _ _
  · have hh := hline _ hright
    rw [Real.mul_rpow paperScale_pos.le hx.le] at hh
    calc
      _ ≤ C * Q * (paperScale ^ (-(A : ℝ)) * x ^ (-(A : ℝ))) := hh
      _ = (C * paperScale ^ (-(A : ℝ))) * Q * x ^ (-(A : ℝ)) := by ring
      _ ≤ (C * B) * Q * x ^ (-(A : ℝ)) := by
        gcongr
        exact le_max_right _ _

theorem paperKernel_euler_source_uniform_weighted_bound
    (a b : ℝ) (ha : 0 < a) (A K : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ W : SchwartzMap ℝ ℂ, Function.support (W : ℝ → ℂ) ⊆ Set.Icc a b →
      ∀ i ≤ K, ∀ x : ℝ, 0 < x →
        (1 + x) ^ A * ‖LocalLogFourier.eulerDeriv (paperKernel W) i x‖ ≤
          C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W := by
  choose s c hc hb using fun i : Fin (K + 1) => paperKernel_euler_source_power_decay a b ha A i.val
  let S : Finset (ℕ × ℕ) := Finset.univ.biUnion s
  let D : ℝ := (∑ i : Fin (K + 1), c i) + 1
  have hD : 0 < D := by
    have hs : (0 : ℝ) ≤ ∑ i : Fin (K + 1), c i := Finset.sum_nonneg (fun i _ => (hc i).le)
    dsimp [D]
    linarith
  have hci (i : Fin (K + 1)) : c i ≤ D := by
    have hs : c i ≤ ∑ k : Fin (K + 1), c k :=
      Finset.single_le_sum (fun k _ => (hc k).le) (Finset.mem_univ i)
    dsimp [D]
    linarith
  refine ⟨S, 2 ^ A * (D + D), by positivity, ?_⟩
  intro W hsupp
  let Q := S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hsource (i : Fin (K + 1)) : c i * (s i).sup (schwartzSeminormFamily ℝ ℝ ℂ) W ≤ D * Q := by
    have hsub : s i ⊆ S := Finset.subset_biUnion_of_mem s (Finset.mem_univ i)
    have hq : (s i).sup (schwartzSeminormFamily ℝ ℝ ℂ) W ≤ Q :=
      Seminorm.le_def.mp (Finset.sup_mono hsub) W
    exact mul_le_mul (hci i) hq (by positivity) hD.le
  have hsmall : ∀ i ≤ K, ∀ x : ℝ, 0 < x → x ≤ 1 →
      ‖LocalLogFourier.eulerDeriv (paperKernel W) i x‖ ≤ D * Q := by
    intro i hi x hx hx1
    let k : Fin (K + 1) := ⟨i, by omega⟩
    have hp : x ^ (1 / 4 : ℝ) ≤ 1 := Real.rpow_le_one hx.le hx1 (by norm_num)
    calc
      _ ≤ (c k * (s k).sup (schwartzSeminormFamily ℝ ℝ ℂ) W) * x ^ (1 / 4 : ℝ) := (hb k W hsupp x hx).1
      _ ≤ c k * (s k).sup (schwartzSeminormFamily ℝ ℝ ℂ) W := by
        simpa using mul_le_mul_of_nonneg_left hp (mul_nonneg (hc k).le (by positivity))
      _ ≤ D * Q := hsource k
  have hlarge : ∀ i ≤ K, ∀ x : ℝ, 1 ≤ x →
      x ^ A * ‖LocalLogFourier.eulerDeriv (paperKernel W) i x‖ ≤ D * Q := by
    intro i hi x hx1
    have hx : 0 < x := lt_of_lt_of_le zero_lt_one hx1
    let k : Fin (K + 1) := ⟨i, by omega⟩
    have hxpow : x ^ A ≠ 0 := pow_ne_zero A hx.ne'
    calc
      _ ≤ x ^ A * ((c k * (s k).sup (schwartzSeminormFamily ℝ ℝ ℂ) W) * x ^ (-(A : ℝ))) :=
        mul_le_mul_of_nonneg_left (hb k W hsupp x hx).2 (pow_nonneg hx.le A)
      _ = c k * (s k).sup (schwartzSeminormFamily ℝ ℝ ℂ) W := by
        rw [Real.rpow_neg hx.le, Real.rpow_natCast]
        field_simp
      _ ≤ D * Q := hsource k
  intro i hi x hx
  have hh := LocalLogFourier.euler_two_regime_bound (paperKernel W) A K (D * Q) (D * Q)
    (mul_nonneg hD.le hQ) (mul_nonneg hD.le hQ) hsmall hlarge i hi x hx
  convert hh using 1 ; dsimp [Q] ; ring

end CubicReflectionKernel

open scoped BigOperators Classical
namespace FirstPassCubeLabels
open ActualEisensteinCubic
open MixedCrossSeparation (crossSymbol quadraticCrossPhase columnPrimeCoprime)
open FiniteGaussPhase (canonicalProductGauss canonicalProductGauss_cross_factors)
open MixedGaussConversion (localGauss)

def gaussBlock {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (S : Finset ι) (e : ι → ℕ) : ℂ :=
  ∏ i ∈ S, (∏ k ∈ S.erase i, crossSymbol p hg i k ^ e i) *
    localGauss (p i) (hp i) (hg i) (e i)

theorem canonicalProductGauss_eq_gaussBlock {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (S : Finset ι) (e : ι → ℕ)
    (he : ∀ i ∈ S, e i ≠ 0) :
    canonicalProductGauss (fun i : S => p i.val) (fun i => hp i.val)
      (columnPrimeCoprime p hcop S) (fun i => hg i.val) (fun i => e i.val) =
      gaussBlock p hp hg S e := by
  let : DecidableEq S := fun a b => Classical.propDecidable (a = b)
  rw [canonicalProductGauss_cross_factors, ← Finset.prod_mul_distrib]
  have hin (i : S) :
      (∏ k ∈ (Finset.univ : Finset S).erase i,
        (canonicalSextic (Ideal.span {p i.val}) (hg i.val) ^ e i.val)
          (Ideal.Quotient.mk (Ideal.span {p i.val}) (p k.val))) =
      ∏ k ∈ S.erase i.val, crossSymbol p hg i.val k ^ e i.val := by
    apply Finset.prod_bij (fun k _ => k.val)
    · intro k hk
      exact Finset.mem_erase.mpr ⟨fun h => (Finset.mem_erase.mp hk).1 (Subtype.ext h), k.property⟩
    · intro a ha b hb hab
      exact Subtype.ext hab
    · intro k hk
      refine ⟨⟨k, (Finset.mem_erase.mp hk).2⟩, ?_, rfl⟩
      exact Finset.mem_erase.mpr ⟨fun h => (Finset.mem_erase.mp hk).1 (congrArg Subtype.val h),
        Finset.mem_univ _⟩
    · intro k hk
      exact MulChar.pow_apply' _ (he i.val i.property) _
  calc
    _ = ∏ i : S, (∏ k ∈ S.erase i.val, crossSymbol p hg i.val k ^ e i.val) *
        localGauss (p i.val) (hp i.val) (hg i.val) (e i.val) := by
      apply Finset.prod_congr rfl
      intro i hi
      rw [hin i]
      rfl
    _ = _ := Finset.prod_coe_sort S (fun i =>
      (∏ k ∈ S.erase i, crossSymbol p hg i k ^ e i) * localGauss (p i) (hp i) (hg i) (e i))

def blockCross {ι : Type*}
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (S T : Finset ι) (e : ι → ℕ) : ℂ :=
  ∏ i ∈ S, ∏ k ∈ T,
    crossSymbol p hg i k ^ e i * crossSymbol p hg k i ^ e k

theorem gaussBlock_union {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (S T : Finset ι) (hd : Disjoint S T)
    (e : ι → ℕ) :
    gaussBlock p hp hg (S ∪ T) e =
      gaussBlock p hp hg S e * gaussBlock p hp hg T e * blockCross p hg S T e := by
  have hS (i : ι) (hi : i ∈ S) :
      (∏ k ∈ (S ∪ T).erase i, crossSymbol p hg i k ^ e i) =
      (∏ k ∈ S.erase i, crossSymbol p hg i k ^ e i) *
        ∏ k ∈ T, crossSymbol p hg i k ^ e i := by
    have hn : i ∉ T := fun h => Finset.disjoint_left.mp hd hi h
    rw [Finset.erase_union_distrib, Finset.erase_eq_of_notMem hn,
      Finset.prod_union (hd.mono_left (Finset.erase_subset _ _))]
  have hT (i : ι) (hi : i ∈ T) :
      (∏ k ∈ (S ∪ T).erase i, crossSymbol p hg i k ^ e i) =
      (∏ k ∈ T.erase i, crossSymbol p hg i k ^ e i) *
        ∏ k ∈ S, crossSymbol p hg i k ^ e i := by
    have hn : i ∉ S := fun h => Finset.disjoint_left.mp hd h hi
    rw [Finset.union_comm S T, Finset.erase_union_distrib, Finset.erase_eq_of_notMem hn,
      Finset.prod_union (hd.symm.mono_left (Finset.erase_subset _ _))]
  have hpS : (∏ i ∈ S, (∏ k ∈ (S ∪ T).erase i, crossSymbol p hg i k ^ e i) *
      localGauss (p i) (hp i) (hg i) (e i)) =
      gaussBlock p hp hg S e * (∏ i ∈ S, ∏ k ∈ T, crossSymbol p hg i k ^ e i) := by
    rw [gaussBlock, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i hi
    rw [hS i hi]
    ring
  have hpT : (∏ i ∈ T, (∏ k ∈ (S ∪ T).erase i, crossSymbol p hg i k ^ e i) *
      localGauss (p i) (hp i) (hg i) (e i)) =
      gaussBlock p hp hg T e * (∏ i ∈ T, ∏ k ∈ S, crossSymbol p hg i k ^ e i) := by
    rw [gaussBlock, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i hi
    rw [hT i hi]
    ring
  rw [gaussBlock, Finset.prod_union hd, hpS, hpT,
    Finset.prod_comm (s := T) (t := S)]
  simp only [blockCross, Finset.prod_mul_distrib]
  ring

theorem gaussBlock_congr {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (S : Finset ι) (e f : ι → ℕ)
    (he : ∀ i ∈ S, e i = f i) : gaussBlock p hp hg S e = gaussBlock p hp hg S f := by
  apply Finset.prod_congr rfl
  intro i hi
  rw [he i hi]

def cubeActiveSupport {ι : Type*} (B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) : Finset ι :=
  B.filter (fun k => conductorExponent (parity (v k)) (ε₁ k) (ε₂ k) ≠ 0)

def blockCubeExponent {ι : Type*} [DecidableEq ι] (U : Finset ι)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (side : Bool) (i : ι) : ℕ :=
  if i ∈ U then (if side then 5 else 1)
  else (conductorExponent (parity (v i)) (ε₁ i) (ε₂ i)).val

theorem gaussBlock_cube_partition {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (U B : Finset ι) (hd : Disjoint U B)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (side : Bool) :
    gaussBlock p hp hg (U ∪ cubeActiveSupport B v ε₁ ε₂)
      (blockCubeExponent U v ε₁ ε₂ side) =
    gaussBlock p hp hg U (fun _ => if side then 5 else 1) *
      gaussBlock p hp hg (cubeActiveSupport B v ε₁ ε₂)
        (fun k => (conductorExponent (parity (v k)) (ε₁ k) (ε₂ k)).val) *
      mixedCubeCross p hg U B v ε₁ ε₂ side := by
  have hdc : Disjoint U (cubeActiveSupport B v ε₁ ε₂) := hd.mono_right (Finset.filter_subset _ _)
  have hU : ∀ i ∈ U, blockCubeExponent U v ε₁ ε₂ side i = (if side then 5 else 1) := by
    intro i hi
    simp only [blockCubeExponent, ite_eq_left hi]
  have hB : ∀ i ∈ cubeActiveSupport B v ε₁ ε₂, blockCubeExponent U v ε₁ ε₂ side i =
      (conductorExponent (parity (v i)) (ε₁ i) (ε₂ i)).val := by
    intro i hi
    exact ite_eq_right (fun hu => Finset.disjoint_left.mp hdc hu hi)
  rw [gaussBlock_union p hp hg U _ hdc,
    gaussBlock_congr p hp hg U _ _ hU, gaussBlock_congr p hp hg _ _ _ hB]
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  apply Finset.prod_congr rfl
  intro k hk
  rw [hU i hi, hB k hk]

theorem canonicalProductGauss_cube_partition {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1) (U B : Finset ι) (hd : Disjoint U B)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (side : Bool) :
    canonicalProductGauss (fun i : ↥(U ∪ cubeActiveSupport B v ε₁ ε₂) => p i.val)
      (fun i => hp i.val) (columnPrimeCoprime p hcop _) (fun i => hg i.val)
      (fun i => blockCubeExponent U v ε₁ ε₂ side i.val) =
    gaussBlock p hp hg U (fun _ => if side then 5 else 1) *
      gaussBlock p hp hg (cubeActiveSupport B v ε₁ ε₂)
        (fun k => (conductorExponent (parity (v k)) (ε₁ k) (ε₂ k)).val) *
      ((if side then star (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg U
          (crtLabel p B v ε₁ ε₂ side))
        else finiteSquarefreeRow (fun i => Ideal.span {p i}) hg U
          (crtLabel p B v ε₁ ε₂ side)) *
        quadraticCrossPhase p hg U (cubeOddSupport B v ε₁ ε₂)) := by
  have he : ∀ i ∈ U ∪ cubeActiveSupport B v ε₁ ε₂, blockCubeExponent U v ε₁ ε₂ side i ≠ 0 := by
    intro i hi
    by_cases hiU : i ∈ U
    · cases side <;> simp [blockCubeExponent, hiU]
    · have hiB := (Finset.mem_union.mp hi).resolve_left hiU
      simp only [blockCubeExponent, ite_eq_right hiU]
      exact (ZMod.val_eq_zero _).not.mpr (Finset.mem_filter.mp hiB).2
  rw [canonicalProductGauss_eq_gaussBlock p hp hcop hg _ _ he,
    gaussBlock_cube_partition p hp hg U B hd,
    mixedCubeCross_eq_row_quadratic p hcop hg hpr U B hd]

theorem columnCoefficient_eq_gaussBlock {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (S : Finset ι) :
    MixedCrossSeparation.columnCoefficient p hp hcop hg S =
      star (FiniteGaussPhase.angularFactor (∏ i ∈ S, p i)) *
        gaussBlock p hp hg S (fun _ => 2) := by
  unfold MixedCrossSeparation.columnCoefficient FiniteGaussPhase.canonicalProductCoefficient
  rw [Finset.prod_coe_sort]
  rw [canonicalProductGauss_eq_gaussBlock p hp hcop hg S (fun _ => 2) (fun _ _ => by decide)]

theorem blockCross_two_eq_row_four {ι : Type*}
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1) (S T : Finset ι) :
    blockCross p hg S T (fun _ => 2) =
      finiteSquarefreeRow (fun i => Ideal.span {p i}) hg S (∏ k ∈ T, p k) ^ 4 := by
  simp only [blockCross, finiteSquarefreeRow, map_prod, ← Finset.prod_pow]
  apply Finset.prod_congr rfl
  intro i hi
  apply Finset.prod_congr rfl
  intro k hk
  have hr : crossSymbol p hg i k ^ 2 = crossSymbol p hg k i ^ 2 :=
    canonicalSextic_sq_reciprocity_primary (Ideal.span {p i}) (Ideal.span {p k})
      (hg i) (hg k) (p i) (p k) rfl rfl (hpr i) (hpr k)
  change crossSymbol p hg i k ^ 2 * crossSymbol p hg k i ^ 2 = crossSymbol p hg i k ^ 4
  rw [← hr]
  ring

theorem columnCoefficient_union_row_four {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1) (S T : Finset ι) (hd : Disjoint S T) :
    MixedCrossSeparation.columnCoefficient p hp hcop hg (S ∪ T) =
      MixedCrossSeparation.columnCoefficient p hp hcop hg S *
        MixedCrossSeparation.columnCoefficient p hp hcop hg T *
        finiteSquarefreeRow (fun i => Ideal.span {p i}) hg S (∏ k ∈ T, p k) ^ 4 := by
  have ha : FiniteGaussPhase.angularFactor (∏ i ∈ S ∪ T, p i) =
      FiniteGaussPhase.angularFactor (∏ i ∈ S, p i) *
        FiniteGaussPhase.angularFactor (∏ i ∈ T, p i) := by
    rw [Finset.prod_union hd]
    simp only [FiniteGaussPhase.angularFactor, map_mul, norm_mul, Complex.ofReal_mul,
      div_eq_mul_inv, mul_inv_rev]
    ring
  rw [columnCoefficient_eq_gaussBlock, columnCoefficient_eq_gaussBlock,
    columnCoefficient_eq_gaussBlock, ha, star_mul, gaussBlock_union p hp hg S T hd,
    blockCross_two_eq_row_four p hg hpr S T]
  ring

theorem gaussBlock_norm_one {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (S : Finset ι) (e : ι → ℕ) (he : ∀ i ∈ S, e i ≠ 0) (he6 : ∀ i ∈ S, e i < 6) :
    ‖gaussBlock p hp hg S e‖ = 1 := by
  rw [← canonicalProductGauss_eq_gaussBlock p hp hcop hg S e he]
  exact FiniteGaussPhase.norm_canonicalProductGauss
    (fun i : S => p i.val) (fun i => hp i.val) (columnPrimeCoprime p hcop S)
    (fun i => hg i.val) (fun i => hc i.val) (fun i => e i.val)
    (fun i => he i.val i.property) (fun i => he6 i.val i.property)

end FirstPassCubeLabels

end

end OAI
