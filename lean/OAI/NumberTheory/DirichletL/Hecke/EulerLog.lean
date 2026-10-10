import OAI.NumberTheory.DirichletL.Hecke.Boundary
import OAI.NumberTheory.DirichletL.LogarithmicControl
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

namespace OAI

noncomputable section
open scoped Classical Topology BigOperators
open Set Metric Filter Complex ActualEisensteinCubic
open SevenEighths.IdealEuler SevenEighths.IdealCharacter
open SmoothMobiusCorrection (PrimeIdeal)

namespace SevenEighths.HeckeEulerLog

def eulerLog (a : Ideal O →*₀ ℂ) (s : ℂ) : ℂ :=
  ∑' P : PrimeIdeal, -Complex.log (1 - weighted a s P.val)

def majorant (σ : ℝ) (P : PrimeIdeal) : ℝ :=
  (3 / 2) * (Ideal.absNorm P.val : ℝ) ^ (-σ)

theorem majorant_summable {σ : ℝ} (hσ : 1 < σ) : Summable (majorant σ) := by
  have h := (SmoothMobiusCorrection.prime_norm_series_summable (σ - 1)
    (by linarith)).mul_left (3 / 2)
  convert h using 1
  ext P
  unfold majorant
  congr 2
  ring

theorem weighted_norm_le (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1)
    (P : PrimeIdeal) {s : ℂ} {σ : ℝ} (hs : σ ≤ s.re) :
    ‖weighted a s P.val‖ ≤ (Ideal.absNorm P.val : ℝ) ^ (-σ) := by
  change ‖a P.val * CubicEisenstein.fullIdealWeight s P.val‖ ≤ _
  simp only [CubicEisenstein.fullIdealWeight, P.property.ne_zero, ite_false, norm_mul]
  change ‖a P.val‖ * ‖SmoothMobiusCorrection.primeNormPower P s‖ ≤ _
  rw [SmoothMobiusCorrection.norm_primeNormPower]
  have hn : (1 : ℝ) ≤ Ideal.absNorm P.val := by
    exact_mod_cast (show 1 ≤ Ideal.absNorm P.val from
      (by have := SmoothMobiusCorrection.prime_norm_two_le P; omega))
  exact (mul_le_of_le_one_left (by positivity) (ha _)).trans
    (Real.rpow_le_rpow_of_exponent_le hn (neg_le_neg hs))

theorem weighted_norm_le_half (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1)
    (P : PrimeIdeal) {s : ℂ} (hs : 1 ≤ s.re) : ‖weighted a s P.val‖ ≤ 1 / 2 := by
  refine (weighted_norm_le a ha P hs).trans ?_
  rw [Real.rpow_neg_one]
  have hn : (2 : ℝ) ≤ Ideal.absNorm P.val := by
    exact_mod_cast SmoothMobiusCorrection.prime_norm_two_le P
  exact inv_le_of_inv_le₀ (by norm_num) (by norm_num at *; exact hn)

theorem log_factor_norm_le (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1)
    (P : PrimeIdeal) {s : ℂ} {σ : ℝ} (hσ : 1 ≤ σ) (hs : σ ≤ s.re) :
    ‖-Complex.log (1 - weighted a s P.val)‖ ≤ majorant σ P := by
  have hhalf := weighted_norm_le_half a ha P (hσ.trans hs)
  have h := Complex.norm_log_one_add_half_le_self
    (z := -weighted a s P.val) (by simpa using hhalf)
  simp only [norm_neg, ← sub_eq_add_neg] at h ⊢
  exact h.trans (mul_le_mul_of_nonneg_left (weighted_norm_le a ha P hs) (by norm_num))

theorem weighted_differentiable (a : Ideal O →*₀ ℂ) (P : PrimeIdeal) :
    Differentiable ℂ (fun s ↦ weighted a s P.val) := by
  have hn : (Ideal.absNorm P.val : ℂ) ≠ 0 := by
    exact_mod_cast (SmoothMobiusCorrection.prime_norm_pos P).ne'
  change Differentiable ℂ (fun s ↦ a P.val * CubicEisenstein.fullIdealWeight s P.val)
  simp only [CubicEisenstein.fullIdealWeight, P.property.ne_zero, ite_false]
  exact (differentiable_id.neg.const_cpow (Or.inl hn)).const_mul _

theorem log_factor_differentiableOn (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1)
    (P : PrimeIdeal) :
    DifferentiableOn ℂ (fun s ↦ -Complex.log (1 - weighted a s P.val)) {s : ℂ | 1 < s.re} := by
  intro s hs
  change 1 < s.re at hs
  have hn := prime_norm_lt_one a ha s (by linarith : 0 < s.re) P
  have hslit : 1 - weighted a s P.val ∈ Complex.slitPlane := by
    simpa only [sub_eq_add_neg] using Complex.mem_slitPlane_of_norm_lt_one
      (z := -weighted a s P.val) (by simpa using hn)
  exact ((Complex.differentiableAt_log hslit).comp s
    ((differentiableAt_const (1 : ℂ)).sub (weighted_differentiable a P s))).neg.differentiableWithinAt

theorem eulerLog_differentiableOn_halfplane (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1)
    {σ : ℝ} (hσ : 1 < σ) : DifferentiableOn ℂ (eulerLog a) {s : ℂ | σ < s.re} := by
  apply Complex.differentiableOn_tsum_of_summable_norm (majorant_summable hσ)
  · intro P
    exact (log_factor_differentiableOn a ha P).mono (fun s hs ↦ hσ.trans hs)
  · exact isOpen_lt continuous_const Complex.continuous_re
  · intro P s hs
    exact log_factor_norm_le a ha P hσ.le hs.le

theorem eulerLog_differentiableOn (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1) :
    DifferentiableOn ℂ (eulerLog a) {s : ℂ | 1 < s.re} := by
  intro s hs
  change 1 < s.re at hs
  have hσ : 1 < (1 + s.re) / 2 := by linarith
  have hmem : s ∈ {w : ℂ | (1 + s.re) / 2 < w.re} := by dsimp; linarith
  exact ((eulerLog_differentiableOn_halfplane a ha hσ s hmem).differentiableAt
    ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hmem)).differentiableWithinAt

theorem exp_eulerLog_eq_series (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1)
    (s : ℂ) (hs : 1 < s.re) : Complex.exp (eulerLog a s) = series a s :=
  SevenEighths.HeckeBoundary.exp_log_euler_eq_series a ha s hs

def eulerLogBound : ℝ := 1 + ∑' P : PrimeIdeal, majorant (3 / 2) P

theorem eulerLogBound_ge_one : 1 ≤ eulerLogBound := by
  unfold eulerLogBound
  have h : 0 ≤ ∑' P : PrimeIdeal, majorant (3 / 2) P :=
    tsum_nonneg (fun P ↦ by unfold majorant; positivity)
  linarith

theorem eulerLog_norm_le (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1)
    {s : ℂ} (hs : 3 / 2 ≤ s.re) : ‖eulerLog a s‖ ≤ eulerLogBound := by
  have hb : ∀ P : PrimeIdeal, ‖-Complex.log (1 - weighted a s P.val)‖ ≤ majorant (3 / 2) P :=
    fun P ↦ log_factor_norm_le a ha P (by norm_num) hs
  have hsum := majorant_summable (by norm_num : (1 : ℝ) < 3 / 2)
  have hnorm : Summable (fun P : PrimeIdeal ↦ ‖-Complex.log (1 - weighted a s P.val)‖) :=
    hsum.of_nonneg_of_le (fun _ ↦ norm_nonneg _) hb
  calc
    ‖eulerLog a s‖ ≤ ∑' P : PrimeIdeal, ‖-Complex.log (1 - weighted a s P.val)‖ :=
      norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' P : PrimeIdeal, majorant (3 / 2) P := hnorm.tsum_le_tsum hb hsum
    _ ≤ eulerLogBound := by unfold eulerLogBound; linarith

theorem inner_disk_re {t : ℝ} {s : ℂ}
    (hs : s ∈ closedBall (2 + (t : ℂ) * Complex.I) (1 / 2)) : 3 / 2 ≤ s.re := by
  have hn : ‖(2 + (t : ℂ) * Complex.I) - s‖ ≤ 1 / 2 := by
    simpa only [mem_closedBall, dist_eq_norm, norm_sub_rev] using hs
  have hr := Complex.re_le_norm ((2 + (t : ℂ) * Complex.I) - s)
  norm_num at hr
  linarith

theorem eulerLog_inner_disk (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1) (t : ℝ) :
    DifferentiableOn ℂ (eulerLog a) (ball (2 + (t : ℂ) * Complex.I) (1 / 2)) ∧
      EqOn (Complex.exp ∘ eulerLog a) (series a)
        (ball (2 + (t : ℂ) * Complex.I) (1 / 2)) ∧
      ∀ s ∈ closedBall (2 + (t : ℂ) * Complex.I) (49 / 100),
        ‖eulerLog a s‖ ≤ eulerLogBound := by
  have hsub : ball (2 + (t : ℂ) * Complex.I) (1 / 2) ⊆ {s : ℂ | 1 < s.re} := by
    intro s hs
    have := inner_disk_re (ball_subset_closedBall hs)
    change 1 < s.re
    linarith
  refine ⟨(eulerLog_differentiableOn a ha).mono hsub, ?_, ?_⟩
  · intro s hs
    exact exp_eulerLog_eq_series a ha s (hsub hs)
  · intro s hs
    exact eulerLog_norm_le a ha (inner_disk_re (closedBall_subset_closedBall (by norm_num) hs))

theorem continued_inner_disk (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1)
    (L : ℂ → ℂ) (hL : ∀ s : ℂ, 1 < s.re → L s = series a s) (t : ℝ) :
    DifferentiableOn ℂ (eulerLog a) (ball (2 + (t : ℂ) * Complex.I) (1 / 2)) ∧
      EqOn (Complex.exp ∘ eulerLog a) L (ball (2 + (t : ℂ) * Complex.I) (1 / 2)) ∧
      ∀ s ∈ closedBall (2 + (t : ℂ) * Complex.I) (49 / 100),
        ‖eulerLog a s‖ ≤ eulerLogBound := by
  obtain ⟨hd, he, hb⟩ := eulerLog_inner_disk a ha t
  refine ⟨hd, ?_, hb⟩
  intro s hs
  have hr := inner_disk_re (ball_subset_closedBall hs)
  exact (he hs).trans (hL s (by linarith)).symm

def principalLog (s : ℂ) : ℂ := Complex.log (1 - 2 / (s + 1))

theorem norm_two_div_add_one_lt_one {s : ℂ} (hs : 1 < s.re) :
    ‖(2 : ℂ) / (s + 1)‖ < 1 := by
  have hr := Complex.re_le_norm (s + 1)
  norm_num at hr
  have hn : 0 < ‖s + 1‖ := by linarith
  rw [norm_div]
  norm_num only [Complex.norm_ofNat]
  exact (div_lt_one hn).mpr (by linarith)

theorem norm_two_div_add_one_le {s : ℂ} (hs : 3 / 2 ≤ s.re) :
    ‖(2 : ℂ) / (s + 1)‖ ≤ 4 / 5 := by
  have hr := Complex.re_le_norm (s + 1)
  norm_num at hr
  have hn : 0 < ‖s + 1‖ := by linarith
  rw [norm_div]
  norm_num only [Complex.norm_ofNat]
  exact (div_le_iff₀ hn).mpr (by linarith)

theorem principalLog_differentiableOn :
    DifferentiableOn ℂ principalLog {s : ℂ | 1 < s.re} := by
  intro s hs
  change 1 < s.re at hs
  have hnorm := norm_two_div_add_one_lt_one hs
  have hslit : 1 - (2 : ℂ) / (s + 1) ∈ Complex.slitPlane := by
    simpa only [sub_eq_add_neg, neg_div] using Complex.mem_slitPlane_of_norm_lt_one
      (z := -(2 : ℂ) / (s + 1)) (by simpa using hnorm)
  have hs1 : s + 1 ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num at hre
    linarith
  exact ((Complex.differentiableAt_log hslit).comp s
    ((differentiableAt_const (1 : ℂ)).sub ((differentiableAt_const (2 : ℂ)).div
      (differentiableAt_id.add_const 1) hs1))).differentiableWithinAt

theorem exp_principalLog {s : ℂ} (hs : 1 < s.re) :
    Complex.exp (principalLog s) = (s - 1) / (s + 1) := by
  have hs1 : s + 1 ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num at hre
    linarith
  rw [principalLog, Complex.exp_log (SmoothMobiusCorrection.one_sub_ne_zero
    (norm_two_div_add_one_lt_one hs))]
  field_simp
  ring

theorem principalLog_norm_le {s : ℂ} (hs : 3 / 2 ≤ s.re) : ‖principalLog s‖ ≤ 3 := by
  have hb := norm_two_div_add_one_le hs
  have hlt : ‖-(2 : ℂ) / (s + 1)‖ < 1 := by simpa using hb.trans_lt (by norm_num : (4 : ℝ) / 5 < 1)
  have h := Complex.norm_log_one_add_le hlt
  have hn : ‖-(2 : ℂ) / (s + 1)‖ = ‖(2 : ℂ) / (s + 1)‖ := by simp
  rw [hn] at h
  have heq : 1 + -(2 : ℂ) / (s + 1) = 1 - 2 / (s + 1) := by ring
  rw [heq] at h
  change ‖principalLog s‖ ≤ _ at h
  have hden : 0 < 1 - ‖(2 : ℂ) / (s + 1)‖ := by linarith
  have hinv : (1 - ‖(2 : ℂ) / (s + 1)‖)⁻¹ ≤ 5 := by
    rw [inv_eq_one_div, div_le_iff₀ hden]
    linarith
  have hnorm := norm_nonneg ((2 : ℂ) / (s + 1))
  have hsq : ‖(2 : ℂ) / (s + 1)‖ ^ 2 ≤ 16 / 25 := by nlinarith
  have hmul := mul_le_mul hsq hinv (inv_nonneg.mpr hden.le) (by norm_num : (0 : ℝ) ≤ 16 / 25)
  nlinarith

def principalEulerLog (a : Ideal O →*₀ ℂ) (s : ℂ) : ℂ := principalLog s + eulerLog a s

theorem principalEulerLog_differentiableOn (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1) :
    DifferentiableOn ℂ (principalEulerLog a) {s : ℂ | 1 < s.re} :=
  principalLog_differentiableOn.add (eulerLog_differentiableOn a ha)

theorem exp_principalEulerLog (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1)
    {s : ℂ} (hs : 1 < s.re) :
    Complex.exp (principalEulerLog a s) = ((s - 1) / (s + 1)) * series a s := by
  rw [principalEulerLog, Complex.exp_add, exp_principalLog hs, exp_eulerLog_eq_series a ha s hs]

theorem principalEulerLog_norm_le (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1)
    {s : ℂ} (hs : 3 / 2 ≤ s.re) : ‖principalEulerLog a s‖ ≤ 3 + eulerLogBound :=
  (norm_add_le _ _).trans (add_le_add (principalLog_norm_le hs) (eulerLog_norm_le a ha hs))

theorem principal_continued_inner_disk (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1)
    (L : ℂ → ℂ)
    (hL : ∀ s : ℂ, 1 < s.re → L s = ((s - 1) / (s + 1)) * series a s) (t : ℝ) :
    DifferentiableOn ℂ (principalEulerLog a) (ball (2 + (t : ℂ) * Complex.I) (1 / 2)) ∧
      EqOn (Complex.exp ∘ principalEulerLog a) L
        (ball (2 + (t : ℂ) * Complex.I) (1 / 2)) ∧
      ∀ s ∈ closedBall (2 + (t : ℂ) * Complex.I) (49 / 100),
        ‖principalEulerLog a s‖ ≤ 3 + eulerLogBound := by
  have hsub : ball (2 + (t : ℂ) * Complex.I) (1 / 2) ⊆ {s : ℂ | 1 < s.re} := by
    intro s hs
    have := inner_disk_re (ball_subset_closedBall hs)
    change 1 < s.re
    linarith
  refine ⟨(principalEulerLog_differentiableOn a ha).mono hsub, ?_, ?_⟩
  · intro s hs
    exact (exp_principalEulerLog a ha (hsub hs)).trans (hL s (hsub hs)).symm
  · intro s hs
    exact principalEulerLog_norm_le a ha
      (inner_disk_re (closedBall_subset_closedBall (by norm_num) hs))

theorem residue_continued_inner_disk (M : Ideal O) [Finite (O ⧸ M)]
    (χ : MulChar (O ⧸ M) ℂ) (hχ : UnitInvariant M χ) (L : ℂ → ℂ)
    (hL : ∀ s : ℂ, 1 < s.re → L s = series (ofResidue M χ hχ) s) (t : ℝ) :
    DifferentiableOn ℂ (eulerLog (ofResidue M χ hχ))
        (ball (2 + (t : ℂ) * Complex.I) (1 / 2)) ∧
      EqOn (Complex.exp ∘ eulerLog (ofResidue M χ hχ)) L
        (ball (2 + (t : ℂ) * Complex.I) (1 / 2)) ∧
      ∀ s ∈ closedBall (2 + (t : ℂ) * Complex.I) (49 / 100),
        ‖eulerLog (ofResidue M χ hχ) s‖ ≤ eulerLogBound :=
  continued_inner_disk _ (norm_ofResidue_le_one M χ hχ) L hL t

theorem continued_logarithmic_control {e M ε : ℝ}
    (he : 0 < e) (he' : e < 1 / 1000) (hM : 1 ≤ M) (hε : 0 < ε) :
    ∃ D : ℝ, 0 < D ∧ ∀ (b C t : ℝ) (a : Ideal O →*₀ ℂ),
      (∀ I, ‖a I‖ ≤ 1) → ∀ L : ℂ → ℂ,
      1 / 2 ≤ b → b ≤ 1 → Real.exp 1 ≤ C →
      (∀ s : ℂ, 1 < s.re → L s = series a s) →
      DifferentiableOn ℂ L (ball (2 + (t : ℂ) * Complex.I) (2 - b - 2 * e)) →
      (∀ z ∈ ball (2 + (t : ℂ) * Complex.I) (2 - b - 2 * e), L z ≠ 0) →
      (∀ z ∈ ball (2 + (t : ℂ) * Complex.I) (2 - b - 3 * e), ‖L z‖ ≤ C ^ M) →
      (∀ z ∈ closedBall (2 + (t : ℂ) * Complex.I) (2 - b - 6 * e),
        ‖L z‖ + ‖(L z)⁻¹‖ ≤ D * C ^ ε) ∧
      (∀ z ∈ closedBall (2 + (t : ℂ) * Complex.I) (2 - b - 8 * e),
        ‖deriv L z / L z‖ ≤
          (LogarithmicControl.outerConstant e eulerLogBound M / (2 * e)) * Real.log C) := by
  obtain ⟨D, hD, hbound⟩ := LogarithmicControl.logarithmic_control he he'
    eulerLogBound_ge_one hM hε
  refine ⟨D, hD, ?_⟩
  intro b C t a ha L hb hb' hC hEq hL h0 hp
  obtain ⟨hE, heq, hEb⟩ := continued_inner_disk a ha L hEq t
  exact hbound b C L (eulerLog a) (2 + (t : ℂ) * Complex.I)
    hb hb' hC hL h0 hp hE heq hEb

theorem principal_continued_logarithmic_control {e M ε : ℝ}
    (he : 0 < e) (he' : e < 1 / 1000) (hM : 1 ≤ M) (hε : 0 < ε) :
    ∃ D : ℝ, 0 < D ∧ ∀ (b C t : ℝ) (a : Ideal O →*₀ ℂ),
      (∀ I, ‖a I‖ ≤ 1) → ∀ L : ℂ → ℂ,
      1 / 2 ≤ b → b ≤ 1 → Real.exp 1 ≤ C →
      (∀ s : ℂ, 1 < s.re → L s = ((s - 1) / (s + 1)) * series a s) →
      DifferentiableOn ℂ L (ball (2 + (t : ℂ) * Complex.I) (2 - b - 2 * e)) →
      (∀ z ∈ ball (2 + (t : ℂ) * Complex.I) (2 - b - 2 * e), L z ≠ 0) →
      (∀ z ∈ ball (2 + (t : ℂ) * Complex.I) (2 - b - 3 * e), ‖L z‖ ≤ C ^ M) →
      (∀ z ∈ closedBall (2 + (t : ℂ) * Complex.I) (2 - b - 6 * e),
        ‖L z‖ + ‖(L z)⁻¹‖ ≤ D * C ^ ε) ∧
      (∀ z ∈ closedBall (2 + (t : ℂ) * Complex.I) (2 - b - 8 * e),
        ‖deriv L z / L z‖ ≤
          (LogarithmicControl.outerConstant e (3 + eulerLogBound) M / (2 * e)) * Real.log C) := by
  have hA : 1 ≤ 3 + eulerLogBound := by linarith [eulerLogBound_ge_one]
  obtain ⟨D, hD, hbound⟩ := LogarithmicControl.logarithmic_control he he' hA hM hε
  refine ⟨D, hD, ?_⟩
  intro b C t a ha L hb hb' hC hEq hL h0 hp
  obtain ⟨hE, heq, hEb⟩ := principal_continued_inner_disk a ha L hEq t
  exact hbound b C L (principalEulerLog a) (2 + (t : ℂ) * Complex.I)
    hb hb' hC hL h0 hp hE heq hEb

end SevenEighths.HeckeEulerLog

end

end OAI
