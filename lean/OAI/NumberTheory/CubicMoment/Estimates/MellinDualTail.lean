import OAI.NumberTheory.CubicMoment.Estimates.GammaLeftLine
import OAI.NumberTheory.CubicMoment.Estimates.IdealMellinSeries
import OAI.NumberTheory.CubicMoment.Estimates.MellinHeckeContour

namespace OAI

/-! Actual far-left dual-series tails. The integer-line Gamma estimate
and smooth Mellin decay provide the analytic bounds. -/

noncomputable section
open MeasureTheory Set
open scoped ContDiff
namespace CubicFirstMoment

lemma shifted_power_le (N : ℕ) (τ t : ℝ) :
    (1+|τ-t|)^N ≤ (1+|t|)^N*(1+|τ|)^N := by
  rw [← mul_pow]
  apply pow_le_pow_left₀ (by positivity)
  have hd := abs_sub_le τ 0 t
  simp only [sub_zero,zero_sub,abs_neg] at hd
  nlinarith [mul_nonneg (abs_nonneg τ) (abs_nonneg t)]

lemma mellin_polynomial_majorant (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hpos : tsupport W ⊆ Ioi 0) (hsm : ContDiff ℝ ∞ W) (σ : ℝ) (N : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ t τ : ℝ,
      ‖mellin W (σ+(τ:ℂ)*Complex.I)‖*(1+|τ-t|)^N ≤
        mellinEdgeMajorant (C*(1+|t|)^N) τ := by
  obtain ⟨C,hC,hdecay⟩ := smooth_mellin_vertical_decay W hW hpos hsm σ (N+2)
  refine ⟨C,hC,?_⟩
  intro t τ
  unfold mellinEdgeMajorant
  apply (le_div_iff₀ (by positivity : 0 < (1+|τ|)^2)).mpr
  calc
    _ ≤ (‖mellin W (σ+(τ:ℂ)*Complex.I)‖*
        ((1+|t|)^N*(1+|τ|)^N))*(1+|τ|)^2 := by
      gcongr
      exact shifted_power_le N τ t
    _ = (1+|t|)^N*((1+|τ|)^(N+2)*‖mellin W (σ+(τ:ℂ)*Complex.I)‖) := by
      rw [pow_add]
      ring
    _ ≤ (1+|t|)^N*C := mul_le_mul_of_nonneg_left (hdecay τ) (by positivity)
    _ = _ := mul_comm _ _

lemma ideal_norm_tail_le {J r : ℝ} (hJ : 0 < J) (hr : 2 < r) :
    (∑' ν : EisensteinIdealExponent,
      if J < idealExponentNorm ν then idealExponentNorm ν^(-r) else 0) ≤
      J^(2-r)*(∑' ν : EisensteinIdealExponent, idealExponentNorm ν^(-(2:ℝ))) := by
  have ht := (summable_ideal_norm_rpow (by linarith : 1 < r)).indicator
    (fun ν => J < idealExponentNorm ν)
  have hs := (summable_ideal_norm_rpow (by norm_num : (1:ℝ) < 2)).mul_left (J^(2-r))
  rw [← tsum_mul_left]
  apply Summable.tsum_le_tsum _ ht hs
  intro ν
  change (if J < idealExponentNorm ν then idealExponentNorm ν^(-r) else 0) ≤
    J^(2-r)*idealExponentNorm ν^(-(2:ℝ))
  by_cases hν : J < idealExponentNorm ν
  · simp only [hν,ite_true]
    have hn := idealExponentNorm_pos ν
    calc
      _ = idealExponentNorm ν^(2-r)*idealExponentNorm ν^(-(2:ℝ)) := by
        rw [← Real.rpow_add hn]
        congr 1
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow_of_nonpos hJ hν.le (by linarith)) (by positivity)
  · simp only [hν,ite_false]
    exact mul_nonneg (Real.rpow_nonneg hJ.le _)
      (Real.rpow_nonneg (idealExponentNorm_pos ν).le _)

/-- The tail is the tail of the full ideal series, with all Euler factors. -/
def idealDirichletTail (χ : EisensteinIdealExponent → ℂ) (J : ℝ) (s : ℂ) : ℂ :=
  ∑' ν : EisensteinIdealExponent,
    if J < idealExponentNorm ν then χ ν*(idealExponentNorm ν:ℂ)^(-s) else 0

lemma norm_idealDirichletTail_le (χ : EisensteinIdealExponent → ℂ)
    (hχ : ∀ ν, ‖χ ν‖ ≤ 1) {J : ℝ} (hJ : 0 < J) (s : ℂ) (hs : 2 < s.re) :
    ‖idealDirichletTail χ J s‖ ≤
      J^(2-s.re)*(∑' ν : EisensteinIdealExponent, idealExponentNorm ν^(-(2:ℝ))) := by
  let f (ν : EisensteinIdealExponent) : ℂ :=
    if J < idealExponentNorm ν then χ ν*(idealExponentNorm ν:ℂ)^(-s) else 0
  let b (ν : EisensteinIdealExponent) : ℝ :=
    if J < idealExponentNorm ν then idealExponentNorm ν^(-s.re) else 0
  have hb : Summable b :=
    (summable_ideal_norm_rpow (by linarith : 1 < s.re)).indicator _
  have hf (ν : EisensteinIdealExponent) : ‖f ν‖ ≤ b ν := by
    dsimp [f,b]
    split_ifs with hν
    · rw [norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos (idealExponentNorm_pos ν),
        Complex.neg_re]
      exact mul_le_of_le_one_left (Real.rpow_nonneg (idealExponentNorm_pos ν).le _) (hχ ν)
    · simp
  have hfn : Summable (fun ν => ‖f ν‖) :=
    hb.of_norm_bounded (fun ν => by rw [Real.norm_eq_abs,abs_of_nonneg (_root_.norm_nonneg _)]; exact hf ν)
  calc
    _ ≤ ∑' ν, ‖f ν‖ := norm_tsum_le_tsum_norm hfn
    _ ≤ ∑' ν, b ν := Summable.tsum_le_tsum hf hfn hb
    _ ≤ _ := ideal_norm_tail_le hJ hs

/-- The integrand of the omitted part of the functional-equation series
on the line `Re s = 1/2-m`. -/
def heckeDualTailIntegrand (W : ℝ → ℂ) (χ : EisensteinIdealExponent → ℂ)
    (ε : ℂ) (A Z J : ℝ) (m : ℕ) (t τ : ℝ) : ℂ :=
  let s : ℂ := (1/2:ℂ)-(m:ℂ)+(τ:ℂ)*Complex.I
  let u : ℂ := s-(t:ℂ)*Complex.I
  mellin W s*(Z:ℂ)^s*ε*(A:ℂ)^(1-2*u)*
    (Complex.Gamma (1-u)/Complex.Gamma u)*idealDirichletTail χ J (1-u)

lemma norm_heckeDualTailIntegrand_le (W : ℝ → ℂ)
    (χ : EisensteinIdealExponent → ℂ) (hχ : ∀ ν, ‖χ ν‖ ≤ 1)
    {ε : ℂ} (hε : ‖ε‖ ≤ 1) {A Z J : ℝ} (hA : 0 < A) (hZ : 0 < Z)
    (hJ : 0 < J) {m : ℕ} (hm : 2 ≤ m) (t τ : ℝ) :
    ‖heckeDualTailIntegrand W χ ε A Z J m t τ‖ ≤
      (Z^(1/2-(m:ℝ))*A^(2*m)*(3*(m:ℝ)+1)^(2*m)*J^(3/2-(m:ℝ))*
        (∑' ν : EisensteinIdealExponent, idealExponentNorm ν^(-(2:ℝ)))) *
      (‖mellin W ((1/2:ℂ)-(m:ℂ)+(τ:ℂ)*Complex.I)‖*(1+|τ-t|)^(2*m)) := by
  let u : ℂ := (1/2:ℂ)-(m:ℂ)+(τ:ℂ)*Complex.I-(t:ℂ)*Complex.I
  have hu : u = (1/2:ℂ)-(m:ℂ)+((τ-t:ℝ):ℂ)*Complex.I := by
    dsimp [u]
    push_cast
    ring
  have hdu : 1-u = (1/2:ℂ)+(m:ℂ)-((τ-t:ℝ):ℂ)*Complex.I := by
    dsimp [u]
    push_cast
    ring
  have hur : (1-u).re = 1/2+(m:ℝ) := by rw [hdu]; simp
  have hd := norm_idealDirichletTail_le χ hχ hJ (1-u)
    (by
      rw [hur]
      have hm' : (2:ℝ) ≤ m := by exact_mod_cast hm
      linarith)
  rw [hur] at hd
  have hde : (2:ℝ)-(1/2+(m:ℝ)) = 3/2-(m:ℝ) := by ring
  rw [hde] at hd
  have hg : ‖Complex.Gamma (1-u)/Complex.Gamma u‖ ≤
      (3*(m:ℝ)+1)^(2*m)*(1+|τ-t|)^(2*m) := by
    rw [hdu,hu]
    exact norm_gamma_left_ratio_le m (τ-t)
  have hAs : ‖(A:ℂ)^(1-2*u)‖ = A^(2*m) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hA]
    have hre : (1-2*u).re = ((2*m:ℕ):ℝ) := by dsimp [u]; simp; ring
    rw [hre,Real.rpow_natCast]
  have hZs : ‖(Z:ℂ)^((1/2:ℂ)-(m:ℂ)+(τ:ℂ)*Complex.I)‖ =
      Z^(1/2-(m:ℝ)) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hZ]
    congr 1
    simp
  change ‖mellin W _ * (Z:ℂ)^_ * ε * (A:ℂ)^(1-2*u) *
    (Complex.Gamma (1-u)/Complex.Gamma u)*idealDirichletTail χ J (1-u)‖ ≤ _
  simp only [norm_mul,hAs,hZs]
  calc
    _ ≤ ‖mellin W ((1/2:ℂ)-(m:ℂ)+(τ:ℂ)*Complex.I)‖ *
        Z^(1/2-(m:ℝ))*1*A^(2*m) *
        ((3*(m:ℝ)+1)^(2*m)*(1+|τ-t|)^(2*m)) *
        (J^(3/2-(m:ℝ))*(∑' ν : EisensteinIdealExponent, idealExponentNorm ν^(-(2:ℝ)))) := by
      gcongr
    _ = _ := by ring

lemma dual_tail_scale_identity {A Z J : ℝ} (hZ : 0 < Z) (hJ : 0 < J)
    (m : ℕ) (t : ℝ) :
    Z^(1/2-(m:ℝ))*A^(2*m)*J^(3/2-(m:ℝ))*(1+|t|)^(2*m) =
      Z^(1/2:ℝ)*J^(3/2:ℝ)*((A^2*(1+|t|)^2)/(Z*J))^m := by
  rw [Real.rpow_sub hZ,Real.rpow_sub hJ,Real.rpow_natCast,Real.rpow_natCast,
    div_pow,mul_pow,mul_pow,pow_mul,pow_mul]
  ring

/-- An arbitrary-order tail bound with the natural dual length displayed.
The constant depends only on the fixed weight and the chosen order `m`. -/
theorem hecke_dual_tail_integral_bound (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hpos : tsupport W ⊆ Ioi 0) (hsm : ContDiff ℝ ∞ W)
    {m : ℕ} (hm : 2 ≤ m) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (χ : EisensteinIdealExponent → ℂ),
      (∀ ν, ‖χ ν‖ ≤ 1) → ∀ (ε : ℂ), ‖ε‖ ≤ 1 →
      ∀ (A Z J : ℝ), 0 < A → 0 < Z → 0 < J → ∀ t : ℝ,
      ‖∫ τ : ℝ, heckeDualTailIntegrand W χ ε A Z J m t τ‖ ≤
        C*Z^(1/2:ℝ)*J^(3/2:ℝ)*((A^2*(1+|t|)^2)/(Z*J))^m := by
  obtain ⟨Cw,hCw,hdecay⟩ := mellin_polynomial_majorant W hW hpos hsm
    (1/2-(m:ℝ)) (2*m)
  let S : ℝ := ∑' ν : EisensteinIdealExponent, idealExponentNorm ν^(-(2:ℝ))
  let I : ℝ := ∫ τ : ℝ, mellinEdgeMajorant 1 τ
  have hS : 0 ≤ S := tsum_nonneg fun ν => Real.rpow_nonneg (idealExponentNorm_pos ν).le _
  have hI : 0 ≤ I := integral_nonneg fun τ => by dsimp [mellinEdgeMajorant]; positivity
  refine ⟨(3*(m:ℝ)+1)^(2*m)*S*Cw*I,by positivity,?_⟩
  intro χ hχ ε hε A Z J hA hZ hJ t
  let B : ℝ := Z^(1/2-(m:ℝ))*A^(2*m)*(3*(m:ℝ)+1)^(2*m)*J^(3/2-(m:ℝ))*S
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hb (τ : ℝ) : ‖heckeDualTailIntegrand W χ ε A Z J m t τ‖ ≤
      mellinEdgeMajorant (B*Cw*(1+|t|)^(2*m)) τ := by
    have hd := hdecay t τ
    have he : (((1/2-(m:ℝ):ℝ):ℂ)+(τ:ℂ)*Complex.I) =
        (1/2:ℂ)-(m:ℂ)+(τ:ℂ)*Complex.I := by push_cast; ring
    rw [he] at hd
    calc
      _ ≤ B*(‖mellin W ((1/2:ℂ)-(m:ℂ)+(τ:ℂ)*Complex.I)‖*(1+|τ-t|)^(2*m)) :=
        norm_heckeDualTailIntegrand_le W χ hχ hε hA hZ hJ hm t τ
      _ ≤ B*mellinEdgeMajorant (Cw*(1+|t|)^(2*m)) τ :=
        mul_le_mul_of_nonneg_left hd hB
      _ = _ := by unfold mellinEdgeMajorant; ring
  calc
    _ ≤ ∫ τ : ℝ, mellinEdgeMajorant (B*Cw*(1+|t|)^(2*m)) τ :=
      norm_integral_le_of_norm_le (mellinEdgeMajorant_integrable _) (Filter.Eventually.of_forall hb)
    _ = B*Cw*(1+|t|)^(2*m)*I := by
      have he : (fun τ => mellinEdgeMajorant (B*Cw*(1+|t|)^(2*m)) τ) =
          fun τ => (B*Cw*(1+|t|)^(2*m))*mellinEdgeMajorant 1 τ := by
        funext τ
        unfold mellinEdgeMajorant
        ring
      rw [he,integral_const_mul]
    _ = ((3*(m:ℝ)+1)^(2*m)*S*Cw*I) *
        (Z^(1/2-(m:ℝ))*A^(2*m)*J^(3/2-(m:ℝ))*(1+|t|)^(2*m)) := by dsimp [B]; ring
    _ = _ := by rw [dual_tail_scale_identity hZ hJ]; ring

end CubicFirstMoment

end

end OAI
