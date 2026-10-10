import OAI.NumberTheory.CubicMoment.Angular.AngularGamma
import OAI.NumberTheory.CubicMoment.Estimates.DualTailTruncation

namespace OAI

/-! The fixed-angular far-left tail, with explicit natural dual length.
Only the constant changes with the angular shift; every power of the
length, conductor and height is retained from the full ideal series. -/
noncomputable section
open MeasureTheory Set
open scoped ContDiff
namespace CubicFirstMoment

/-- The integrand of the omitted part of the functional-equation series
on the line `Re s = 1/2-m`. -/
def angularDualTailIntegrand (W : ℝ → ℂ) (χ : EisensteinIdealExponent → ℂ)
    (ε : ℂ) (A Z J k : ℝ) (m : ℕ) (t τ : ℝ) : ℂ :=
  let s : ℂ := (1/2:ℂ)-(m:ℂ)+(τ:ℂ)*Complex.I
  let u : ℂ := s-(t:ℂ)*Complex.I
  mellin W s*(Z:ℂ)^s*ε*(A:ℂ)^(1-2*u)*
    (Complex.Gamma (1-u+(k:ℂ))/Complex.Gamma (u+(k:ℂ)))*idealDirichletTail χ J (1-u)

lemma norm_angularDualTailIntegrand_le (W : ℝ → ℂ)
    (χ : EisensteinIdealExponent → ℂ) (hχ : ∀ ν, ‖χ ν‖ ≤ 1) {k : ℝ} (hk : 0 ≤ k)
    {ε : ℂ} (hε : ‖ε‖ ≤ 1) {A Z J : ℝ} (hA : 0 < A) (hZ : 0 < Z)
    (hJ : 0 < J) {m : ℕ} (hm : 2 ≤ m) (t τ : ℝ) :
    ‖angularDualTailIntegrand W χ ε A Z J k m t τ‖ ≤
      (Z^(1/2-(m:ℝ))*A^(2*m)*(k+3*(m:ℝ)+1)^(2*m)*J^(3/2-(m:ℝ))*
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
  have hg : ‖Complex.Gamma (1-u+(k:ℂ))/Complex.Gamma (u+(k:ℂ))‖ ≤
      (k+3*(m:ℝ)+1)^(2*m)*(1+|τ-t|)^(2*m) := by
    rw [hdu,hu]
    have hnum : (1/2:ℂ)+(m:ℂ)-((τ-t:ℝ):ℂ)*Complex.I+(k:ℂ) =
        (1/2:ℂ)+(m:ℂ)+(k:ℂ)-((τ-t:ℝ):ℂ)*Complex.I := by ring
    have hden : (1/2:ℂ)-(m:ℂ)+((τ-t:ℝ):ℂ)*Complex.I+(k:ℂ) =
        (1/2:ℂ)-(m:ℂ)+(k:ℂ)+((τ-t:ℝ):ℂ)*Complex.I := by ring
    rw [hnum,hden]
    exact norm_angular_gamma_left_ratio_le hk m (τ-t)
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
    (Complex.Gamma (1-u+(k:ℂ))/Complex.Gamma (u+(k:ℂ)))*idealDirichletTail χ J (1-u)‖ ≤ _
  simp only [norm_mul,hAs,hZs]
  calc
    _ ≤ ‖mellin W ((1/2:ℂ)-(m:ℂ)+(τ:ℂ)*Complex.I)‖ *
        Z^(1/2-(m:ℝ))*1*A^(2*m) *
        ((k+3*(m:ℝ)+1)^(2*m)*(1+|τ-t|)^(2*m)) *
        (J^(3/2-(m:ℝ))*(∑' ν : EisensteinIdealExponent, idealExponentNorm ν^(-(2:ℝ)))) := by
      gcongr
    _ = _ := by ring

/-- An arbitrary-order tail bound with the natural dual length displayed.
The constant depends only on the fixed weight and the chosen order `m`. -/
theorem angular_dual_tail_integral_bound (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hpos : tsupport W ⊆ Ioi 0) (hsm : ContDiff ℝ ∞ W)
    {k : ℝ} (hk : 0 ≤ k) {m : ℕ} (hm : 2 ≤ m) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (χ : EisensteinIdealExponent → ℂ),
      (∀ ν, ‖χ ν‖ ≤ 1) → ∀ (ε : ℂ), ‖ε‖ ≤ 1 →
      ∀ (A Z J : ℝ), 0 < A → 0 < Z → 0 < J → ∀ t : ℝ,
      ‖∫ τ : ℝ, angularDualTailIntegrand W χ ε A Z J k m t τ‖ ≤
        C*Z^(1/2:ℝ)*J^(3/2:ℝ)*((A^2*(1+|t|)^2)/(Z*J))^m := by
  obtain ⟨Cw,hCw,hdecay⟩ := mellin_polynomial_majorant W hW hpos hsm
    (1/2-(m:ℝ)) (2*m)
  let S : ℝ := ∑' ν : EisensteinIdealExponent, idealExponentNorm ν^(-(2:ℝ))
  let I : ℝ := ∫ τ : ℝ, mellinEdgeMajorant 1 τ
  have hS : 0 ≤ S := tsum_nonneg fun ν => Real.rpow_nonneg (idealExponentNorm_pos ν).le _
  have hI : 0 ≤ I := integral_nonneg fun τ => by dsimp [mellinEdgeMajorant]; positivity
  refine ⟨(k+3*(m:ℝ)+1)^(2*m)*S*Cw*I,by positivity,?_⟩
  intro χ hχ ε hε A Z J hA hZ hJ t
  let B : ℝ := Z^(1/2-(m:ℝ))*A^(2*m)*(k+3*(m:ℝ)+1)^(2*m)*J^(3/2-(m:ℝ))*S
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hb (τ : ℝ) : ‖angularDualTailIntegrand W χ ε A Z J k m t τ‖ ≤
      mellinEdgeMajorant (B*Cw*(1+|t|)^(2*m)) τ := by
    have hd := hdecay t τ
    have he : (((1/2-(m:ℝ):ℝ):ℂ)+(τ:ℂ)*Complex.I) =
        (1/2:ℂ)-(m:ℂ)+(τ:ℂ)*Complex.I := by push_cast; ring
    rw [he] at hd
    calc
      _ ≤ B*(‖mellin W ((1/2:ℂ)-(m:ℂ)+(τ:ℂ)*Complex.I)‖*(1+|τ-t|)^(2*m)) :=
        norm_angularDualTailIntegrand_le W χ hχ hk hε hA hZ hJ hm t τ
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
    _ = ((k+3*(m:ℝ)+1)^(2*m)*S*Cw*I) *
        (Z^(1/2-(m:ℝ))*A^(2*m)*J^(3/2-(m:ℝ))*(1+|t|)^(2*m)) := by dsimp [B]; ring
    _ = _ := by rw [dual_tail_scale_identity hZ hJ]; ring


/-- The omitted far-left tail is smaller than every fixed negative power
once the cutoff exceeds the natural length by `Y^δ`. Only polynomial
upper bounds for the two lengths are used. -/
theorem angular_dual_tail_arbitrary_power (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hpos : tsupport W ⊆ Ioi 0) (hsm : ContDiff ℝ ∞ W)
    {k : ℝ} (hk : 0 ≤ k) {δ : ℝ} (hδ : 0 < δ) (B R : ℝ) :
    ∃ (m : ℕ) (C : ℝ), 2 ≤ m ∧ 0 ≤ C ∧
      ∀ (χ : EisensteinIdealExponent → ℂ), (∀ ν, ‖χ ν‖ ≤ 1) →
      ∀ (ε : ℂ), ‖ε‖ ≤ 1 → ∀ (Y A Z J : ℝ),
      1 ≤ Y → 0 < A → 0 < Z → 0 < J → Z ≤ Y^B → J ≤ Y^B →
      ∀ t : ℝ, (A^2*(1+|t|)^2)/(Z*J) ≤ Y^(-δ) →
      ‖∫ τ : ℝ, angularDualTailIntegrand W χ ε A Z J k m t τ‖ ≤ C*Y^(-R) := by
  obtain ⟨m,hm2,hm⟩ := exists_dual_tail_order hδ B R
  obtain ⟨C,hC,hbound⟩ := angular_dual_tail_integral_bound W hW hpos hsm hk hm2
  refine ⟨m,C,hm2,hC,?_⟩
  intro χ hχ ε hε Y A Z J hY hA hZ hJ hZB hJB t hcut
  calc
    _ ≤ C*Z^(1/2:ℝ)*J^(3/2:ℝ)*((A^2*(1+|t|)^2)/(Z*J))^m :=
      hbound χ hχ ε hε A Z J hA hZ hJ t
    _ = C*(Z^(1/2:ℝ)*J^(3/2:ℝ)*((A^2*(1+|t|)^2)/(Z*J))^m) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (dual_tail_scale_bound hY hA hZ hJ hZB hJB hcut hm) hC


end CubicFirstMoment

end

end OAI
