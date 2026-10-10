import OAI.MathematicalPhysics.ContinuumCoulomb.Nuclei.MoserFlux
import OAI.MathematicalPhysics.ContinuumCoulomb.Programs.PiProgram

namespace OAI

/-! Stable algebraic evaluation of the actual Moser velocity. The
denominator is clamped below by the fixed positive density; this clamp
does not affect the exact field and cannot increase denominator error. -/

noncomputable section
namespace ContinuumCoulomb.MoserVelocityNumerics
open NeutralAtom (dirPartial axis coordinateLaplacian)

theorem component_formula (rho : ℝ) (V : Position → ℝ) (t : ℝ) (x : Position) (a : Fin 3) :
    moserVelocity rho V t x a =
      -dirPartial V (axis a) x/(4*Real.pi*rho+t*coordinateLaplacian V x) := by
  have hden : 4*Real.pi*homotopyDensity rho V t x =
      4*Real.pi*rho+t*coordinateLaplacian V x := by
    unfold homotopyDensity manufacturedCharge
    field_simp [Real.pi_ne_zero]
  change -dirPartial V (axis a) x/(4*Real.pi*homotopyDensity rho V t x) = _
  rw [hden]

theorem denominator_lower {rho : ℝ} (hrho : 0 ≤ rho) (V : Position → ℝ)
    (hcharge : ∀ x, |manufacturedCharge V x| ≤ rho/2)
    {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) (x : Position) :
    rho ≤ 4*Real.pi*rho+t*coordinateLaplacian V x := by
  have h := mul_le_mul_of_nonneg_left (homotopyDensity_bounds V hcharge ht.1 ht.2 x).1
    (show (0:ℝ) ≤ 4*Real.pi by positivity)
  have heq : 4*Real.pi*homotopyDensity rho V t x =
      4*Real.pi*rho+t*coordinateLaplacian V x := by
    unfold homotopyDensity manufacturedCharge
    field_simp [Real.pi_ne_zero]
  rw [heq] at h
  have hp : rho ≤ 2*Real.pi*rho :=
    le_mul_of_one_le_left hrho (by linarith [Real.pi_gt_three])
  exact hp.trans (by convert h using 1; ring)

theorem clamp_error {rho q d ε : ℝ} (hd : rho ≤ d) (hq : |q-d| ≤ ε) :
    |max rho q-d| ≤ ε := by
  by_cases h : rho ≤ q
  · simpa only [max_eq_right h] using hq
  · rw [max_eq_left (le_of_not_ge h),abs_of_nonpos (sub_nonpos.mpr hd)]
    have hl := (abs_le.mp hq).1
    linarith

theorem quotient_error {g g' d d' B ε η : ℝ}
    (hd : 1 ≤ d) (hd' : 1 ≤ d') (hg : |g| ≤ B)
    (hgn : |g'-g| ≤ ε) (hden : |d'-d| ≤ η) :
    |(-g')/d'-(-g)/d| ≤ ε+B*η := by
  have hdp : 0 < d := by linarith
  have hdp' : 0 < d' := by linarith
  have hi : d⁻¹ ≤ 1 := (inv_le_one₀ hdp).mpr hd
  have hi' : d'⁻¹ ≤ 1 := (inv_le_one₀ hdp').mpr hd'
  have hB : 0 ≤ B := (abs_nonneg _).trans hg
  have hη : 0 ≤ η := (abs_nonneg _).trans hden
  have hε : 0 ≤ ε := (abs_nonneg _).trans hgn
  have heq : (-g')/d'-(-g)/d =
      -(g'-g)*d'⁻¹+g*(d'-d)*d'⁻¹*d⁻¹ := by
    field_simp [hdp.ne',hdp'.ne']
    ring
  rw [heq]
  apply (abs_add_le _ _).trans
  rw [abs_mul,abs_neg,abs_mul,abs_mul,abs_mul,
    abs_of_pos (inv_pos.mpr hdp),abs_of_pos (inv_pos.mpr hdp')]
  have hfirst : |g'-g| * d'⁻¹ ≤ ε := by
    exact (mul_le_mul hgn hi' (inv_nonneg.mpr hdp'.le) hε).trans_eq (mul_one _)
  have hsecond : |g| * |d'-d| * d'⁻¹*d⁻¹ ≤ B*η := by
    calc
      _ ≤ B*η*1*1 := by gcongr
      _ = _ := by ring
  exact add_le_add hfirst hsecond

theorem component_error (rho : ℝ) (hrho : 1 ≤ rho)
    (V : Position → ℝ) (hcharge : ∀ x, |manufacturedCharge V x| ≤ rho/2)
    {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) (x : Position) (a : Fin 3)
    (g lap pi' : ℝ) {B ε : ℝ}
    (hB : |dirPartial V (axis a) x| ≤ B)
    (hg : |g-dirPartial V (axis a) x| ≤ ε)
    (hlap : |lap-coordinateLaplacian V x| ≤ ε)
    (hpi : |pi'-Real.pi| ≤ ε) :
    |(-g)/max rho (4*pi'*rho+t*lap)-moserVelocity rho V t x a| ≤
      (1+B*(4*rho+1))*ε := by
  have hrho0 : 0 ≤ rho := by linarith
  have hε : 0 ≤ ε := (abs_nonneg _).trans hg
  have hraw : |(4*pi'*rho+t*lap)-(4*Real.pi*rho+t*coordinateLaplacian V x)| ≤
      (4*rho+1)*ε := by
    have hid : (4*pi'*rho+t*lap)-(4*Real.pi*rho+t*coordinateLaplacian V x) =
        (4*rho)*(pi'-Real.pi)+t*(lap-coordinateLaplacian V x) := by ring
    rw [hid]
    apply (abs_add_le _ _).trans
    simp only [abs_mul,abs_of_nonneg hrho0,abs_of_nonneg ht.1,
      abs_of_pos (by norm_num : (0:ℝ)<4)]
    have hfirst := mul_le_mul_of_nonneg_left hpi (show 0 ≤ 4*rho by positivity)
    have hsecond : t*|lap-coordinateLaplacian V x| ≤ ε := by
      exact (mul_le_mul ht.2 hlap (abs_nonneg _) zero_le_one).trans_eq (one_mul _)
    nlinarith
  have hd := denominator_lower hrho0 V hcharge ht x
  rw [component_formula]
  have he := quotient_error (hrho.trans hd) (hrho.trans (le_max_left _ _)) hB hg
    (clamp_error hd hraw)
  exact he.trans_eq (by ring)

end ContinuumCoulomb.MoserVelocityNumerics

end

end OAI
