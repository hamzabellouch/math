import OAI.Analysis.CircleDomains.Rigidity.CircleFluxStability
import OAI.Analysis.CircleDomains.Selection.PrincipalExteriorGerm

namespace OAI

/-! Derivatives of the actual analytic remainder on large circles.
The bounds will make its contribution to signed area tend to zero. -/
open Set Filter Function MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 def principalCircleRemainder (R : ℝ) (T : ℂ → ℂ) (t : ℝ) : ℂ :=
    (unitCircleParam 0 R t)⁻¹^2 * T (unitCircleParam 0 R t)⁻¹

 theorem principalCircleRemainder_hasDerivAt {R : ℝ} (hR : 0 < R)
    {T : ℂ → ℂ} (t : ℝ) (hT : DifferentiableAt ℂ T (unitCircleParam 0 R t)⁻¹) :
    HasDerivAt (principalCircleRemainder R T)
      (2*(unitCircleParam 0 R t)⁻¹ *
          (-(deriv (unitCircleParam 0 R) t)/(unitCircleParam 0 R t)^2) *
          T (unitCircleParam 0 R t)⁻¹ +
        (unitCircleParam 0 R t)⁻¹^2 * (deriv T (unitCircleParam 0 R t)⁻¹ *
          (-(deriv (unitCircleParam 0 R) t)/(unitCircleParam 0 R t)^2))) t := by
  have hn : unitCircleParam 0 R t ≠ 0 := by
    have hh : ‖unitCircleParam 0 R t‖ = R := by
      simp only [unitCircleParam, norm_circleMap_zero, abs_of_pos hR]
    intro he
    rw [he, norm_zero] at hh
    linarith
  have hd : HasDerivAt (unitCircleParam 0 R) (deriv (unitCircleParam 0 R) t) t :=
    (unitCircleParam_hasDerivAt R t).differentiableAt.hasDerivAt
  have hi := hd.inv hn
  have ht := hT.hasDerivAt.comp t hi
  convert (hi.pow 2).mul ht using 1
  · funext s
    rfl
  · norm_num


 theorem principalCircleRemainder_deriv_bound {R B C : ℝ} (hR : 1 ≤ R)
    (_hB : 0 ≤ B) (hC : 0 ≤ C) {T : ℂ → ℂ} (t : ℝ)
    (hT : DifferentiableAt ℂ T (unitCircleParam 0 R t)⁻¹)
    (hb : ‖T (unitCircleParam 0 R t)⁻¹‖ ≤ B)
    (hc : ‖deriv T (unitCircleParam 0 R t)⁻¹‖ ≤ C) :
    ‖deriv (principalCircleRemainder R T) t‖ ≤ 2*Real.pi*(2*B+C)/R^2 := by
  have hRp : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hn : ‖unitCircleParam 0 R t‖ = R := by
    simp only [unitCircleParam, norm_circleMap_zero, abs_of_pos hRp]
  have hi : ‖(unitCircleParam 0 R t)⁻¹‖ = R⁻¹ := by rw [norm_inv, hn]
  have hd : ‖-(deriv (unitCircleParam 0 R) t)/(unitCircleParam 0 R t)^2‖ = 2*Real.pi/R := by
    rw [norm_div, norm_neg, unitCircleParam_deriv_norm hRp.le, norm_pow, hn]
    field_simp
  rw [(principalCircleRemainder_hasDerivAt hRp t hT).deriv]
  calc
    _ ≤ ‖2*(unitCircleParam 0 R t)⁻¹ *
          (-(deriv (unitCircleParam 0 R) t)/(unitCircleParam 0 R t)^2) *
          T (unitCircleParam 0 R t)⁻¹‖ +
        ‖(unitCircleParam 0 R t)⁻¹^2 * (deriv T (unitCircleParam 0 R t)⁻¹ *
          (-(deriv (unitCircleParam 0 R) t)/(unitCircleParam 0 R t)^2))‖ := norm_add_le _ _
    _ = 2*R⁻¹*(2*Real.pi/R)*‖T (unitCircleParam 0 R t)⁻¹‖ +
        R⁻¹^2*(‖deriv T (unitCircleParam 0 R t)⁻¹‖*(2*Real.pi/R)) := by
      simp only [norm_mul, Complex.norm_ofNat, hi, hd, norm_pow]
    _ ≤ 2*R⁻¹*(2*Real.pi/R)*B + R⁻¹^2*(C*(2*Real.pi/R)) := by gcongr
    _ = 2*Real.pi*(2*B*R⁻¹^2+C*R⁻¹^3) := by field_simp
    _ ≤ 2*Real.pi*(2*B*R⁻¹^2+C*R⁻¹^2) := by
      have hri : R⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hR
      have hh : R⁻¹^3 ≤ R⁻¹^2 := by
        calc
          _ = R⁻¹^2*R⁻¹ := by ring
          _ ≤ R⁻¹^2*1 := mul_le_mul_of_nonneg_left hri (sq_nonneg _)
          _ = _ := mul_one _
      gcongr
    _ = _ := by field_simp

end CircleDomainRigidity

end

end OAI
