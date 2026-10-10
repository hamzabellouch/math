import OAI.NumberTheory.CubicMoment.Estimates.CubeSchwartz
import OAI.NumberTheory.CubicMoment.Estimates.SchwartzLattice

namespace OAI

/-! The integral main term of the principal cube lattice. -/

noncomputable section
open scoped BigOperators SchwartzMap ContDiff
open MeasureTheory
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

/-- The normalized planar integral; the measure of an Eisenstein
fundamental parallelogram is one. -/
def cubeProfileIntegral (W : ℝ → ℂ) : ℂ :=
  (2/Real.sqrt 3:ℝ) • ∫ z : ℂ, normProfileFourier W (z^3)

lemma cubeProfileIntegral_eq (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hW' : ContDiff ℝ ∞ W) :
    cubeProfileIntegral W = (2/Real.sqrt 3:ℝ) • ∫ z : ℂ, cubeProfileSchwartz W hW hW' z := by
  unfold cubeProfileIntegral
  congr 1
  apply integral_congr_ae
  filter_upwards with z
  change normProfileFourier W (z^3) = normProfileFourierSchwartz W hW hW' (z^3)
  exact (normProfileFourierSchwartz_apply W hW hW' _).symm

/-- The nonzero cube lattice has its integral main term with a bounded
error for `q ≤ 1`. This is stronger than the radius-size error needed in
the low-height dispersion application. -/
theorem radial_cube_lattice_asymptotic (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (hW' : ContDiff ℝ ∞ W) :
    ∃ C : ℝ, 0 < C ∧ ∀ q : ℝ, 0 < q → q ≤ 1 →
      ‖(∑' j : Eisenstein, if j = 0 then (0:ℂ) else
          radialDualProfile W (q^3*(norm j)^3)) -
        (q⁻¹:ℝ) • cubeProfileIntegral W‖ ≤ C := by
  let F := cubeProfileSchwartz W hW hW'
  obtain ⟨D,hD,hbound⟩ := schwartz_lattice_approximation F
  refine ⟨D+‖F 0‖+1,by positivity,?_⟩
  intro q hq hq1
  let s := Real.sqrt q
  have hs : 0 < s := Real.sqrt_pos.mpr hq
  have hs2 : s^2 = q := Real.sq_sqrt hq.le
  have hsC : (s:ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  have hh := hbound s hs
  rw [hs2] at hh
  have hF (j : Eisenstein) : F ((s:ℂ)*(j:ℂ)) =
      radialDualProfile W (q^3*(norm j)^3) := by
    dsimp only [F]
    rw [cubeProfileSchwartz_scaled_apply,hs2]
  have hsum := (schwartz_summable_eisenstein_coset F (s:ℂ) hsC 0).tsum_eq_add_tsum_ite 0
  simp only [zero_add,Eisenstein.coe_zero,mul_zero] at hsum
  have hmain : (2/(Real.sqrt 3*q):ℝ) • (∫ z : ℂ, F z) =
      (q⁻¹:ℝ) • cubeProfileIntegral W := by
    rw [cubeProfileIntegral_eq W hW hW',smul_smul]
    congr 1
    ring
  rw [hmain,hsum] at hh
  have hnonzero : (∑' j : Eisenstein, if j = 0 then (0:ℂ) else F ((s:ℂ)*(j:ℂ))) =
      ∑' j : Eisenstein, if j = 0 then 0 else radialDualProfile W (q^3*(norm j)^3) := by
    simp_rw [hF]
  rw [hnonzero] at hh
  let S := ∑' j : Eisenstein, if j = 0 then (0:ℂ) else radialDualProfile W (q^3*(norm j)^3)
  change ‖S-(q⁻¹:ℝ) • cubeProfileIntegral W‖ ≤ _
  calc
    _ = ‖(F 0+S-(q⁻¹:ℝ) • cubeProfileIntegral W)-F 0‖ := by congr 1; ring
    _ ≤ ‖F 0+S-(q⁻¹:ℝ) • cubeProfileIntegral W‖+‖F 0‖ := norm_sub_le _ _
    _ ≤ D*q+‖F 0‖ := add_le_add hh le_rfl
    _ ≤ D+‖F 0‖+1 := by nlinarith

end CubicFirstMoment

end

end OAI
