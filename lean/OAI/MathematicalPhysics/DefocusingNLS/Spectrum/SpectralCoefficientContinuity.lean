import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralCircularField
import Mathlib.Analysis.Calculus.ContDiff.RCLike

namespace OAI

/-! Local Lipschitz control of the actual odd-power coefficient pair. -/

open Set
open scoped ContDiff
namespace DefocusingNLS
local notation "E₄" => (ℂ × ℂ) × (ℂ × ℂ)

theorem spectralCoefficient_lipschitz (m : ℕ) (M : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ q p : ℂ, ‖q‖ ≤ M → ‖p‖ ≤ M →
      ‖(spectralDiagonalCoefficient m q-spectralDiagonalCoefficient m p,
        spectralCrossCoefficient m q-spectralCrossCoefficient m p)‖ ≤ K*‖q-p‖ := by
  let F := fun q : ℂ => (spectralDiagonalCoefficient m q,spectralCrossCoefficient m q)
  have hF : ContDiff ℝ 1 F := by
    have hi : ContDiff ℝ 1 (fun q : ℂ => q) := contDiff_id
    have hs : ContDiff ℝ 1 (fun q : ℂ => star q) := (starL' ℝ : ℂ ≃L[ℝ] ℂ).contDiff
    exact ((contDiff_const.mul (hi.pow m)).mul (hs.pow m)).prodMk
      ((contDiff_const.mul (hi.pow (m+1))).mul (hs.pow (m-1)))
  obtain ⟨K,hK⟩ := hF.contDiffOn.exists_lipschitzOnWith (by norm_num : (1 : ℕ∞ω)≠0)
    (convex_closedBall (0 : ℂ) M) (isCompact_closedBall (0 : ℂ) M)
  refine ⟨K,K.coe_nonneg,?_⟩
  intro q p hq hp
  exact hK.norm_sub_le (by simpa only [Metric.mem_closedBall,dist_zero_right] using hq)
    (by simpa only [Metric.mem_closedBall,dist_zero_right] using hp)

noncomputable def circularCoefficientAction (A B : ℂ) (z : E₄) : E₄ :=
  ((0,A*z.1.1+B*z.2.1),(0,star A*z.2.1+star B*z.1.1))

theorem circularCoefficientAction_norm (A B : ℂ) (z : E₄) :
    ‖circularCoefficientAction A B z‖ ≤ (‖A‖+‖B‖)*‖z‖ := by
  have h1 : ‖z.1.1‖ ≤ ‖z‖ := (norm_fst_le z.1).trans (norm_fst_le z)
  have h2 : ‖z.2.1‖ ≤ ‖z‖ := (norm_fst_le z.2).trans (norm_snd_le z)
  change max (max ‖(0 : ℂ)‖ ‖A*z.1.1+B*z.2.1‖)
    (max ‖(0 : ℂ)‖ ‖star A*z.2.1+star B*z.1.1‖) ≤ _
  simp only [norm_zero,max_eq_right (norm_nonneg _)]
  apply max_le
  · calc
      _ ≤ ‖A*z.1.1‖+‖B*z.2.1‖ := norm_add_le _ _
      _ = ‖A‖*‖z.1.1‖+‖B‖*‖z.2.1‖ := by simp only [norm_mul]
      _ ≤ ‖A‖*‖z‖+‖B‖*‖z‖ := by gcongr
      _ = _ := by ring
  · calc
      _ ≤ ‖star A*z.2.1‖+‖star B*z.1.1‖ := norm_add_le _ _
      _ = ‖A‖*‖z.2.1‖+‖B‖*‖z.1.1‖ := by simp only [norm_mul,norm_star]
      _ ≤ ‖A‖*‖z‖+‖B‖*‖z‖ := by gcongr
      _ = _ := by ring

theorem circularBoundedField_coefficient_difference (νp νm η : ℂ) (m : ℕ)
    (q p : ℂ) (z : E₄) :
    circularBoundedField νp νm η m q z-circularBoundedField νp νm η m p z=
      circularCoefficientAction
        (spectralDiagonalCoefficient m q-spectralDiagonalCoefficient m p)
        (spectralCrossCoefficient m q-spectralCrossCoefficient m p) z := by
  apply Prod.ext <;> apply Prod.ext <;>
    simp only [circularBoundedField,circularCoefficientAction,Prod.fst_sub,Prod.snd_sub,star_sub]
  all_goals ring

theorem circularBoundedField_coefficient_lipschitz (m : ℕ) (M : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ νp νm η q p : ℂ, ‖q‖ ≤ M → ‖p‖ ≤ M → ∀ z : E₄,
      ‖circularBoundedField νp νm η m q z-circularBoundedField νp νm η m p z‖ ≤
        K*‖q-p‖*‖z‖ := by
  obtain ⟨K,hK,hLip⟩ := spectralCoefficient_lipschitz m M
  refine ⟨2*K,by positivity,?_⟩
  intro νp νm η q p hq hp z
  let A := spectralDiagonalCoefficient m q-spectralDiagonalCoefficient m p
  let B := spectralCrossCoefficient m q-spectralCrossCoefficient m p
  have hAB : ‖(A,B)‖ ≤ K*‖q-p‖ := hLip q p hq hp
  have hA : ‖A‖ ≤ K*‖q-p‖ := (norm_fst_le (A,B)).trans hAB
  have hB : ‖B‖ ≤ K*‖q-p‖ := (norm_snd_le (A,B)).trans hAB
  rw [circularBoundedField_coefficient_difference]
  calc
    _ ≤ (‖A‖+‖B‖)*‖z‖ := circularCoefficientAction_norm A B z
    _ ≤ (2*K*‖q-p‖)*‖z‖ := by gcongr; nlinarith
    _ = _ := by ring

end DefocusingNLS

end OAI
