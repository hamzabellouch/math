import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.CutoffProfileTailAssembly
import Mathlib.Algebra.Order.Field.GeomSum

namespace OAI

/-! # Geometric decay of the actual sampled profile tail -/

open scoped SchwartzMap ContDiff

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

theorem exists_cutoffProfile_tail_bound (a k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k)
    (χ : 𝓢(E, ℂ)) (hχ : HasCompactSupport (χ : E → ℂ))
    (hχzero : ∀ y : E, 1 ≤ ‖y‖ → χ y = 0)
    (hχone : ∀ y : E, ‖y‖ ≤ 1 / 2 → χ y = 1) :
    ∃ (N : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ (Q : E → ℂ) (hQ : ContDiff ℝ ∞ Q)
      (D : ℝ), 0 ≤ D →
      (∀ n ≤ N, ∀ y : E, y ≠ 0 →
        ‖iteratedFDeriv ℝ n Q y‖ ≤ D * ‖y‖ ^ (-2 * a - (n : ℝ))) →
      ∀ (J : ℕ) (L : ℝ) (hL : 1 ≤ L), 2 * (2 : ℝ) ^ J ≤ L →
        ‖schwartzTorusSample a k L ha1 hk hL (radianFourierKernel
            (cutoffProfileSchwartz L (by linarith) χ hχ Q hQ)) -
          schwartzTorusSample a k L ha1 hk hL (radianFourierKernel
            (cutoffProfileSchwartz ((2 : ℝ) ^ J) (by positivity)
              homogeneousCoreCutoff homogeneousCoreCutoff_hasCompactSupport Q hQ))‖ ≤
          C * D * (2 ^ (-a) : ℝ) ^ J := by
  obtain ⟨N, C, hC, hc⟩ := exists_cutoffAnnulus_uniform_bound a k ha ha1 hk χ hχzero
  let r : ℝ := 2 ^ (-a)
  have hr0 : 0 ≤ r := by dsimp [r]; positivity
  have hr1 : r < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hden : 0 < 1 - r := sub_pos.mpr hr1
  refine ⟨N, C / (1 - r), div_nonneg hC hden.le, ?_⟩
  intro Q hQ D hD hsymbol J L hL hJL
  obtain ⟨M₀, hM₀⟩ := pow_unbounded_of_one_lt (2 * L) (by norm_num : (1 : ℝ) < 2)
  let M := max J M₀
  have hJM : J ≤ M := le_max_left _ _
  have hM : 2 * L ≤ (2 : ℝ) ^ M := hM₀.le.trans
    (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (le_max_right J M₀))
  let P := physicalSchwartzTorusSamplingLinear a k L ha1 hk hL
  let ψ := fun j => schwartzPhysicalDilation a ((2 : ℝ) ^ j) (by positivity)
    (cutoffProfileAnnulus a ((2 : ℝ) ^ j) L χ homogeneousAnnulusCutoff
      homogeneousAnnulusCutoff_hasCompactSupport Q hQ)
  have hb (j : ℕ) : ‖P (ψ j)‖ ≤ (C * D) * r ^ j := by
    have h := hc Q hQ D hD hsymbol L ((2 : ℝ) ^ j) hL (one_le_pow₀ (by norm_num))
    have he : ((2 : ℝ) ^ j) ^ (-a) = r ^ j :=
      (Real.rpow_pow_comm (by norm_num : (0 : ℝ) ≤ 2) _ _).symm
    simpa only [P, ψ, physicalSchwartzTorusSamplingLinear_apply, he] using h
  change ‖P _ - P _‖ ≤ _
  rw [← map_sub, cutoffProfileSchwartz_tail_assembly a L (by linarith) χ hχ hχzero hχone Q hQ J M hJM hJL hM,
    map_sum]
  calc
    _ ≤ ∑ j ∈ Finset.Ico J M, ‖P (ψ j)‖ := norm_sum_le _ _
    _ ≤ ∑ j ∈ Finset.Ico J M, (C * D) * r ^ j := Finset.sum_le_sum (fun j _ => hb j)
    _ = (C * D) * ∑ j ∈ Finset.Ico J M, r ^ j := (Finset.mul_sum _ _ _).symm
    _ ≤ (C * D) * (r ^ J / (1 - r)) :=
      mul_le_mul_of_nonneg_left (geom_sum_Ico_le_of_lt_one hr0 hr1) (mul_nonneg hC hD)
    _ = C / (1 - r) * D * (2 ^ (-a) : ℝ) ^ J := by dsimp [r]; ring

end DefocusingNLS

end OAI
