import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.CutoffProfileTailBound
import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingCoefficientCompactness

namespace OAI

/-! # Compact approximation of the actual expanding cutoff profile -/

open Filter Topology
open scoped SchwartzMap ContDiff

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

theorem cutoffProfile_compactApproximation (a k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k)
    (χ : 𝓢(E, ℂ)) (hχ : HasCompactSupport (χ : E → ℂ))
    (hχzero : ∀ y : E, 1 ≤ ‖y‖ → χ y = 0)
    (hχone : ∀ y : E, ‖y‖ ≤ 1 / 2 → χ y = 1)
    (Q : E → ℂ) (hQ : ContDiff ℝ ∞ Q)
    (hsymbol : ∀ N : ℕ, ∃ D : ℝ, 0 ≤ D ∧ ∀ n ≤ N, ∀ y : E, y ≠ 0 →
      ‖iteratedFDeriv ℝ n Q y‖ ≤ D * ‖y‖ ^ (-2 * a - (n : ℝ)))
    (L : ℕ → ℝ) (hL : ∀ n, 1 ≤ L n) (hLinf : Tendsto L atTop atTop) :
    ExpandingCompactApproximation a k ha1 hk L hL (fun n =>
      schwartzTorusSample a k (L n) ha1 hk (hL n) (radianFourierKernel
        (cutoffProfileSchwartz (L n) (by linarith [hL n]) χ hχ Q hQ))) := by
  obtain ⟨N, C, hC, hc⟩ := exists_cutoffProfile_tail_bound a k ha ha1 hk χ hχ hχzero hχone
  obtain ⟨D, hD, hd⟩ := hsymbol N
  have hr0 : 0 ≤ (2 ^ (-a) : ℝ) := by positivity
  have hr1 : (2 ^ (-a) : ℝ) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have ht : Tendsto (fun J : ℕ => C * D * (2 ^ (-a) : ℝ) ^ J) atTop (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1).const_mul (C * D)
  intro δ hδ
  obtain ⟨J, hJ⟩ := (ht.eventually (gt_mem_nhds hδ)).exists
  refine ⟨(2 : ℝ) ^ J,
    cutoffProfileSchwartz ((2 : ℝ) ^ J) (by positivity)
      homogeneousCoreCutoff homogeneousCoreCutoff_hasCompactSupport Q hQ, ?_, ?_⟩
  · intro y hy
    exact cutoffProfile_core_zero _ _ Q hQ y hy.le
  · filter_upwards [hLinf.eventually (eventually_ge_atTop (2 * (2 : ℝ) ^ J))] with n hn
    exact (hc Q hQ D hD hd J (L n) (hL n) hn).trans_lt hJ

end DefocusingNLS

end OAI
