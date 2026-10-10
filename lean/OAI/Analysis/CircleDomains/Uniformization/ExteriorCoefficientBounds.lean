import OAI.Analysis.CircleDomains.Modulus.PrincipalNormalization

namespace OAI

/-!
# The published coefficient area theorem and exterior bounds

Ahlfors, *Conformal Invariants* (1973), Theorem 5-1, p. 83, states
that the Laurent coefficients of a normalized exterior univalent map
satisfy the weighted square-sum bound. The proposition below includes
its Laurent expansion, in the zero-constant-term normalization needed
here. It is an explicit published input.

Only a coarse uniform exterior bound is needed for normal-family
compactness. It follows from the coefficient inequality and a geometric
series, with no additional analytic input.
-/

open Set Filter Function Asymptotics Bornology
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

def ExteriorCoefficientAreaTheorem : Prop :=
  ∀ F : ℂ → ℂ, DifferentiableOn ℂ F {z | 1 < ‖z‖} → InjOn F {z | 1 < ‖z‖} →
    (fun z => F z - z) =O[cobounded ℂ] (fun z => z⁻¹) →
    ∃ c : ℕ → ℂ, Summable (fun n : ℕ => ((n : ℝ) + 1) * ‖c n‖ ^ 2) ∧
      (∑' n : ℕ, ((n : ℝ) + 1) * ‖c n‖ ^ 2) ≤ 1 ∧
      ∀ z : ℂ, 1 < ‖z‖ → HasSum (fun n => c n * (z⁻¹) ^ (n + 1)) (F z - z)

theorem norm_coefficient_le_one {c : ℕ → ℂ}
    (hc : Summable (fun n : ℕ => ((n : ℝ) + 1) * ‖c n‖ ^ 2))
    (hbound : (∑' n : ℕ, ((n : ℝ) + 1) * ‖c n‖ ^ 2) ≤ 1) (n : ℕ) : ‖c n‖ ≤ 1 := by
  have hterm : ((n : ℝ) + 1) * ‖c n‖ ^ 2 ≤ 1 :=
    (hc.le_tsum n (fun i _ => mul_nonneg (by positivity) (sq_nonneg _))).trans hbound
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hcross : 0 ≤ (n : ℝ) * ‖c n‖ ^ 2 := mul_nonneg hn (sq_nonneg _)
  nlinarith [norm_nonneg (c n)]

theorem norm_exterior_series_le_one {c : ℕ → ℂ} {z w : ℂ}
    (hc : ∀ n, ‖c n‖ ≤ 1) (hz : 2 ≤ ‖z‖)
    (hw : HasSum (fun n => c n * (z⁻¹) ^ (n + 1)) w) : ‖w‖ ≤ 1 := by
  let r : ℝ := ‖z‖⁻¹
  have hr0 : 0 ≤ r := inv_nonneg.mpr (norm_nonneg z)
  have hrhalf : r ≤ 1 / 2 := by
    dsimp only [r]
    simpa only [one_div] using
      (inv_le_inv₀ (by linarith : 0 < ‖z‖) (by norm_num : (0 : ℝ) < 2)).mpr hz
  have hr1 : r < 1 := by linarith
  have hg : HasSum (fun n : ℕ => r ^ (n + 1)) (r / (1 - r)) := by
    simpa only [pow_succ', div_eq_mul_inv] using (hasSum_geometric_of_lt_one hr0 hr1).mul_left r
  have hle := hw.norm_le_of_bounded hg (fun n => show ‖c n * (z⁻¹) ^ (n + 1)‖ ≤ r ^ (n + 1) from by
    rw [norm_mul, norm_pow, norm_inv]
    exact mul_le_of_le_one_left (pow_nonneg hr0 _) (hc n))
  refine hle.trans ?_
  apply (div_le_one (by linarith : 0 < 1 - r)).mpr
  linarith

theorem ExteriorCoefficientAreaTheorem.exterior_bound
    (harea : ExteriorCoefficientAreaTheorem) {F : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F {z | 1 < ‖z‖}) (hinj : InjOn F {z | 1 < ‖z‖})
    (hnorm : (fun z => F z - z) =O[cobounded ℂ] (fun z => z⁻¹)) :
    ∀ z : ℂ, 2 ≤ ‖z‖ → ‖F z - z‖ ≤ 1 := by
  obtain ⟨c, hc, hbound, hseries⟩ := harea F hF hinj hnorm
  intro z hz
  exact norm_exterior_series_le_one (norm_coefficient_le_one hc hbound) hz
    (hseries z (by linarith))

end CircleDomainRigidity

end

end OAI
