import OAI.NumberTheory.CubicMoment.Decomposition.StoppedCoefficients
import OAI.NumberTheory.CubicMoment.Estimates.PrimeDetectorCutoff

namespace OAI

/-! Pointwise bounds for the actual stopped coefficients, before any
analytic sequence estimate. The divisor count is literal and introduces
no dependence on the number or width of prime bins. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma cutoffMoebius_norm_le_one {ψ : ℝ → ℝ}
    (hψ : ∀ x, 0 ≤ ψ x ∧ ψ x ≤ 1) (w : ℝ) (d : Eisenstein) :
    ‖cutoffMoebius ψ w d‖ ≤ 1 := by
  rw [cutoffMoebius,norm_mul,norm_prod]
  have hp : (∏ p ∈ primaryPrimeFactors d, ‖(ψ (norm p/w):ℂ)‖) ≤ 1 := by
    apply Finset.prod_le_one₀ (fun _ _ => _root_.norm_nonneg _)
    intro p hp
    simpa only [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hψ _).1] using (hψ (norm p/w)).2
  exact (mul_le_mul (norm_idealMoebius_le_one d) hp
    (Finset.prod_nonneg (fun _ _ => _root_.norm_nonneg _)) zero_le_one).trans_eq (one_mul 1)

lemma primeDetectorCutoff_moebius_norm (w : ℝ) (d : Eisenstein) :
    ‖cutoffMoebius primeDetectorCutoff w d‖ ≤ 1 :=
  cutoffMoebius_norm_le_one (fun x => ⟨primeDetectorCutoff_nonneg x,
    primeDetectorCutoff_le_one x⟩) w d

theorem stoppedAlpha_divisor_bound (E U : Finset Eisenstein)
    (hE : ∀ e ∈ E, primary e) {ψ : ℝ → ℝ}
    (hψ : ∀ x, 0 ≤ ψ x ∧ ψ x ≤ 1) (w : ℝ)
    (remaining : Eisenstein → Prop) (a : Eisenstein) :
    ‖stoppedAlpha E U ψ w remaining a‖ ≤ ((E.filter (fun e => e ∣ a)).card:ℝ) := by
  apply (primaryPairCoefficient_norm_le E U hE a _ zero_le_one _).trans_eq (mul_one _)
  intro p hp
  by_cases he : remaining p.1
  · simpa only [ite_eq_left he] using cutoffMoebius_norm_le_one hψ w p.1
  · simp only [ite_eq_right he,norm_zero,zero_le_one]

theorem stoppedBeta_divisor_bound (R D : Finset Eisenstein)
    (hR : ∀ r ∈ R, primary r) {ψ : ℝ → ℝ}
    (hψ : ∀ x, 0 ≤ ψ x ∧ ψ x ≤ 1) (w : ℝ)
    (selected : Eisenstein → Eisenstein → Prop) (v : Eisenstein → ℂ)
    {M : ℝ} (hM : 0 ≤ M) (hv : ∀ r ∈ R, ‖v r‖ ≤ M) (b : Eisenstein) :
    ‖stoppedBeta R D v ψ w selected b‖ ≤ ((R.filter (fun r => r ∣ b)).card:ℝ)*M := by
  apply primaryPairCoefficient_norm_le R D hR b _ hM
  intro p hp
  by_cases hs : selected p.1 p.2
  · simp only [ite_eq_left hs,norm_mul]
    exact (mul_le_mul_of_nonneg_left (cutoffMoebius_norm_le_one hψ w p.2)
      (_root_.norm_nonneg _)).trans ((mul_one _).le.trans
        (hv p.1 (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).1))
  · simpa only [ite_eq_right hs,norm_zero] using hM

/-- An independently supported side can be restricted to squarefree
elements without adding any cross-side coprimality predicate. -/
theorem stopped_coefficients_squarefree_sides (R D E U : Finset Eisenstein)
    (v : Eisenstein → ℂ) (ψ : ℝ → ℝ) (w : ℝ)
    (selected : Eisenstein → Eisenstein → Prop) (remaining : Eisenstein → Prop)
    (K : Eisenstein → ℂ) (hK : ∀ n, ¬Squarefree n → K n = 0) :
    (∑ a ∈ (primaryPairSupport E U).filter Squarefree,
      ∑ b ∈ (primaryPairSupport R D).filter Squarefree,
        stoppedAlpha E U ψ w remaining a*stoppedBeta R D v ψ w selected b*K (a*b)) =
    ∑ a ∈ primaryPairSupport E U, ∑ b ∈ primaryPairSupport R D,
      stoppedAlpha E U ψ w remaining a*stoppedBeta R D v ψ w selected b*K (a*b) := by
  simp only [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro a ha
  by_cases hsa : Squarefree a
  · simp only [ite_eq_left hsa]
    apply Finset.sum_congr rfl
    intro b hb
    by_cases hsb : Squarefree b
    · simp only [ite_eq_left hsb]
    · have hab : ¬Squarefree (a*b) := fun h => hsb (fun x hx => h x (hx.trans (dvd_mul_left b a)))
      simp [hsb,hK _ hab]
  · have hz : ∀ b, K (a*b) = 0 := fun b => hK _
      (fun h => hsa (fun x hx => h x (hx.trans (dvd_mul_right a b))))
    simp [hsa,hz]

end CubicFirstMoment

end

end OAI
