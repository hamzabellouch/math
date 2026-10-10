import OAI.Analysis.IrrationalRotation.Rotation.WeightedOrbitInvariance

namespace OAI

noncomputable section
namespace Invariant233.ConvolutionAbsoluteBound
open WeightedShift

theorem shifted_norm_products (ξ γ : Hilbert) (n : ℤ) :
    (Summable (fun v : ℤ => ‖ξ v‖ * ‖γ (v + n)‖)) ∧
      (∑' v : ℤ, ‖ξ v‖ * ‖γ (v + n)‖) ≤ ‖ξ‖ * ‖γ‖ := by
  have h := lp.tsum_mul_le_mul_norm (p := 2) (q := 2)
    (by rw [Real.holderConjugate_iff]; norm_num) ξ (shift (-n) γ)
  simpa only [shift_apply, sub_neg_eq_add, LinearIsometryEquiv.norm_map] using h

theorem weighted_shifted_products (a : ℤ → ℂ) (ha : ∀ v, ‖a v‖ ≤ 1)
    (ξ γ : Hilbert) (n : ℤ) :
    (Summable (fun v : ℤ => ‖a v * ξ v * star (γ (v + n))‖)) ∧
      (∑' v : ℤ, ‖a v * ξ v * star (γ (v + n))‖) ≤ ‖ξ‖ * ‖γ‖ := by
  have hCS := shifted_norm_products ξ γ n
  have hb (v : ℤ) : ‖a v * ξ v * star (γ (v + n))‖ ≤
      ‖ξ v‖ * ‖γ (v + n)‖ := by
    rw [norm_mul, norm_mul, norm_star]
    calc
      ‖a v‖ * ‖ξ v‖ * ‖γ (v + n)‖ ≤ 1 * ‖ξ v‖ * ‖γ (v + n)‖ :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (ha v) (norm_nonneg _)) (norm_nonneg _)
      _ = ‖ξ v‖ * ‖γ (v + n)‖ := by ring
  have hs := Summable.of_nonneg_of_le (fun v => norm_nonneg _) hb hCS.1
  exact ⟨hs, (hs.tsum_le_tsum hb hCS.1).trans hCS.2⟩

theorem coefficient_sequences (Fx Fy : ℤ → ℝ) (ξ γ : Hilbert) (n : ℤ)
    (hratio : ∀ v : ℤ, ‖(Fy (v + n) : ℂ) / (Fx v : ℂ)‖ ≤ 1) :
    let A : ℤ → ℂ := fun v => ξ v / (Fx v : ℂ)
    let B : ℤ → ℂ := fun v => (Fy (-v) : ℂ) * star (γ (-v))
    (Summable (fun v : ℤ => ‖A v * B (-n - v)‖)) ∧
      (∑' v : ℤ, ‖A v * B (-n - v)‖) ≤ ‖ξ‖ * ‖γ‖ := by
  dsimp only
  have heq (v : ℤ) : ξ v / (Fx v : ℂ) *
      ((Fy (-(-n - v)) : ℂ) * star (γ (-(-n - v)))) =
      ((Fy (v + n) : ℂ) / (Fx v : ℂ)) * ξ v * star (γ (v + n)) := by
    have hi : -(-n - v) = v + n := by omega
    rw [hi]
    simp only [div_eq_mul_inv]
    ring
  simp_rw [heq]
  exact weighted_shifted_products _ hratio ξ γ n

theorem coefficient_sequences_le_one (Fx Fy : ℤ → ℝ) (ξ γ : Hilbert) (n : ℤ)
    (hratio : ∀ v : ℤ, ‖(Fy (v + n) : ℂ) / (Fx v : ℂ)‖ ≤ 1)
    (hξ : ‖ξ‖ ≤ 1) (hγ : ‖γ‖ ≤ 1) :
    let A : ℤ → ℂ := fun v => ξ v / (Fx v : ℂ)
    let B : ℤ → ℂ := fun v => (Fy (-v) : ℂ) * star (γ (-v))
    (Summable (fun v : ℤ => ‖A v * B (-n - v)‖)) ∧
      (∑' v : ℤ, ‖A v * B (-n - v)‖) ≤ 1 := by
  have h := coefficient_sequences Fx Fy ξ γ n hratio
  refine ⟨h.1, h.2.trans ?_⟩
  simpa only [one_mul] using mul_le_mul hξ hγ (norm_nonneg γ) zero_le_one

end Invariant233.ConvolutionAbsoluteBound

end

end OAI
