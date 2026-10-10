import OAI.NumberTheory.CubicMoment.Estimates.SemiprimeGaussTailWindows
import OAI.NumberTheory.CubicMoment.Estimates.SemiprimePolynomialBounds

namespace OAI

/-! Exact angular coefficient transfer for the original semiprime Gauss
window. The twist preserves the actual prime support and coefficient energy. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma productGaussWindow_angular_coefficients (P S : Finset Eisenstein)
    (α β : Eisenstein → ℂ) (ℓ : ℤ) (W : ℝ → ℂ) (H U X : ℝ) :
    productGaussWindow P S (fun a => theta ℓ a*α a) (fun b => theta ℓ b*β b)
      0 W H U X = productGaussWindow P S α β ℓ W H U X := by
  unfold productGaussWindow
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  simp only [productGaussHeightWindowKernel,theta_zero,theta_mul]
  ring

def semiprimeAngularCoefficient (ℓ : ℤ) (X : ℝ) (i : ℕ) (p : Eisenstein) : ℂ :=
  theta ℓ p*semiprimePartitionCoefficient X i p

lemma semiprimeAngularCoefficient_energy (ℓ : ℤ) {X : ℝ} (hX : 0 < X) (i : ℕ) :
    (∑ p ∈ semiprimeFullSupport X i, ‖semiprimeAngularCoefficient ℓ X i p‖^2) ≤
      36*semiprimePartitionScale i := by
  calc
    _ ≤ ∑ _p ∈ semiprimeFullSupport X i, (1:ℝ) := by
      apply Finset.sum_le_sum
      intro p hp
      have hn : p ≠ 0 := primary_ne_zero (semiprimeFullSupport_bounds hX i hp).1
      rw [semiprimeAngularCoefficient,norm_theta_mul hn]
      exact (pow_le_pow_left₀ (_root_.norm_nonneg _) (semiprimeSmoothWeight_norm _ _) 2).trans_eq
        (by norm_num)
    _ = ((semiprimeFullSupport X i).card:ℝ) := by simp
    _ ≤ _ := semiprimeFullSupport_card hX i

lemma semiprimeGaussTailPiece_angular_window (ℓ : ℤ) (H U : ℝ)
    {X : ℝ} (hX : 0 < X) (i j : ℕ) :
    semiprimeGaussTailPiece ℓ H U X i j =
      productGaussWindow (semiprimeFullSupport X i) (semiprimeFullSupport X j)
        (semiprimeAngularCoefficient ℓ X i) (semiprimeAngularCoefficient ℓ X j)
        0 primeProductEnvelope H U X := by
  rw [semiprimeGaussTailPiece_window ℓ H U hX i j]
  symm
  exact productGaussWindow_angular_coefficients _ _ _ _ _ _ _ _ _

end CubicFirstMoment

end

end OAI
