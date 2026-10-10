import OAI.MeasureTheory.Falconer.Estimates.FarCellCount
import OAI.MeasureTheory.Falconer.Shells.PositiveSpatialKernel

namespace OAI

/-! # Positive far kernels over the actual comparable cell pairs

The maximum ranges over the original tested distance laws.  The number
of summands is bounded by two free cell labels, not four.
-/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
attribute [local instance] Classical.propDecidable

noncomputable def farCollisionMaximum {d : ℕ}
    (w₀ : Sphere d) (Q : DyadicCube d) (ρ : Measure (Space d))
    (m : ℝ → ℝ) (A : ℕ → ℝ) (N : ℕ) (σ : ℝ) (J i q b t : ℕ)
    (X Y : List (Fin d → Bool)) (n : ℕ) : ℝ≥0∞ :=
  ((farCellPartners (Q.descendant X) ρ n) ×ˢ
    (farCellPartners (Q.descendant Y) ρ n)).sup fun z =>
      max (positiveCollisionCount w₀ Q ρ m A N σ J i q b t (X++z.1.1) (X++z.1.2))
        (positiveCollisionCount w₀ Q ρ m A N σ J i q b t (Y++z.2.1) (Y++z.2.2))

theorem far_positive_kernel_sum_le {d : ℕ}
    (w₀ : Sphere d) (Q : DyadicCube d) (ρ : Measure (Space d)) [IsFiniteMeasure ρ]
    (m : ℝ → ℝ) (A : ℕ → ℝ) (N : ℕ) (σ : ℝ) (J i q b t : ℕ)
    (X Y : List (Fin d → Bool)) (n : ℕ)
    (S : (List (Fin d → Bool) × List (Fin d → Bool)) →
      (List (Fin d → Bool) × List (Fin d → Bool)) →
        Set ((Space d × Space d) × (Space d × Space d))) :
    (∑ z ∈ (farCellPartners (Q.descendant X) ρ n) ×ˢ
        (farCellPartners (Q.descendant Y) ρ n),
      ENNReal.ofReal ((2:ℝ)^(t-b)*((2:ℝ)^N)^(4*m b)) *
        (∫⁻ v in S z.1 z.2,
          ENNReal.ofReal (1/(1+(2:ℝ)^t*|dist v.1.1 v.1.2-dist v.2.1 v.2.2|)^2)
          ∂(testedCellPair ρ ρ (Q.descendant (X++z.1.1)) (Q.descendant (X++z.1.2))
            (policyTestPairs w₀ Q ρ m A N σ J i q b t)).prod
            (testedCellPair ρ ρ (Q.descendant (Y++z.2.1)) (Q.descendant (Y++z.2.2))
              (policyTestPairs w₀ Q ρ m A N σ J i q b t)))) ≤
      (((farCellPartners (Q.descendant X) ρ n) ×ˢ
        (farCellPartners (Q.descendant Y) ρ n)).card : ℝ≥0∞) *
        PlanarFalconer.binKernelConstant *
        farCollisionMaximum w₀ Q ρ m A N σ J i q b t X Y n := by
  let T := (farCellPartners (Q.descendant X) ρ n) ×ˢ
    (farCellPartners (Q.descendant Y) ρ n)
  calc
    _ ≤ ∑ _z ∈ T, PlanarFalconer.binKernelConstant *
        farCollisionMaximum w₀ Q ρ m A N σ J i q b t X Y n := by
      apply Finset.sum_le_sum
      intro z hz
      exact (positiveCollision_spatial_kernel_max w₀ Q ρ m A N σ J i q b t
        (X++z.1.1) (X++z.1.2) (Y++z.2.1) (Y++z.2.2) (S z.1 z.2)).trans
        (mul_le_mul' le_rfl (Finset.le_sup (s := T) (f := fun z =>
          max (positiveCollisionCount w₀ Q ρ m A N σ J i q b t (X++z.1.1) (X++z.1.2))
            (positiveCollisionCount w₀ Q ρ m A N σ J i q b t (Y++z.2.1) (Y++z.2.2))) hz))
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul, mul_assoc, T]

theorem farCellPartners_regular_card {d : ℕ} {Q : DyadicCube d}
    {ρ : Measure (Space d)} {N : ℕ} {s lam : ℝ} {m : ℝ → ℝ}
    (h : Regularization.RegularizedProfileData Q ρ N s lam m) (hQ : 0 < Q.side)
    {a b : ℕ} (hab : a ≤ b) (hb : b ≤ N)
    (X Y : List (Fin d → Bool)) (hX : X.length = a) (hY : Y.length = a) :
    (((farCellPartners (Q.descendant X) ρ (b-a)) ×ˢ
      (farCellPartners (Q.descendant Y) ρ (b-a))).card : ℝ) ≤
      ((2*(1100*(d+1))+1)^(2*d):ℕ) *
        ((2:ℝ)^N)^(2*(m ((b:ℝ)/N)-m ((a:ℝ)/N))+4*((d:ℝ)+1)*lam) := by
  have hc := farCellPartners_pair_card (Q.descendant X) (Q.descendant Y)
    (Q.descendant_side_pos hQ X) (Q.descendant_side_pos hQ Y) ρ ρ (b-a)
  have hc' : (((farCellPartners (Q.descendant X) ρ (b-a)) ×ˢ
      (farCellPartners (Q.descendant Y) ρ (b-a))).card : ℝ) ≤
      (((2*(1100*(d+1))+1)^(2*d):ℕ):ℝ) *
        (((Q.descendant X).occupiedPaths ρ (b-a) ×ˢ
          (Q.descendant Y).occupiedPaths ρ (b-a)).card : ℝ) := by exact_mod_cast hc
  exact hc'.trans (mul_le_mul_of_nonneg_left (h.pair_count hab hb X Y hX hY)
    (Nat.cast_nonneg _))

end Falconer

end OAI
