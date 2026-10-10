import OAI.MeasureTheory.Falconer.Shells.PositiveKernel

namespace OAI

/-! # The collision kernel on the original four-point measures

An additional far-cell or comparable-band restriction can be dropped
after the kernel has become nonnegative. The endpoint tests remain in
the two original pair measures throughout this comparison.
-/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal

theorem testedCellDistance_lintegral {d : ℕ}
    (ρ : Measure (Space d)) [IsFiniteMeasure ρ]
    (P Q P' Q' : DyadicCube d) (G H : Set (Space d × Space d))
    (F : ℝ × ℝ → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ z, F z ∂(testedCellDistance ρ ρ P Q G).prod (testedCellDistance ρ ρ P' Q' H)) =
    ∫⁻ z, F (dist z.1.1 z.1.2,dist z.2.1 z.2.2)
      ∂(testedCellPair ρ ρ P Q G).prod (testedCellPair ρ ρ P' Q' H) := by
  rw [testedCellDistance,testedCellDistance,
    Measure.map_prod_map _ _ (by fun_prop) (by fun_prop),lintegral_map hF (by fun_prop)]
  rfl

theorem positiveCollision_spatial_kernel_max {d : ℕ}
    (w₀ : Sphere d) (Q : DyadicCube d) (ρ : Measure (Space d)) [IsFiniteMeasure ρ]
    (m : ℝ → ℝ) (A : ℕ → ℝ) (N : ℕ) (σ : ℝ) (J i q a t : ℕ)
    (X Y X' Y' : List (Fin d → Bool))
    (S : Set ((Space d × Space d) × (Space d × Space d))) :
    ENNReal.ofReal ((2:ℝ)^(t-a)*((2:ℝ)^N)^(4*m a)) *
      (∫⁻ z in S, ENNReal.ofReal (1/(1+(2:ℝ)^t*|dist z.1.1 z.1.2-dist z.2.1 z.2.2|)^2)
        ∂(testedCellPair ρ ρ (Q.descendant X) (Q.descendant Y)
          (policyTestPairs w₀ Q ρ m A N σ J i q a t)).prod
        (testedCellPair ρ ρ (Q.descendant X') (Q.descendant Y')
          (policyTestPairs w₀ Q ρ m A N σ J i q a t))) ≤
      PlanarFalconer.binKernelConstant *
        max (positiveCollisionCount w₀ Q ρ m A N σ J i q a t X Y)
          (positiveCollisionCount w₀ Q ρ m A N σ J i q a t X' Y') := by
  have h := positiveCollision_kernel_max w₀ Q ρ m A N σ J i q a t X Y X' Y'
  rw [testedCellDistance_lintegral ρ _ _ _ _ _ _ _ (by fun_prop)] at h
  apply le_trans _ h
  exact mul_le_mul' le_rfl (lintegral_mono' Measure.restrict_le_self (fun _ => le_rfl))

end Falconer

end OAI
