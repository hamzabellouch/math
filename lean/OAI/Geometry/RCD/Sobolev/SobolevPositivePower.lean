import OAI.Geometry.RCD.Sobolev.WeakLaplacianWeightedProduct

namespace OAI

/-! # Positive integer powers of bounded Sobolev functions

Only positive powers are constructed, so no integrable constant function
is required when the ambient measure is infinite.
-/

open Set Filter MeasureTheory
open scoped NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) (Q : QuadraticCheegerEnergy μ)

theorem exists_sobolev_positive_power (u : SobolevSpace μ Q) (A : ℝ≥0)
    (hu : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ Q u x| ≤ A) (n : ℕ) :
    ∃ v : SobolevSpace μ Q,
      (SobolevSpace.toLp μ Q v =ᵐ[μ] fun x => (SobolevSpace.toLp μ Q u x)^(n+1)) ∧
      (∀ᵐ x ∂μ, |SobolevSpace.toLp μ Q v x| ≤ A^(n+1)) ∧
      ∀ w : SobolevSpace μ Q, localGamma μ Q v w =ᵐ[μ]
        fun x => (n+1:ℝ)*(SobolevSpace.toLp μ Q u x)^n*localGamma μ Q u w x := by
  induction n with
  | zero =>
      refine ⟨u,?_,?_,?_⟩
      · simp only [zero_add,pow_one]; exact EventuallyEq.rfl
      · simpa only [zero_add,pow_one] using hu
      · intro w
        simp only [Nat.cast_zero,zero_add,pow_zero,one_mul]
        exact EventuallyEq.rfl
  | succ n ih =>
      obtain ⟨v,hv,hvb,hvg⟩ := ih
      let z := SobolevSpace.product μ Q u v A (A^(n+1))
      have hz := SobolevSpace.product_coe μ Q u v A (A^(n+1)) hu hvb
      have hval : SobolevSpace.toLp μ Q z =ᵐ[μ]
          fun x => (SobolevSpace.toLp μ Q u x)^(n+1+1) := by
        filter_upwards [hz,hv] with x hx hy
        rw [hx,hy,pow_succ]
        ring
      refine ⟨z,hval,?_,?_⟩
      · filter_upwards [hval,hu] with x hx hy
        rw [hx,abs_pow]
        exact pow_le_pow_left₀ (abs_nonneg _) hy _
      · intro w
        filter_upwards [localGamma_product_left μ Q u v w A (A^(n+1)) hu hvb,hvg w,hv]
          with x hx hy hzv
        change localGamma μ Q (SobolevSpace.product μ Q u v A (A^(n+1))) w x = _
        rw [hx,hy,hzv]
        simp only [Nat.cast_add,Nat.cast_one,pow_succ]
        ring

end RegularPointCoordinates

end

end OAI
