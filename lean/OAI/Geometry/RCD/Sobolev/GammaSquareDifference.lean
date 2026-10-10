import OAI.Geometry.RCD.Sobolev.GammaL2Bound

namespace OAI

/-! # Stability of energy densities under bounded-gradient approximation -/

open Set Filter MeasureTheory
open scoped NNReal ENNReal

namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

theorem localGamma_self_sub_bound (f g : SobolevSpace μ hQ) (L M : ℝ≥0)
    (hf : ∀ᵐ x ∂μ, SobolevSpace.minimalSlope μ hQ f x ≤ L)
    (hg : ∀ᵐ x ∂μ, SobolevSpace.minimalSlope μ hQ g x ≤ M) :
    ∀ᵐ x ∂μ, |localGamma μ hQ f f x - localGamma μ hQ g g x| ≤
      ((L : ℝ) + M) * SobolevSpace.minimalSlope μ hQ (f - g) x := by
  filter_upwards [hf, hg, localGamma_sub_left μ hQ f g f,
    localGamma_sub_left μ hQ f g g, localGamma_comm μ hQ f g,
    localGamma_abs_le μ hQ (f - g) f, localGamma_abs_le μ hQ (f - g) g,
    (Lp.coeFn_nonneg _).mpr (SobolevSpace.minimalSlope_nonneg μ hQ (f - g))]
    with x hf' hg' hdf hdg hcomm hbf hbg h0
  have heq : localGamma μ hQ f f x - localGamma μ hQ g g x =
      localGamma μ hQ (f - g) f x + localGamma μ hQ (f - g) g x := by
    rw [hdf, hdg, hcomm]
    ring
  rw [heq]
  calc
    _ ≤ |localGamma μ hQ (f - g) f x| + |localGamma μ hQ (f - g) g x| := abs_add_le _ _
    _ ≤ SobolevSpace.minimalSlope μ hQ (f - g) x * (L : ℝ) +
        SobolevSpace.minimalSlope μ hQ (f - g) x * (M : ℝ) :=
      add_le_add (hbf.trans (mul_le_mul_of_nonneg_left hf' h0))
        (hbg.trans (mul_le_mul_of_nonneg_left hg' h0))
    _ = _ := by ring

end RegularPointCoordinates

end OAI
