import OAI.Geometry.RCD.Sobolev.BoundedLpSquare

namespace OAI

/-! # Bounded compact Lipschitz approximation in L² -/

open Set Filter MeasureTheory
open scoped NNReal ENNReal Topology

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

/-- Clip the compact recovery sequence to preserve the amplitude of the
original bounded Sobolev function. L² convergence suffices after heat flow. -/
theorem SobolevSpace.bounded_compact_L2_approximation (f : SobolevSpace μ hQ)
    (C : ℝ≥0) (hf : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ f x| ≤ C) (p : X) :
    ∃ (us : ℕ → Lp ℝ 2 μ) (gs : ℕ → X → ℝ),
      Tendsto us atTop (𝓝 (SobolevSpace.toLp μ hQ f)) ∧
      (∀ i, ∃ L : ℝ≥0, LipschitzWith L (gs i)) ∧
      (∀ i, HasCompactSupport (gs i)) ∧
      (∀ i, us i =ᵐ[μ] gs i) ∧ (∀ i x, |gs i x| ≤ C) := by
  obtain ⟨vs,ks,Gs,hl,hs,he,_hG,hv,_hGs⟩ :=
    (SobolevSpace.minimalSlope_isRelaxed μ hQ f).compact_recovery μ p
  let P : Lp ℝ 2 μ → Lp ℝ 2 μ := (clipReal_lipschitz C).compLp (clipReal_zero C)
  have hPf : P (SobolevSpace.toLp μ hQ f) = SobolevSpace.toLp μ hQ f := by
    apply Lp.ext
    filter_upwards [(clipReal_lipschitz C).coeFn_compLp (clipReal_zero C)
      (SobolevSpace.toLp μ hQ f),hf] with x hx hfx
    exact hx.trans (clipReal_eq_self C hfx)
  refine ⟨fun i => P (vs i),fun i x => clipReal C (ks i x),?_,?_,?_,?_,?_⟩
  · have hPc : Continuous P := (clipReal_lipschitz C).continuous_compLp (clipReal_zero C)
    simpa only [hPf,Function.comp_apply] using! (hPc.tendsto (SobolevSpace.toLp μ hQ f)).comp hv
  · intro i
    obtain ⟨L,hL⟩ := hl i
    exact ⟨1*L,(clipReal_lipschitz C).comp hL⟩
  · intro i
    exact (hs i).comp_left (clipReal_zero C)
  · intro i
    filter_upwards [(clipReal_lipschitz C).coeFn_compLp (clipReal_zero C) (vs i),he i] with x hx he
    exact hx.trans (congrArg (clipReal C) he)
  · intro i x
    exact clipReal_abs_le C (ks i x)

end RegularPointCoordinates

end

end OAI
