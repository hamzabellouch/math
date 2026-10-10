import OAI.Geometry.RCD.Sobolev.SubsolutionUpperTailBound

namespace OAI

/-! # Arbitrarily small upper gaps from a small quadratic tail -/

open Set Metric Filter MeasureTheory
open scoped NNReal Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.subsolution_upper_tail_gap {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) (hn : 2≤n) (Λ H β : ℝ)
    (hΛ : 0≤Λ) (hH : 0≤H) (hβ : 0<β) :
    ∃ δ : ℝ, 0<δ ∧ ∀ (x : X) (R : ℝ), 0<R → -1≤K*R^2 →
      ∀ (u : SobolevSpace (hausdorff n X) hX.quadratic) (a : ℝ), 0≤a → a*R^2≤Λ →
      IsWeakSubsolutionOn (hausdorff n X) hX.quadratic (ball x R) u a →
      (∫ y in ball x R, (max (SobolevSpace.toLp (hausdorff n X) hX.quadratic u y-H) 0)^2
        ∂hausdorff n X)≤δ*(hausdorff n X).real (ball x R) →
      ∀ᵐ y ∂(hausdorff n X).restrict (ball x (R/2)),
        SobolevSpace.toLp (hausdorff n X) hX.quadratic u y≤H+β := by
  obtain ⟨δ,hδ,hbound⟩ := hX.subsolution_small_upper_tail_bound hn Λ (H/β) hΛ (div_nonneg hH hβ.le)
  refine ⟨β^2*δ,by positivity,?_⟩
  intro x R hR hcurv u a ha haR hu hsmall
  let μ := hausdorff n X
  let v := β⁻¹ • u
  have he : SobolevSpace.toLp μ hX.quadratic v =ᵐ[μ]
      fun y => β⁻¹*SobolevSpace.toLp μ hX.quadratic u y := by
    dsimp only [v]
    rw [map_smul]
    exact Lp.coeFn_smul _ _
  have hmax (z : ℝ) : max (β⁻¹*z-H/β) 0=β⁻¹*max (z-H) 0 := by
    rw [mul_max_of_nonneg _ _ (inv_nonneg.mpr hβ.le),mul_zero]
    congr 1
    field_simp
  have hi : (∫ y in ball x R, (max (SobolevSpace.toLp μ hX.quadratic v y-H/β) 0)^2 ∂μ)=
      (β⁻¹)^2*(∫ y in ball x R, (max (SobolevSpace.toLp μ hX.quadratic u y-H) 0)^2 ∂μ) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae he] with y hy
    rw [hy,hmax,mul_pow]
  have hvsmall : (∫ y in ball x R, (max (SobolevSpace.toLp μ hX.quadratic v y-H/β) 0)^2 ∂μ)≤
      δ*μ.real (ball x R) := by
    rw [hi]
    apply (mul_le_mul_of_nonneg_left hsmall (sq_nonneg (β⁻¹))).trans_eq
    field_simp
    rfl
  have hv := hbound x R hR hcurv v a ha haR
    (hu.smul μ hX.quadratic β⁻¹ (inv_nonneg.mpr hβ.le)) hvsmall
  filter_upwards [hv,ae_restrict_of_ae he] with y hy hey
  rw [hey] at hy
  calc SobolevSpace.toLp μ hX.quadratic u y
      = β*(β⁻¹*SobolevSpace.toLp μ hX.quadratic u y) := by field_simp
    _ ≤ β*(H/β+1) := mul_le_mul_of_nonneg_left hy hβ.le
    _ = H+β := by field_simp

end RegularPointCoordinates

end

end OAI
