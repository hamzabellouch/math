import OAI.Geometry.RCD.Coordinates.RegularBochnerSquare
import OAI.Geometry.RCD.Sobolev.HessianActionLocality
import OAI.Geometry.RCD.Sobolev.BochnerDensityQuadratic

namespace OAI

/-! # Directional Hessian domination for actual regular Bochner families -/

open Set Filter MeasureTheory
open scoped NNReal BoundedContinuousFunction

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ) {m : ℕ}

/-- The full product calculus and measure positivity give the sharp
pointwise diagonal-direction Hessian bound, with the same Bochner measure. -/
theorem regularBochner_directional_bound [μ.Regular] [SigmaFinite μ] [SecondCountableTopology X]
    (K : ℝ) (U : Euclidean m →L[ℝ] SobolevSpace μ hQ)
    (D : Euclidean m →L[ℝ] Lp ℝ 2 μ)
    (H : Euclidean m →ₗ[ℝ] Euclidean m →ₗ[ℝ] SobolevSpace μ hQ)
    (L : Euclidean m → ℝ≥0)
    (hU : ∀ a, ∀ᵐ x ∂μ, SobolevSpace.minimalSlope μ hQ (U a) x≤L a)
    (hD : ∀ a, IsWeakLaplacian μ hQ (U a) (D a))
    (hH : ∀ a b, SobolevSpace.toLp μ hQ (H a b) =ᵐ[μ] localGamma μ hQ (U a) (U b))
    (hsym : ∀ a b, H a b=H b a)
    {Ω S : Set X} (hΩ : MeasurableSet Ω) (M : PositiveBilinearMeasure X (Euclidean m))
    (hM : ∀ (a : Euclidean m) (ψ : SobolevSpace μ hQ) (q : X →ᵇ ℝ),
      HasCompactSupport (q : X → ℝ) → tsupport q ⊆ Ω →
      SobolevSpace.toLp μ hQ ψ =ᵐ[μ] q →
      (∫ x, q x ∂M.measure a)=regularBochnerForm μ hQ K U D H q ψ L hU a a)
    (v w z : Euclidean m) (G : X →ᵇ ℝ)
    (hG : SobolevSpace.toLp μ hQ (U w) =ᵐ[μ] G)
    (hz : U z=SobolevSpace.product μ hQ (U w) (U w) ‖G‖₊ ‖G‖₊)
    (dv dw dz : SobolevSpace μ hQ) (A B C : ℝ≥0)
    (hv : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ dv x|≤A)
    (hw : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ dw x|≤B)
    (hzz : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ dz x|≤C)
    (hdv : D v =ᵐ[μ.restrict Ω] SobolevSpace.toLp μ hQ dv)
    (hdw : D w =ᵐ[μ.restrict Ω] SobolevSpace.toLp μ hQ dw)
    (hdz : D z =ᵐ[μ.restrict Ω] SobolevSpace.toLp μ hQ dz)
    (hS : MeasurableSet S) (hsub : S ⊆ Ω)
    (χ : X →ᵇ ℝ) {Cχ : ℝ≥0} (hχ : LipschitzWith Cχ χ)
    (hχc : HasCompactSupport (χ : X → ℝ)) (hχΩ : tsupport χ ⊆ Ω)
    (hχ0 : ∀ x, 0≤χ x) (hχ1 : ∀ x ∈ S, χ x=1) :
    ∀ᵐ x ∂μ.restrict S,
      (localHessianAction μ hQ (U v) (U w) (U w) (H v w) (H v w) (H w w) x)^2 ≤
        bochnerRadonDensity μ M x v v*(localGamma μ hQ (U w) (U w) x)^2 := by
  have h₁ := regularBochner_square_product μ hQ K U D H L hU hD hH hsym hΩ M hM
    v w z G hG hz dv dw A B hv hw hdv hdw hS χ hχ hχc hχΩ hχ0 hχ1
  have h₂ := regularBochner_square_product μ hQ K U D H L hU hD hH hsym hΩ M hM
    w w z G hG hz dw dw B B hw hw hdw hdw hS χ hχ hχc hχΩ hχ0 hχ1
  have h₃ := regularBochner_square_product μ hQ K U D H L hU hD hH hsym hΩ M hM
    z w z G hG hz dz dw C B hzz hw hdz hdw hS χ hχ hχc hχΩ hχ0 hχ1
  have hgb : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ (U w) x|≤‖G‖₊ := by
    filter_upwards [hG] with x hx
    rw [hx]
    exact G.norm_coe_le_norm x
  have hsq := localHessianAction_square_self μ hQ (Ω := Ω) (U w) (H w w) (H z w)
    ‖G‖₊ (L w*L w) hgb (regularGram_abs_le μ hQ U H L hU hH w w)
    (ae_restrict_of_ae (hH w w))
    (by rw [← hz]; exact ae_restrict_of_ae (hH z w))
  rw [← hz] at hsq
  have hsq' : localHessianAction μ hQ (U z) (U w) (U w) (H z w) (H z w) (H w w)
      =ᵐ[μ.restrict S] fun x =>
        2*G x*localHessianAction μ hQ (U w) (U w) (U w) (H w w) (H w w) (H w w) x+
          2*(localGamma μ hQ (U w) (U w) x)^2 := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub hsq,
      ae_restrict_of_ae hG] with x hx hg
    simpa only [hg] using hx
  exact bochner_measure_quadratic_bound μ M v w z G
    (localHessianAction μ hQ (U v) (U w) (U w) (H v w) (H v w) (H w w))
    (localHessianAction μ hQ (U w) (U w) (U w) (H w w) (H w w) (H w w))
    (localHessianAction μ hQ (U z) (U w) (U w) (H z w) (H z w) (H w w))
    (localGamma μ hQ (U w) (U w))
    (localHessianAction_integrable μ hQ _ _ _ _ _ _)
    (localHessianAction_integrable μ hQ _ _ _ _ _ _)
    (localHessianAction_integrable μ hQ _ _ _ _ _ _) hS h₁ h₂ h₃ hsq'

end RegularPointCoordinates

end

end OAI
