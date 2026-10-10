import OAI.Geometry.RCD.Coordinates.RegularBochnerWeakSquare
import OAI.Geometry.RCD.Sobolev.HessianActionLocality
import OAI.Geometry.RCD.Sobolev.BochnerDensityShiftedQuadratic
import OAI.Geometry.RCD.Coordinates.LaplacianCoordinateForm

namespace OAI

/-! # Shifted directional domination for the actual weak regular algebra -/

open Set Filter MeasureTheory
open scoped NNReal BoundedContinuousFunction

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ) {m : ℕ}

/-- The full product calculus and measure positivity give the sharp
pointwise diagonal-direction Hessian bound, with the same Bochner measure. -/
theorem regularBochner_shifted_directional_bound_weak [μ.Regular] [SigmaFinite μ] [SecondCountableTopology X]
    (K N b : ℝ) (hN : 0<N) (U : Euclidean m →L[ℝ] SobolevSpace μ hQ)
    (D : Euclidean m →L[ℝ] Lp ℝ 2 μ)
    (H : Euclidean m →ₗ[ℝ] Euclidean m →ₗ[ℝ] SobolevSpace μ hQ)
    (L : Euclidean m → ℝ≥0)
    (hU : ∀ a, ∀ᵐ x ∂μ, SobolevSpace.minimalSlope μ hQ (U a) x≤L a)
    (hD : ∀ a, IsWeakLaplacian μ hQ (U a) (D a))
    (hH : ∀ a b, SobolevSpace.toLp μ hQ (H a b) =ᵐ[μ] localGamma μ hQ (U a) (U b))
    (hsym : ∀ a b, H a b=H b a)
    {Ω S : Set X} (M : PositiveBilinearMeasure X (Euclidean m))
    (hM : ∀ (a : Euclidean m) (ψ : SobolevSpace μ hQ) (q : X →ᵇ ℝ),
      HasCompactSupport (q : X → ℝ) → tsupport q ⊆ Ω →
      SobolevSpace.toLp μ hQ ψ =ᵐ[μ] q →
      (∫ x, q x ∂M.measure a)=regularBochnerForm μ hQ K U D H q ψ L hU a a)
    (v w z : Euclidean m) (G : X →ᵇ ℝ)
    (hG : SobolevSpace.toLp μ hQ (U w) =ᵐ[μ] G)
    (hz : U z=SobolevSpace.product μ hQ (U w) (U w) ‖G‖₊ ‖G‖₊)
    (hS : MeasurableSet S) (hsub : S ⊆ Ω)
    (χ : X →ᵇ ℝ) {Cχ : ℝ≥0} (hχ : LipschitzWith Cχ χ)
    (hχc : HasCompactSupport (χ : X → ℝ)) (hχΩ : tsupport χ ⊆ Ω)
    (hχ0 : ∀ x, 0≤χ x) (hχ1 : ∀ x ∈ S, χ x=1)
    (hBE : ∀ a, ∀ᵐ x ∂μ.restrict S,
      (laplacianCoordinateForm μ D x a)^2≤N*bochnerRadonDensity μ M x a a) :
    ∀ᵐ x ∂μ.restrict S,
      (localHessianAction μ hQ (U v) (U w) (U w) (H v w) (H v w) (H w w) x-
        b*localGamma μ hQ (U w) (U w) x)^2 ≤
        (bochnerRadonDensity μ M x v v-2*b*laplacianCoordinateForm μ D x v+N*b^2)*
          (localGamma μ hQ (U w) (U w) x)^2 := by
  have h₁ := regularBochner_square_product_weak μ hQ K U D H L hU hD hH hsym M hM
    v w z G hG hz hS χ hχ hχc hχΩ hχ0 hχ1
  have h₂ := regularBochner_square_product_weak μ hQ K U D H L hU hD hH hsym M hM
    w w z G hG hz hS χ hχ hχc hχΩ hχ0 hχ1
  have h₃ := regularBochner_square_product_weak μ hQ K U D H L hU hD hH hsym M hM
    z w z G hG hz hS χ hχ hχc hχΩ hχ0 hχ1
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
  have hgrad : ∀ᵐ x ∂μ, localGamma μ hQ (U w) (U w) x≤(L w:ℝ)^2 := by
    filter_upwards [localGamma_self μ hQ (U w),hU w,
      (Lp.coeFn_nonneg _).mpr (SobolevSpace.minimalSlope_nonneg μ hQ (U w))] with x he hb h0
    rw [he]
    exact pow_le_pow_left₀ h0 hb 2
  have hsource := laplacianCoordinateForm_square μ hQ U D hD w z ‖G‖₊ (L w) hgb hgrad hz
  have hdelta : ∀ᵐ x ∂μ.restrict S,
      laplacianCoordinateForm μ D x z=2*G x*laplacianCoordinateForm μ D x w+
        2*localGamma μ hQ (U w) (U w) x := by
    filter_upwards [ae_restrict_of_ae hsource,ae_restrict_of_ae hG] with x hs hg
    rwa [hg] at hs
  exact bochner_measure_shifted_quadratic_bound μ M v w z G
    (localHessianAction μ hQ (U v) (U w) (U w) (H v w) (H v w) (H w w))
    (localHessianAction μ hQ (U w) (U w) (U w) (H w w) (H w w) (H w w))
    (localHessianAction μ hQ (U z) (U w) (U w) (H z w) (H z w) (H w w))
    (localGamma μ hQ (U w) (U w)) (laplacianCoordinateForm μ D) N b hN
    (localHessianAction_integrable μ hQ _ _ _ _ _ _)
    (localHessianAction_integrable μ hQ _ _ _ _ _ _)
    (localHessianAction_integrable μ hQ _ _ _ _ _ _) hS h₁ h₂ h₃ hsq' hdelta hBE

end RegularPointCoordinates

end

end OAI
