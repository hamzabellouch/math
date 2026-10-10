import OAI.Geometry.RCD.Coordinates.RegularBochnerSquare
import OAI.Geometry.RCD.Sobolev.HessianSquareCross
import OAI.Geometry.RCD.Sobolev.LocalBochnerDensityProduct
import OAI.Geometry.RCD.Sobolev.BochnerRadonDensity

namespace OAI

/-! # Mixed Bochner densities of actual squared regular directions -/

open Set Filter MeasureTheory
open scoped NNReal BoundedContinuousFunction
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ) {m : ℕ}

theorem regularBochner_square_pair [μ.Regular] [SigmaFinite μ] [SecondCountableTopology X]
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
    (v w zv zw : Euclidean m) (F G : X →ᵇ ℝ)
    (hF : SobolevSpace.toLp μ hQ (U v) =ᵐ[μ] F)
    (hG : SobolevSpace.toLp μ hQ (U w) =ᵐ[μ] G)
    (hzv : U zv=SobolevSpace.product μ hQ (U v) (U v) ‖F‖₊ ‖F‖₊)
    (hzw : U zw=SobolevSpace.product μ hQ (U w) (U w) ‖G‖₊ ‖G‖₊)
    (dzv dw : SobolevSpace μ hQ) (A B : ℝ≥0)
    (hdzv : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ dzv x|≤A)
    (hdw : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ dw x|≤B)
    (hDzv : D zv =ᵐ[μ.restrict Ω] SobolevSpace.toLp μ hQ dzv)
    (hDw : D w =ᵐ[μ.restrict Ω] SobolevSpace.toLp μ hQ dw)
    (hS : MeasurableSet S) (hsub : S⊆Ω)
    (χ : X →ᵇ ℝ) {Cχ : ℝ≥0} (hχ : LipschitzWith Cχ χ)
    (hχc : HasCompactSupport (χ : X → ℝ)) (hχΩ : tsupport χ⊆Ω)
    (hχ0 : ∀ x, 0≤χ x) (hχ1 : ∀ x∈S, χ x=1) :
    ∀ᵐ x ∂μ.restrict S, bochnerRadonDensity μ M x zv zw=
      2*G x*bochnerRadonDensity μ M x zv w+
      4*F x*localHessianAction μ hQ (U v) (U w) (U w) (H v w) (H v w) (H w w) x+
      4*(localGamma μ hQ (U v) (U w) x)^2 := by
  have hp := regularBochner_square_product μ hQ K U D H L hU hD hH hsym hΩ M hM
    zv w zw G hG hzw dzv dw A B hdzv hdw hDzv hDw hS χ hχ hχc hχΩ hχ0 hχ1
  have hd := signed_rnDeriv_local_product μ (M.bilinear zv w) (M.bilinear zv w)
    (M.bilinear zv zw) G G
    (localHessianAction_integrable μ hQ _ _ _ _ _ _) hS hp
  have hfb : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ (U v) x|≤‖F‖₊ := by
    filter_upwards [hF] with x hx
    rw [hx]
    exact F.norm_coe_le_norm x
  have hh := localHessianAction_square_cross μ hQ (Ω := Ω) (U v) (U w) (H v w) (H w w)
    (H zv w) ‖F‖₊ (L v*L w) hfb (regularGram_abs_le μ hQ U H L hU hH v w)
    (ae_restrict_of_ae (hH v w)) (by rw [← hzv]; exact ae_restrict_of_ae (hH zv w))
  rw [← hzv] at hh
  filter_upwards [hd,ae_restrict_of_ae_restrict_of_subset hsub hh,ae_restrict_of_ae hF,
    ae_restrict_of_ae (bochnerRadonDensity_rep μ M zv zw),
    ae_restrict_of_ae (bochnerRadonDensity_rep μ M zv w)] with x hd hh hf hzz hzw
  rw [hzz,hzw] at hd
  rw [hh,hf] at hd
  linarith only [hd]

end RegularPointCoordinates

end

end OAI
