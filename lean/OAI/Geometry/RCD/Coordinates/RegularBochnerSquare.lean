import OAI.Geometry.RCD.Coordinates.RegularSquareLaplacian
import OAI.Geometry.RCD.Coordinates.RegularBochnerMeasureLaplacian
import OAI.Geometry.RCD.Sobolev.BochnerMeasureProductLocal

namespace OAI

/-! # The full Bochner square identity for a regular finite family -/

open Set Filter MeasureTheory
open scoped NNReal BoundedContinuousFunction

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ) {m : ℕ}

theorem regularGram_abs_le
    (U : Euclidean m →L[ℝ] SobolevSpace μ hQ)
    (H : Euclidean m →ₗ[ℝ] Euclidean m →ₗ[ℝ] SobolevSpace μ hQ)
    (L : Euclidean m → ℝ≥0)
    (hU : ∀ a, ∀ᵐ x ∂μ, SobolevSpace.minimalSlope μ hQ (U a) x≤L a)
    (hH : ∀ a b, SobolevSpace.toLp μ hQ (H a b) =ᵐ[μ] localGamma μ hQ (U a) (U b))
    (a b : Euclidean m) :
    ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ (H a b) x|≤L a*L b := by
  filter_upwards [hH a b,localGamma_abs_le μ hQ (U a) (U b),hU a,hU b,
    (Lp.coeFn_nonneg _).mpr (SobolevSpace.minimalSlope_nonneg μ hQ (U b))]
    with x hh hab ha hb h0
  rw [hh]
  exact hab.trans (mul_le_mul ha hb h0 (L a).coe_nonneg)

/-- Squaring one member of the regular family produces the actual full
measure product identity. Only local Sobolev representatives of the two
original Laplacians are needed. -/
theorem regularBochner_square_product [μ.Regular] [SecondCountableTopology X]
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
    (a w z : Euclidean m) (G : X →ᵇ ℝ)
    (hG : SobolevSpace.toLp μ hQ (U w) =ᵐ[μ] G)
    (hz : U z=SobolevSpace.product μ hQ (U w) (U w) ‖G‖₊ ‖G‖₊)
    (da dw : SobolevSpace μ hQ) (A B : ℝ≥0)
    (ha : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ da x|≤A)
    (hw : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ dw x|≤B)
    (hda : D a =ᵐ[μ.restrict Ω] SobolevSpace.toLp μ hQ da)
    (hdw : D w =ᵐ[μ.restrict Ω] SobolevSpace.toLp μ hQ dw)
    (hS : MeasurableSet S) (χ : X →ᵇ ℝ) {Cχ : ℝ≥0} (hχ : LipschitzWith Cχ χ)
    (hχc : HasCompactSupport (χ : X → ℝ)) (hχΩ : tsupport χ ⊆ Ω)
    (hχ0 : ∀ x, 0≤χ x) (hχ1 : ∀ x ∈ S, χ x=1) :
    (M.bilinear a z).restrict S =
      (signedSourceWeight (M.bilinear a w) G+signedSourceWeight (M.bilinear a w) G+
        (2:ℝ) • μ.withDensityᵥ
          (localHessianAction μ hQ (U a) (U w) (U w) (H a w) (H a w) (H w w))).restrict S := by
  have hgb : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ (U w) x|≤‖G‖₊ := by
    filter_upwards [hG] with x hx
    rw [hx]
    exact G.norm_coe_le_norm x
  have hL : ∀ᵐ x ∂μ, localGamma μ hQ (U w) (U w) x≤(L w:ℝ)^2 := by
    filter_upwards [localGamma_self μ hQ (U w),hU w,
      (Lp.coeFn_nonneg _).mpr (SobolevSpace.minimalSlope_nonneg μ hQ (U w))] with x he hb h0
    rw [he]
    exact pow_le_pow_left₀ h0 hb 2
  let dz := SobolevSpace.product μ hQ (U w) dw ‖G‖₊ B+
    SobolevSpace.product μ hQ (U w) dw ‖G‖₊ B+(2:ℝ) • H w w
  obtain ⟨q,hq,hqr⟩ := (hD w).square_local μ hQ (U w) (H w w) dw (D w)
    ‖G‖₊ B (L w) hgb hw hL (ae_restrict_of_ae (hH w w)) hdw
  have hqz : D z=q := IsWeakLaplacian.unique μ hQ (by simpa only [hz] using hD z) hq
  have hdz : D z =ᵐ[μ.restrict Ω] SobolevSpace.toLp μ hQ dz := by rw [hqz]; exact hqr
  have hdzb := squareLaplacianSource_bound μ hQ (U w) (H w w) dw ‖G‖₊ B
    (L w*L w) hgb hw (regularGram_abs_le μ hQ U H L hU hH w w)
  let E : ℝ≥0 := 2*‖G‖₊*B+2*(L w*L w)
  have hE : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ dz x|≤E := by
    simpa only [E,NNReal.coe_add,NNReal.coe_mul,NNReal.coe_ofNat] using hdzb
  have hsg := regularBochner_measure_laplacian μ hQ K U D H L hU hsym hΩ M hM
    a w da dw (hH a w) (hD a) (hD w) hda hdw A B ha hw
  have hsz := regularBochner_measure_laplacian μ hQ K U D H L hU hsym hΩ M hM
    a z da dz (hH a z) (hD a) (hD z) hda hdz A E ha hE
  apply bochner_measure_product μ hQ hΩ K (U a) (U w) (U w) da dw dw
    (H a w) (H a w) (H w w) (H a z) (D w) (D w) (hD w) (hD w)
    hdw hdw G G hG hG (L a*L w) (L a*L w) B B
    (regularGram_abs_le μ hQ U H L hU hH a w)
    (regularGram_abs_le μ hQ U H L hU hH a w) hw hw
    (ae_restrict_of_ae (hH a w)) (ae_restrict_of_ae (hH a w))
    (by rw [← hz]; exact ae_restrict_of_ae (hH a z))
    (M.bilinear a w) (M.bilinear a w) (M.bilinear a z)
    hsg hsg
    (by rw [hz] at hsz; exact hsz)
    hS χ hχ hχc hχΩ hχ0 hχ1

end RegularPointCoordinates

end

end OAI
