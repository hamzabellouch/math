import OAI.Geometry.RCD.Sobolev.WeakBochnerSquare
import OAI.Geometry.RCD.Coordinates.RegularBochnerSquare

namespace OAI

/-! # The full finite-family square identity with L² sources

The exact weak product calculation avoids local Sobolev assumptions on
the Laplacians of the two original directions.
-/

open Set Filter MeasureTheory
open scoped NNReal BoundedContinuousFunction

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ) {m : ℕ}

/-- The square product identity for the actual full bilinear measure.
Only the genuine L² Laplacian and Sobolev Gram representatives occur. -/
theorem regularBochner_square_product_weak [μ.Regular] [SecondCountableTopology X]
    (K : ℝ) (U : Euclidean m →L[ℝ] SobolevSpace μ hQ)
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
    (a w z : Euclidean m) (G : X →ᵇ ℝ)
    (hG : SobolevSpace.toLp μ hQ (U w) =ᵐ[μ] G)
    (hz : U z=SobolevSpace.product μ hQ (U w) (U w) ‖G‖₊ ‖G‖₊)
    (hS : MeasurableSet S) (χ : X →ᵇ ℝ) {Cχ : ℝ≥0} (hχ : LipschitzWith Cχ χ)
    (hχc : HasCompactSupport (χ : X → ℝ)) (hχΩ : tsupport χ ⊆ Ω)
    (hχ0 : ∀ x, 0≤χ x) (hχ1 : ∀ x∈S, χ x=1) :
    (M.bilinear a z).restrict S=
      (signedSourceWeight (M.bilinear a w) G+signedSourceWeight (M.bilinear a w) G+
        (2:ℝ) • μ.withDensityᵥ
          (localHessianAction μ hQ (U a) (U w) (U w) (H a w) (H a w) (H w w))).restrict S := by
  have hgb : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ (U w) x|≤‖G‖₊ := by
    filter_upwards [hG] with x hx
    rw [hx]
    exact G.norm_coe_le_norm x
  have hF := regularGram_abs_le μ hQ U H L hU hH a w
  have hGG := regularGram_abs_le μ hQ U H L hU hH w w
  have hgrad : ∀ᵐ x ∂μ, localGamma μ hQ (U w) (U w) x≤(L w:ℝ)^2 := by
    filter_upwards [localGamma_self μ hQ (U w),hU w,
      (Lp.coeFn_nonneg _).mpr (SobolevSpace.minimalSlope_nonneg μ hQ (U w))] with x he hb h0
    rw [he]
    exact pow_le_pow_left₀ h0 hb 2
  obtain ⟨qz,hqz,hqzr⟩ := (hD w).product μ hQ (U w) (U w) (D w) (D w) (hD w)
    ‖G‖₊ ‖G‖₊ (L w) hgb hgb hgrad
  have hDz : D z=qz := IsWeakLaplacian.unique μ hQ (by simpa only [hz] using hD z) hqz
  have hDzr : D z =ᵐ[μ] fun x => 2*SobolevSpace.toLp μ hQ (U w) x*D w x+
      2*SobolevSpace.toLp μ hQ (H w w) x := by
    rw [hDz]
    filter_upwards [hqzr,hH w w] with x hx hh
    rw [hx,hh]
    ring
  have hFz : H a z=(2:ℝ) • SobolevSpace.product μ hQ (U w) (H a w) ‖G‖₊ (L a*L w) := by
    apply Subtype.ext
    apply Lp.ext
    change SobolevSpace.toLp μ hQ (H a z) =ᵐ[μ]
      SobolevSpace.toLp μ hQ ((2:ℝ) • SobolevSpace.product μ hQ (U w) (H a w) ‖G‖₊ (L a*L w))
    have hp := SobolevSpace.product_coe μ hQ (U w) (H a w) ‖G‖₊ (L a*L w) hgb hF
    have hg := localGamma_product_right μ hQ (U a) (U w) (U w) ‖G‖₊ ‖G‖₊ hgb hgb
    filter_upwards [hH a z,hH a w,hp,hg,
      Lp.coeFn_smul (2:ℝ) (SobolevSpace.toLp μ hQ (SobolevSpace.product μ hQ (U w) (H a w) ‖G‖₊ (L a*L w)))]
      with x haz haw hp hg hs
    simp only [map_smul]
    rw [hs]
    simp only [Pi.smul_apply,smul_eq_mul]
    rw [haz,hp,haw,hz,hg]
    ring
  apply signedMeasure_eq_restrict_of_tests _ _ hS χ hχ hχc hχΩ hχ0 hχ1
  intro q
  obtain ⟨Aq,hq,hqc,hqΩ⟩ := q.property
  let ψ := compactTestSobolev μ hQ Ω q
  have hψ : SobolevSpace.toLp μ hQ ψ =ᵐ[μ] (q : X →ᵇ ℝ) := compactTestSobolev_coe μ hQ Ω q
  have hψb : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ ψ x|≤‖(q:X →ᵇ ℝ)‖₊ := by
    filter_upwards [hψ] with x hx
    rw [hx]
    exact (q:X →ᵇ ℝ).norm_coe_le_norm x
  let ψg := SobolevSpace.product μ hQ ψ (U w) ‖(q:X →ᵇ ℝ)‖₊ ‖G‖₊
  have hψg : SobolevSpace.toLp μ hQ ψg =ᵐ[μ] (q:X →ᵇ ℝ)*G := by
    filter_upwards [SobolevSpace.product_coe μ hQ ψ (U w) ‖(q:X →ᵇ ℝ)‖₊ ‖G‖₊ hψb hgb,hψ,hG]
      with x hp hq hg
    change SobolevSpace.toLp μ hQ ψg x=_ at hp
    simp only [hp,hq,hg,Pi.mul_apply]
  have hprodcompact : HasCompactSupport ((q:X →ᵇ ℝ)*G : X → ℝ) := hqc.mul_right
  have hprodΩ : tsupport ((q:X →ᵇ ℝ)*G) ⊆ Ω := tsupport_mul_subset_left.trans hqΩ
  have htest₁ := M.polarized_test (q:X →ᵇ ℝ) (regularBochnerForm μ hQ K U D H q ψ L hU)
    (regularBochnerForm_symmetric μ hQ K U D H q ψ L hU hsym)
    (fun v => hM v ψ q hqc hqΩ hψ) a z
  have htest₂ := M.polarized_test ((q:X →ᵇ ℝ)*G)
    (regularBochnerForm μ hQ K U D H ((q:X →ᵇ ℝ)*G) ψg L hU)
    (regularBochnerForm_symmetric μ hQ K U D H _ ψg L hU hsym)
    (fun v => hM v ψg _ hprodcompact hprodΩ hψg) a w
  have hcalc := mixedBochnerTest_square μ hQ K (U a) (U w) (H a w) (H w w) ψ
    (D a) (D w) (D z) (hD a) (hD w) ‖G‖₊ (L a*L w) (L w*L w) (L a) (L w)
    hgb hF hGG (hU a) (hU w) (hH a w) (hH w w) G q hG hψ hDzr
  change mixedBochnerTest μ hQ K (U a) _ (D a) (D z) _ q ψ=
    2*mixedBochnerTest μ hQ K (U a) (U w) (D a) (D w) (H a w) _ ψg+_ at hcalc
  rw [← hz,← hFz] at hcalc
  change signedTestIntegral (q:X →ᵇ ℝ) (M.bilinear a z)=
    mixedBochnerTest μ hQ K (U a) (U z) (D a) (D z) (H a z) q ψ at htest₁
  change signedTestIntegral ((q:X →ᵇ ℝ)*G) (M.bilinear a w)=
    mixedBochnerTest μ hQ K (U a) (U w) (D a) (D w) (H a w) _ ψg at htest₂
  rw [map_add,map_add,map_smul]
  change _=(∫ᵛ x, (q:X →ᵇ ℝ) x ∂<•signedSourceWeight (M.bilinear a w) G)+
    (∫ᵛ x, (q:X →ᵇ ℝ) x ∂<•signedSourceWeight (M.bilinear a w) G)+
      2*(∫ᵛ x, (q:X →ᵇ ℝ) x ∂<•μ.withDensityᵥ _)
  simp only [integral_signedSourceWeight]
  rw [integral_signedDensity μ (localHessianAction_integrable μ hQ _ _ _ _ _ _)]
  change signedTestIntegral (q:X →ᵇ ℝ) (M.bilinear a z)=
    signedTestIntegral ((q:X →ᵇ ℝ)*G) (M.bilinear a w)+
      signedTestIntegral ((q:X →ᵇ ℝ)*G) (M.bilinear a w)+_
  rw [htest₁,htest₂]
  linarith only [hcalc]

end RegularPointCoordinates

end

end OAI
