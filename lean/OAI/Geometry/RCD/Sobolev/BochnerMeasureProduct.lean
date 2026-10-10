import OAI.Geometry.RCD.Sobolev.BochnerGramSource
import OAI.Geometry.RCD.Harmonic.GramProductMeasure
import OAI.Geometry.RCD.Sobolev.MeasureLaplacianUniqueness

namespace OAI

/-! # The exact local Leibniz identity for the full Bochner measure -/

open Set Filter MeasureTheory
open scoped NNReal BoundedContinuousFunction

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

/-- The full weak product calculation, tested against an arbitrary
continuous compact Sobolev function. The extra term is twice the Hessian
action; all singular Bochner terms remain in the weighted measures. -/
theorem bochner_measure_product_test {Ω : Set X} (hΩ : MeasurableSet Ω) (K : ℝ)
    (f g h df dg dh Fg Fh Gh Fz : SobolevSpace μ hQ)
    (dg₀ dh₀ : Lp ℝ 2 μ) (hdg : IsWeakLaplacian μ hQ g dg₀)
    (hdh : IsWeakLaplacian μ hQ h dh₀)
    (hdg₀ : dg₀ =ᵐ[μ.restrict Ω] SobolevSpace.toLp μ hQ dg)
    (hdh₀ : dh₀ =ᵐ[μ.restrict Ω] SobolevSpace.toLp μ hQ dh)
    (G H : X →ᵇ ℝ) (hG : SobolevSpace.toLp μ hQ g =ᵐ[μ] G)
    (hH : SobolevSpace.toLp μ hQ h =ᵐ[μ] H)
    (A B E F : ℝ≥0)
    (hA : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ Fg x|≤A)
    (hB : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ Fh x|≤B)
    (hE : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ dg x|≤E)
    (hF : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ dh x|≤F)
    (hFg : SobolevSpace.toLp μ hQ Fg =ᵐ[μ.restrict Ω] localGamma μ hQ f g)
    (hFh : SobolevSpace.toLp μ hQ Fh =ᵐ[μ.restrict Ω] localGamma μ hQ f h)
    (hFz : SobolevSpace.toLp μ hQ Fz =ᵐ[μ.restrict Ω]
      localGamma μ hQ f (SobolevSpace.product μ hQ g h ‖G‖₊ ‖H‖₊))
    (Sg Sh Sz : SignedMeasure X)
    (hSg : IsMeasureLaplacianOn μ hQ Ω Fg (bochnerGramSource μ hQ K f g df dg Sg))
    (hSh : IsMeasureLaplacianOn μ hQ Ω Fh (bochnerGramSource μ hQ K f h df dh Sh))
    (hSz : IsMeasureLaplacianOn μ hQ Ω Fz
      (bochnerGramSource μ hQ K f (SobolevSpace.product μ hQ g h ‖G‖₊ ‖H‖₊) df
        (SobolevSpace.product μ hQ g dh ‖G‖₊ F+
          SobolevSpace.product μ hQ h dg ‖H‖₊ E+(2:ℝ) • Gh) Sz))
    (ψ : SobolevSpace μ hQ) (q : X →ᵇ ℝ) (hqc : HasCompactSupport (q : X → ℝ))
    (hqs : tsupport q ⊆ Ω) (hψ : SobolevSpace.toLp μ hQ ψ =ᵐ[μ] q) :
    signedTestIntegral q Sz=signedTestIntegral (q*G) Sh+signedTestIntegral (q*H) Sg+
      2*(∫ x, q x*localHessianAction μ hQ f g h Fg Fh Gh x ∂μ) := by
  let P := SobolevSpace.product μ hQ Fh g B ‖G‖₊+SobolevSpace.product μ hQ Fg h A ‖H‖₊
  obtain ⟨hP,hΔP⟩ := gram_product_measure μ hQ f g h Fg Fh G H hG hH dg₀ dh₀ hdg hdh
    _ _ hSg hSh hFg hFh A B hA hB
  have he := energyForm_eq_of_test_support μ hQ hΩ (hP.trans hFz.symm) q hψ hqs
  have h₁ := hΔP ψ q q.continuous hqc hqs hψ
  have h₂ := hSz ψ q q.continuous hqc hqs hψ
  have hsource : signedTestIntegral q
      (cutoffMeasureSource μ hQ Fh g dg₀ (bochnerGramSource μ hQ K f h df dh Sh) G+
      cutoffMeasureSource μ hQ Fg h dh₀ (bochnerGramSource μ hQ K f g df dg Sg) H) =
      signedTestIntegral q (bochnerGramSource μ hQ K f
        (SobolevSpace.product μ hQ g h ‖G‖₊ ‖H‖₊) df
        (SobolevSpace.product μ hQ g dh ‖G‖₊ F+
          SobolevSpace.product μ hQ h dg ‖H‖₊ E+(2:ℝ) • Gh) Sz) := by
    change _ = (∫ᵛ x, q x ∂<•_)
    change energyForm μ hQ P ψ = _ at h₁
    change energyForm μ hQ Fz ψ = _ at h₂
    change energyForm μ hQ P ψ=energyForm μ hQ Fz ψ at he
    exact neg_inj.mp (h₁.symm.trans (he.trans h₂))
  rw [map_add,integral_cutoffMeasureSource_local μ hQ hΩ Fh g dg₀
      (SobolevSpace.toLp μ hQ dg) _ G q hqs hdg₀,
    integral_cutoffMeasureSource_local μ hQ hΩ Fg h dh₀
      (SobolevSpace.toLp μ hQ dh) _ H q hqs hdh₀,
    ← map_add,integral_gramProductSource μ hQ K f g h df dg dh Fg Fh Sg Sh G H q hG hH,
    integral_bochnerGramSource] at hsource
  have hg : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ g x|≤(‖G‖₊:ℝ) := by
    filter_upwards [hG] with x hx
    simpa only [hx,Real.norm_eq_abs,coe_nnnorm] using G.norm_coe_le_norm x
  have hh : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ h x|≤(‖H‖₊:ℝ) := by
    filter_upwards [hH] with x hx
    simpa only [hx,Real.norm_eq_abs,coe_nnnorm] using H.norm_coe_le_norm x
  have hprod := integral_bochnerProductDensity μ hQ hΩ K f g h df dg dh Fg Fh Gh
    ‖G‖₊ ‖H‖₊ E F hg hh hE hF hFg hFh q hqs
  linarith only [hsource,hprod]

end RegularPointCoordinates

end

end OAI
