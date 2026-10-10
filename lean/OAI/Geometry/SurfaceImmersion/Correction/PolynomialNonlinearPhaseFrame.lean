import OAI.Geometry.SurfaceImmersion.Atlas.PhaseChartJetTransfer
import OAI.Geometry.SurfaceImmersion.Atlas.NonlinearPhaseFrameMargins

namespace OAI

/-! Polynomial reconstruction bounds for nonlinear first-coordinate phase
charts, including the cross-chart quadratic phases. -/
noncomputable section
open Set
open scoped ContDiff
namespace ClosedSurfaceR4.RealModes
open SmallModes PhaseGeometry WeightedEstimates

theorem polynomial_nonlinear_phase_frame_bound (m : ℕ) :
    ∃ d : ℕ, ∃ A : ℝ, 1 ≤ A ∧
    ∀ (F : RField 4) (φ : Base → ℝ) (e : OpenPartialHomeomorph Base Base),
      ContDiff ℝ ∞ F → ContDiff ℝ ∞ φ → ContDiff ℝ ∞ e → ContDiff ℝ ∞ e.symm →
      (∀ x, (e x).1 = φ x) →
    ∀ s B : ℝ, 0 < s → s ≤ 1 → 1 ≤ B →
      (∀ j ≤ m+2, WeightedBound e.source 1 j (B/s^(j-2)) F) →
      (∀ j, 1 ≤ j → j ≤ m+2 → ∀ x ∈ e.source,
        ‖iteratedFDerivWithin ℝ j e e.source x‖ ≤ B) →
      (∀ x ∈ e.source, ‖(coordDet (fderiv ℝ e x))⁻¹‖ ≤ B) →
      (∀ x ∈ e.source, |coordDet (fderiv ℝ e x)| ≤ B) →
      (∀ x ∈ e.source, Function.Injective (fderiv ℝ F x)) →
      (∀ x ∈ e.source, Good (realSecondTensor F x) (phaseDerivative φ x)) →
      (∀ x ∈ e.source,
        ‖(NormalFrame.gramDet (coordDeriv dx F x) (coordDeriv dy F x))⁻¹‖ ≤ B) →
      (∀ x ∈ e.source, ‖secondQuadratic (realSecondTensor F x)
        (-(phaseDerivative φ x).2,(phaseDerivative φ x).1)‖⁻¹ ≤ B) →
      ReconstructionCoefficientBound (fun x => complexify ((F ∘ e.symm) x))
        e.target s m (A*B^d) ∧
      WeightedBound e.target s m (A*B^d) (freeNormal (F ∘ e.symm)) := by
  obtain ⟨d₀,A₀,hA₀,hjet⟩ := polynomial_inverse_chart_twoJet_bound m
  obtain ⟨q,C,hC,hframe⟩ := polynomial_frame_envelope m
  let S : ℝ → ℝ := fun B => 1+A₀*B^d₀+B^3+B^6
  have hp : HasPolynomialBound S := by
    dsimp [S]
    repeat first
      | exact polynomialBound_id
      | apply HasPolynomialBound.add
      | apply HasPolynomialBound.mul
      | apply HasPolynomialBound.pow
      | (apply polynomialBound_const; positivity)
  obtain ⟨d,A,hA,hpoly⟩ := (polynomialBound_const (zero_le_one.trans hC)).mul (hp.pow q)
  refine ⟨d,A,hA,?_⟩
  intro F φ e hF hφ he hi hphase s B hs hs1 hB hFj hej heinv hedet hImm hgood hG hN
  have hB0 := zero_le_one.trans hB
  have hterms : 1 ≤ S B ∧ A₀*B^d₀ ≤ S B ∧ B^3 ≤ S B ∧ B^6 ≤ S B := by
    have h0 : 0 ≤ A₀*B^d₀ := mul_nonneg (zero_le_one.trans hA₀) (pow_nonneg hB0 _)
    have h3 : 0 ≤ B^3 := pow_nonneg hB0 _
    have h6 : 0 ≤ B^6 := pow_nonneg hB0 _
    dsimp [S]
    constructor
    · linarith
    constructor
    · linarith
    constructor <;> linarith
  have hj := (hjet F e hF he hi s B hs hs1 hB hFj hej heinv).mono_const hterms.2.1
  have hdomain := realModeDomain_smooth_phase_chart hF hφ e he hi hphase hImm hgood
  obtain ⟨hc,hf⟩ := hframe (hF.comp hi) hdomain hs hterms.1 hj
    (fun y hy => (inverse_gram_nonlinear_chart_bound hF e he hi hy hB0 hB0
      (hedet _ (e.map_target hy)) (hG _ (e.map_target hy))).trans (by
        convert hterms.2.2.1 using 1
        ring))
    (fun y hy => (inverse_normal_nonlinear_chart_bound hF hφ e he hi hphase hy hB0
      (hedet _ (e.map_target hy)) (hImm _ (e.map_target hy))
      (hgood _ (e.map_target hy)) (hN _ (e.map_target hy))).trans (by
        convert hterms.2.2.2 using 1
        ring))
  exact ⟨hc.mono_const (hpoly B hB).2,hf.mono_const (hpoly B hB).2⟩

end ClosedSurfaceR4.RealModes

end

end OAI
