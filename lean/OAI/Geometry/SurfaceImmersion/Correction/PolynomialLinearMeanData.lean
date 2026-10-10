import OAI.Geometry.SurfaceImmersion.Correction.PolynomialLinearMeanBudgets
import OAI.Geometry.SurfaceImmersion.Correction.UnperturbedMeanDataFromBounds

namespace OAI

/-! Actual supported mean data with polynomial geometric budgets, for
the linear phases used in the exact metric correction. -/
noncomputable section
open Set TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open WeightedEstimates PhaseMean RealModes PhaseGeometry

theorem polynomial_linear_charted_mean_data :
    ∃ (p : ℕ → ℕ) (A : ℕ → ℝ), (∀ m, 1 ≤ A m) ∧
    ∀ {G : Base → Space} {hG : ContDiff ℝ ∞ G} {φ : Base → ℝ}
      {K : Compacts Base} {τ : ℝ} {s : ℝ≥0}
      (c : PolynomialSolveData emptyMetricPolynomial 0 G hG φ K τ s)
      {U : Set SmallModes.Base} (hU : IsOpen U) {ξ : SmallModes.Base} (hξ : ξ ≠ 0),
      c.e = linearPhaseChart ξ hξ U hU →
      ∀ {U₀ : Set Base} (hU₀ : IsOpen U₀) (K₀ : Compacts Base),
      U₀ ⊆ K₀ → ∀ hKU₀ : (K : Set Base) ⊆ U₀, 0 < (s : ℝ) → s ≤ 1 →
      ∀ (ψ : SupportedField (F := ℝ) c.chartCompact) (Q : Tensor →L[ℝ] ℝ)
        {r ρ R : ℝ} {reference : SmallModes.Base → Tensor},
      (∀ x ∈ U, ρ+‖Q‖*r ≤ Q (reference x) ∧ Q (reference x) ≤ R-‖Q‖*r) →
      (∀ x ∈ U, Function.Injective (fderiv ℝ (G ∘ planeCoordinateIsometry.symm) x)) →
      (∀ x ∈ U, Good (realSecondTensor (G ∘ planeCoordinateIsometry.symm) x) ξ) →
      ∀ B P Pjet : ℕ → ℝ, (∀ m, 1 ≤ B m) → (∀ m, 1 ≤ P m) →
      (∀ m, 0 ≤ Pjet m) →
      (∀ m, ‖ξ‖ ≤ B m ∧ ‖(phaseEquiv ξ hξ).symm.toContinuousLinearMap‖ ≤ B m ∧
        ‖Q‖ ≤ B m ∧
        (∀ j ≤ m+2, WeightedBound U 1 j (B m/(s : ℝ)^(j-2))
          (G ∘ planeCoordinateIsometry.symm)) ∧
        (∀ x ∈ U, ‖(NormalFrame.gramDet
          (SmallModes.coordDeriv SmallModes.dx (G ∘ planeCoordinateIsometry.symm) x)
          (SmallModes.coordDeriv SmallModes.dy (G ∘ planeCoordinateIsometry.symm) x))⁻¹‖ ≤ B m) ∧
        (∀ x ∈ U, ‖secondQuadratic (realSecondTensor (G ∘ planeCoordinateIsometry.symm) x)
          (-ξ.2,ξ.1)‖⁻¹ ≤ B m)) →
      (∀ m, WeightedBound c.e.target s m (P m) ψ) →
      (∀ m j, j ≤ m+2 → WeightedBound U₀ 1 j (Pjet m/(s : ℝ)^(j-2)) G) →
      ∃ d : ChartedMeanData (c.onSourceDomain U₀ hU₀ hKU₀)
          r ρ R reference,
        d.cutoff = ψ ∧ d.form = (fun _ => Q) ∧
        ∀ m, d.budgets.inv m ≤ linearMeanGeometryBudget p A B P m ∧
          d.budgets.chi m ≤ linearMeanGeometryBudget p A B P m ∧
          d.budgets.forms m ≤ linearMeanGeometryBudget p A B P m ∧
          d.budgets.pull m ≤ linearMeanGeometryBudget p A B P m ∧
          d.budgets.psi m ≤ linearMeanGeometryBudget p A B P m ∧
          d.budgets.normal m ≤ linearMeanGeometryBudget p A B P m ∧
          d.budgets.mode m ≤ linearMeanGeometryBudget p A B P m := by
  obtain ⟨p,A,hA,hbudgets⟩ := polynomial_linear_mean_budgets
  refine ⟨p,A,hA,?_⟩
  intro G hG φ K τ s c U hU ξ hξ hce U₀ hU₀ K₀ hU₀K hKU₀ hs hs1
    ψ Q r ρ R reference hmargin hImm hgood B P Pjet hB hP hPjet hb hψ hpref
  have hGc : ContDiff ℝ ∞ (G ∘ planeCoordinateIsometry.symm) :=
    hG.comp planeCoordinateIsometry.symm.contDiff
  have hψ' : ∀ m, WeightedBound (linearPhaseChart ξ hξ U hU).target s m (P m) ψ := by
    simpa only [hce] using hψ
  obtain ⟨b,hb⟩ := hbudgets hGc hU hξ hs hs1 ψ Q B P hB hP hb hImm hgood hψ'
  have loc : LocalBounds c.e.source c.e.target s r ρ R reference
      c.realMap ψ (fun _ => Q) c.e c.e.symm := by
    simpa only [hce,linearPhaseChart_source,PolynomialSolveData.realMap] using
      linear_phase_local_bounds hGc hU hξ hImm hgood ψ.contDiff Q hmargin
  let b' : Budgets c.e.source c.e.target s c.realMap ψ (fun _ => Q) c.e c.e.symm := {
    inv := b.inv
    chi := b.chi
    psi := b.psi
    forms := b.forms
    pull := b.pull
    normal := b.normal
    mode := b.mode
    inv_pos := b.inv_pos
    chi_pos := b.chi_pos
    psi_pos := b.psi_pos
    forms_pos := b.forms_pos
    pull_pos := b.pull_pos
    normal_pos := b.normal_pos
    mode_pos := b.mode_pos
    inv_bound := by simpa only [hce] using b.inv_bound
    chi_bound := by simpa only [hce,linearPhaseChart_source] using b.chi_bound
    psi_bound := by simpa only [hce] using b.psi_bound
    normal_bound := by simpa only [hce,PolynomialSolveData.realMap] using b.normal_bound
    mode_bound := by simpa only [hce,PolynomialSolveData.realMap] using b.mode_bound
    forms_bound := by simpa only [hce] using b.forms_bound
    pull_bound := by simpa only [hce,linearPhaseChart_source] using b.pull_bound
  }
  obtain ⟨d,hcut,hform,hi,hχ,hQ,hpull,hpsi,hn,hm⟩ :=
    unperturbed_mean_data_from_bounds c hU₀ K₀ hU₀K hKU₀ hs hs1 ψ (fun _ => Q)
      loc b' Pjet hPjet hpref
  refine ⟨d,hcut,hform,?_⟩
  intro m
  rw [hi,hχ,hQ,hpull,hpsi,hn,hm]
  exact hb m

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
