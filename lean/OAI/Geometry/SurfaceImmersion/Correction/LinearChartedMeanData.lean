import OAI.Geometry.SurfaceImmersion.Atlas.LinearPhaseBudgets
import OAI.Geometry.SurfaceImmersion.Correction.CompactChartedMeanData

namespace OAI

/-! Assemble the actual charted mean data for a linear good phase from
its immersion, compact coordinate domains and positive coefficient margin. -/
noncomputable section
open TopologicalSpace Set
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open PhaseMean RealModes WeightedEstimates PhaseGeometry

theorem linear_charted_mean_data {n : ℕ} {P : Fin 3 → Fin n → Expression}
    {ε τ : ℝ} {s : ℝ≥0} {G : Base → Space} {hG : ContDiff ℝ ∞ G}
    {φ : Base → ℝ} {K : Compacts Base} (c : PolynomialSolveData P ε G hG φ K τ s)
    {U Ω K₁ : Set SmallModes.Base} (hU : IsOpen U) (hΩ : IsOpen Ω)
    (hK₁ : IsCompact K₁) (hUK₁ : U ⊆ K₁) (hK₁Ω : K₁ ⊆ Ω)
    {ξ : SmallModes.Base} (hξ : ξ ≠ 0)
    (hchart : c.e = linearPhaseChart ξ hξ U hU)
    (hImm : ∀ x ∈ Ω, Function.Injective (fderiv ℝ (G ∘ planeCoordinateIsometry.symm) x))
    (hgood : ∀ x ∈ Ω, Good (realSecondTensor (G ∘ planeCoordinateIsometry.symm) x) ξ)
    (ψ : SupportedField (F := ℝ) c.chartCompact) (Q : Tensor →L[ℝ] ℝ)
    {r ρ R : ℝ} {reference : SmallModes.Base → Tensor}
    (hmargin : ∀ x ∈ U, ρ + ‖Q‖*r ≤ Q (reference x) ∧ Q (reference x) ≤ R - ‖Q‖*r)
    {K₀ : Set Base} (hK₀ : IsCompact K₀) (hUK₀ : c.U ⊆ K₀) (hs1 : s ≤ 1)
    {J : Set LowJet} (hJ : IsCompact J) (hJO : J ⊆ c.O) (hGJ : MapsTo (lowJet G) c.U J) :
    ∃ d : ChartedMeanData c r ρ R reference, d.cutoff = ψ ∧ d.form = (fun _ => Q) := by
  have hF := hG.comp planeCoordinateIsometry.symm.contDiff
  have hlocal : LocalBounds c.e.source c.e.target s r ρ R reference c.realMap ψ
      (fun _ => Q) c.e c.e.symm := by
    simpa only [PolynomialSolveData.realMap,hchart,linearPhaseChart_source] using
      linear_phase_local_bounds hF hU hξ (fun x hx => hImm x (hK₁Ω (hUK₁ hx)))
        (fun x hx => hgood x (hK₁Ω (hUK₁ hx))) ψ.contDiff Q hmargin
  obtain ⟨b₀⟩ := linear_phase_budgets hF hΩ hU hK₁ hUK₁ hK₁Ω hξ hImm hgood ψ.contDiff Q
  have b : Budgets c.e.source c.e.target 1 c.realMap ψ (fun _ => Q) c.e c.e.symm := by
    simpa only [PolynomialSolveData.realMap,hchart,linearPhaseChart_source] using b₀
  exact compact_charted_mean_data c ψ (fun _ => Q) hlocal (b.atScale s s.coe_nonneg hs1)
    hK₀ hUK₀ hs1 hJ hJO hGJ

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
