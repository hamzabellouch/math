import OAI.MeasureTheory.Falconer.Graphs.GraphPointIntegralChart
import OAI.MeasureTheory.Falconer.Graphs.GraphInheritedTransformChart

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

theorem sourceGraphFourTransform_pointIntegral
    (ρ : Fin 4 → Measure Plane) [∀ i, IsFiniteMeasure (ρ i)]
    (X : Fin 4 → Set Plane) (M : Fin 4 → ℝ)
    (b : Fin 4 → Plane → UnitCircle → ℂ)
    (hb : ∀ i, Measurable (fun p : Plane × UnitCircle => b i p.1 p.2))
    (hbcont : ∀ i x, Continuous (b i x))
    (B : Fin 4 → ℝ) (hB : ∀ i, 0 ≤ B i) (hbound : ∀ i x ω, ‖b i x ω‖ ≤ B i)
    (distance plus : Bool) (axis δ v : ℝ) (j k : ℕ)
    {Ψ : ℝ → ℝ} (hΨ : Continuous Ψ) (hsupp : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4) :
    ((2:ℝ)^v)⁻¹ • (∫ r : ℝ, ∫ u, ∫ w, Ψ (r/(2:ℝ)^v) •
      sourceGraphFourTransform ρ X M b (graphSourceWeight distance plus axis (angularBinCount δ) j k) r u w
        ∂sourceArcLength ∂sourceArcLength) =
    ((M 0*M 1)*(M 2*M 3))⁻¹ •
      (∫ x, graphPointIntegral (graphAmplitudePullback b x distance plus axis δ j k Ψ)
        v (graphSourceSign distance plus) (x 0-x 1) (x 2-x 3)
        ∂Measure.pi (fun i => (ρ i).restrict (X i))) := by
  let W := graphSourceWeight distance plus axis (angularBinCount δ) j k
  let μ := Measure.pi (fun i => (ρ i).restrict (X i))
  have hW := graphSourceWeight_continuous distance plus axis (angularBinCount δ) j k
  have hw := graphSourceWeight_norm_le distance plus axis (angularBinCount δ) j k
  have hchart := graphSourceWeight_parameter distance plus axis (angularBinCount δ) j k
  obtain ⟨C,hC,hc⟩ := continuous_supported_bump_bound hΨ hsupp
  rw [sourceGraphFourTransform_chart ρ X M b W hb hbcont hW B hB hbound hw hΨ hsupp hC hc
    (by positivity : (0:ℝ) < (2:ℝ)^v) (graphSourceChartAxis distance plus) hchart]
  congr 1
  have hi := graphFourKernel_spatial_integrable μ b W hb hW.measurable B hB hbound hw
    hΨ.measurable hsupp hC hc ((2:ℝ)^v) (graphSourceChartAxis distance plus) hchart
  rw [integral_integral_swap hi]
  apply integral_congr_ae
  filter_upwards with x
  exact graphTransport_integral_eq_pointIntegral b x distance plus axis δ v j k Ψ
    (graphFourKernel_transport_integrable b W hbcont hW B hB hbound hw hΨ hsupp hC hc
      ((2:ℝ)^v) (graphSourceChartAxis distance plus) hchart x)

theorem actual_inherited_fourTransform_pointIntegral
    {ι : Fin 4 → Type*} (S : ∀ l, Finset (ι l)) (d : ∀ l, ι l → PolicyDescriptor)
    (k : ∀ l, ι l → ℕ) (Q : Fin 4 → DyadicSquare) (hQ : ∀ l, 0 < (Q l).side)
    (ρ : Fin 4 → Measure Plane) [∀ l, IsFiniteMeasure (ρ l)]
    (mass : Fin 4 → ℝ → ℝ) (N : ℕ) (lam sig : ℝ) (J i : ℕ)
    (h : Fin 4 → Plane → ℂ) (hh : ∀ l, Measurable (h l)) (hhbound : ∀ l x, ‖h l x‖ ≤ 1)
    (K : ℕ) (hK : ∀ l, ∑ t ∈ S l, k l t ≤ K)
    (X : Fin 4 → Set Plane) (M : Fin 4 → ℝ)
    (distance plus : Bool) (axis δ v : ℝ) (j₁ j₂ : ℕ)
    {Ψ : ℝ → ℝ} (hΨ : Continuous Ψ) (hsupp : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4) :
    let b := fun l => inheritedCircleSymbol (S l) (d l) (k l) (Q l) (ρ l) (mass l) N lam sig J i (h l)
    ((2:ℝ)^v)⁻¹ • (∫ r : ℝ, ∫ u, ∫ w, Ψ (r/(2:ℝ)^v) •
      sourceGraphFourTransform ρ X M b (graphSourceWeight distance plus axis (angularBinCount δ) j₁ j₂) r u w
        ∂sourceArcLength ∂sourceArcLength) =
    ((M 0*M 1)*(M 2*M 3))⁻¹ •
      (∫ x, graphPointIntegral (graphAmplitudePullback b x distance plus axis δ j₁ j₂ Ψ)
        v (graphSourceSign distance plus) (x 0-x 1) (x 2-x 3)
        ∂Measure.pi (fun l => (ρ l).restrict (X l))) := by
  dsimp only
  let B : Fin 4 → ℝ := fun _ => symbolDerivativeConstant K^K
  apply sourceGraphFourTransform_pointIntegral ρ X M _ _ _ B _ _ distance plus axis δ v j₁ j₂ hΨ hsupp
  · intro l
    exact measurable_inheritedCircleSymbol (S l) (d l) (k l) (Q l) (ρ l) (mass l)
      N lam sig J i (h l) (hh l)
  · intro l x
    exact inheritedCircleSymbol_continuous (S l) (d l) (k l) (Q l) (hQ l) (ρ l) (mass l)
      N lam sig J i (h l) x
  · intro l
    exact pow_nonneg (zero_le_one.trans (symbolDerivativeConstant_one_le K)) K
  · intro l x ω
    exact inheritedCircleSymbol_norm_le (S l) (d l) (k l) (Q l) (hQ l) (ρ l) (mass l)
      N lam sig J i (h l) K (hK l) x (hhbound l x) ω

end PlanarFalconer

end OAI
