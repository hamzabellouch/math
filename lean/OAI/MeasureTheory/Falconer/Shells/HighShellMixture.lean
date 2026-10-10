import OAI.MeasureTheory.Falconer.Shells.HighShellFiniteSeparation
import OAI.MeasureTheory.Falconer.Shells.ShellMultipliers
import OAI.MeasureTheory.Falconer.Estimates.SpatialPhasedDistanceForm

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
namespace PositiveDistanceData

noncomputable def inversePhasedForm (d : PositiveDistanceData)
    (k : PairMaskIndex → ℕ) (ξ : Plane) : ℝ → ℂ :=
  sourceParentDistanceF (d.Q.descendant d.X) (d.Q.descendant d.Y)
    d.ρ d.ρ d.levelMass d.levelMass
    (spatialPhasedSymbol ((2:ℝ)^(-(d.a:ℝ))) ξ (d.inverseEndpointSymbol k 0))
    (spatialPhasedSymbol ((2:ℝ)^(-(d.a:ℝ))) ξ (d.inverseEndpointSymbol k 1))

noncomputable def inverseSpatialMixture (d : PositiveDistanceData) (j : ℕ)
    (k : PairMaskIndex → ℕ) (r : ℝ) : ℂ :=
  ∫ ξ, spatialFourierCoeff 96 2004 (by norm_num) (by norm_num) j ξ * d.inversePhasedForm k ξ r

noncomputable def inversePhasedBound (d : PositiveDistanceData) (j : ℕ) : ℝ :=
  (1*(symbolDerivativeConstant (2*j)^(2*j))*(symbolDerivativeConstant (2*j)^(2*j))*
    sourceArcLength.real univ) * ((d.ρ (d.Q.descendant d.X).carrier).toReal/d.levelMass)*
    ((d.ρ (d.Q.descendant d.Y).carrier).toReal/d.levelMass)

theorem inversePhasedBound_nonneg (d : PositiveDistanceData) (j : ℕ) :
    0 ≤ d.inversePhasedBound j := by
  have hC := zero_le_one.trans (symbolDerivativeConstant_one_le (2*j))
  unfold inversePhasedBound levelMass
  positivity

theorem inversePhasedForm_data (d : PositiveDistanceData) [IsFiniteMeasure d.ρ]
    (hQ : 0 < d.Q.side) (j : ℕ) {b : ℂ × (PairMaskIndex → ℕ)}
    (hb : b ∈ inverseLeibnizTerms j (pairMaskIndices d.inverseDescriptorList)) :
    Measurable (fun p : Plane × ℝ => d.inversePhasedForm b.2 p.1 p.2) ∧
      ∀ p : Plane × ℝ, ‖d.inversePhasedForm b.2 p.1 p.2‖ ≤ d.inversePhasedBound j := by
  have hC : 0 ≤ symbolDerivativeConstant (2*j)^(2*j) :=
    pow_nonneg (zero_le_one.trans (symbolDerivativeConstant_one_le _)) _
  constructor
  · exact spatialPhasedDistanceF_joint_measurable _ d.ρ d.ρ _ _ d.levelMass d.levelMass
      _ _ _ (measurable_sourceConeCircle _) (d.inverseEndpointSymbol_measurable b.2 0)
      (d.inverseEndpointSymbol_measurable b.2 1) (by norm_num) hC hC
      (sourceConeCircle_norm_le _) (d.inverseEndpointSymbol_norm hQ j hb 0)
      (d.inverseEndpointSymbol_norm hQ j hb 1)
  · intro p
    apply sourceDistanceF_norm_le d.ρ d.ρ _ _
      (show 0 < d.levelMass by unfold levelMass; positivity)
      (show 0 < d.levelMass by unfold levelMass; positivity)
      _ _ _ (by norm_num) hC hC (sourceConeCircle_norm_le _)
    · intro x hx ω
      rw [spatialPhasedSymbol_norm]
      exact d.inverseEndpointSymbol_norm hQ j hb 0 x ω
    · intro y hy ω
      rw [spatialPhasedSymbol_norm]
      exact d.inverseEndpointSymbol_norm hQ j hb 1 y ω

theorem inverseSpatialMixture_data (d : PositiveDistanceData) [IsFiniteMeasure d.ρ]
    (hQ : 0 < d.Q.side) (j : ℕ) {b : ℂ × (PairMaskIndex → ℕ)}
    (hb : b ∈ inverseLeibnizTerms j (pairMaskIndices d.inverseDescriptorList))
    (μ : Measure ℝ) [IsFiniteMeasure μ] :
    Measurable (d.inverseSpatialMixture j b.2) ∧
    (∀ r, ‖d.inverseSpatialMixture j b.2 r‖ ≤
      spatialFourierCost 96 2004 (by norm_num) (by norm_num) j*d.inversePhasedBound j) ∧
    Integrable (fun r => ‖d.inverseSpatialMixture j b.2 r‖^2) μ := by
  have hd := d.inversePhasedForm_data hQ j hb
  exact continuous_shell_mixture_bound μ _
    (spatialFourierCoeff 96 2004 (by norm_num) (by norm_num) j).continuous.measurable
    (spatialFourierCoeff_integrable _ _ _ _ _) _ hd.1 (d.inversePhasedBound_nonneg j) hd.2

theorem inverseSpatialMixture_shell (d : PositiveDistanceData) [IsFiniteMeasure d.ρ]
    (hQ : 0 < d.Q.side) (j : ℕ) {b : ℂ × (PairMaskIndex → ℕ)}
    (hb : b ∈ inverseLeibnizTerms j (pairMaskIndices d.inverseDescriptorList))
    (μ : Measure ℝ) [IsFiniteMeasure μ] {B : ℝ}
    (hB : ∀ ξ, (∫ r, ‖d.inversePhasedForm b.2 ξ r‖^2 ∂μ) ≤ B) :
    (∫ r, ‖d.inverseSpatialMixture j b.2 r‖^2 ∂μ) ≤
      (spatialFourierCost 96 2004 (by norm_num) (by norm_num) j)^2*B := by
  have hd := d.inversePhasedForm_data hQ j hb
  exact continuous_coefficient_shell_square μ _
    (spatialFourierCoeff 96 2004 (by norm_num) (by norm_num) j).continuous.measurable
    (spatialFourierCoeff_integrable _ _ _ _ _) _ hd.1 (d.inversePhasedBound_nonneg j) hd.2 hB

end PositiveDistanceData

end PlanarFalconer

end OAI
