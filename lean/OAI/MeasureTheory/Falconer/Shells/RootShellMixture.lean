import OAI.MeasureTheory.Falconer.Shells.RootShellData
import OAI.MeasureTheory.Falconer.Shells.ShellMultipliers
import OAI.MeasureTheory.Falconer.Estimates.SpatialPhasedDistanceForm

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
namespace RootShellData

noncomputable def inversePhasedForm (d : RootShellData)
    (k : RootMaskIndex → ℕ) (ξ : Plane) : ℝ → ℂ :=
  sourceParentDistanceF d.U d.V
    d.left.ρ d.right.ρ 1 1
    (spatialPhasedSymbol 1 ξ (d.endpointLeft k))
    (spatialPhasedSymbol 1 ξ (d.endpointRight k))

noncomputable def inverseSpatialMixture (d : RootShellData) (δ L : ℝ) (hδ : 0 < δ) (hL : 0 < L) (j : ℕ)
    (k : RootMaskIndex → ℕ) (r : ℝ) : ℂ :=
  ∫ ξ, spatialFourierCoeff δ L hδ hL j ξ * d.inversePhasedForm k ξ r

noncomputable def inversePhasedBound (d : RootShellData) (j : ℕ) : ℝ :=
  (1*(symbolDerivativeConstant (2*j)^(2*j))*(symbolDerivativeConstant (2*j)^(2*j))*
    sourceArcLength.real univ) * ((d.left.ρ d.U.carrier).toReal/1)*
    ((d.right.ρ d.V.carrier).toReal/1)

theorem inversePhasedBound_nonneg (d : RootShellData) (j : ℕ) :
    0 ≤ d.inversePhasedBound j := by
  have hC := zero_le_one.trans (symbolDerivativeConstant_one_le (2*j))
  unfold inversePhasedBound
  positivity

theorem inversePhasedForm_data (d : RootShellData) [IsFiniteMeasure d.left.ρ] [IsFiniteMeasure d.right.ρ]
    (hd : 0 < d.left.Q.side) (he : 0 < d.right.Q.side) (j : ℕ) {b : ℂ × (RootMaskIndex → ℕ)}
    (hb : b ∈ inverseLeibnizTerms j (d.indices)) :
    Measurable (fun p : Plane × ℝ => d.inversePhasedForm b.2 p.1 p.2) ∧
      ∀ p : Plane × ℝ, ‖d.inversePhasedForm b.2 p.1 p.2‖ ≤ d.inversePhasedBound j := by
  have hC : 0 ≤ symbolDerivativeConstant (2*j)^(2*j) :=
    pow_nonneg (zero_le_one.trans (symbolDerivativeConstant_one_le _)) _
  constructor
  · exact spatialPhasedDistanceF_joint_measurable 1 d.left.ρ d.right.ρ d.U.carrier d.V.carrier 1 1
      _ _ _ (measurable_sourceConeCircle _) (d.endpointLeft_measurable b.2)
      (d.endpointRight_measurable b.2) (by norm_num) hC hC
      (sourceConeCircle_norm_le _) (d.endpointLeft_norm hd j hb)
      (d.endpointRight_norm he j hb)
  · intro p
    apply sourceDistanceF_norm_le d.left.ρ d.right.ρ d.U.carrier d.V.carrier
      (show (0:ℝ) < 1 by norm_num)
      (show (0:ℝ) < 1 by norm_num)
      _ _ _ (by norm_num) hC hC (sourceConeCircle_norm_le _)
    · intro x hx ω
      rw [spatialPhasedSymbol_norm]
      exact d.endpointLeft_norm hd j hb x ω
    · intro y hy ω
      rw [spatialPhasedSymbol_norm]
      exact d.endpointRight_norm he j hb y ω

theorem inverseSpatialMixture_data (d : RootShellData) (δ L : ℝ) (hδ : 0 < δ) (hL : 0 < L) [IsFiniteMeasure d.left.ρ] [IsFiniteMeasure d.right.ρ]
    (hd : 0 < d.left.Q.side) (he : 0 < d.right.Q.side) (j : ℕ) {b : ℂ × (RootMaskIndex → ℕ)}
    (hb : b ∈ inverseLeibnizTerms j (d.indices))
    (μ : Measure ℝ) [IsFiniteMeasure μ] :
    Measurable (d.inverseSpatialMixture δ L hδ hL j b.2) ∧
    (∀ r, ‖d.inverseSpatialMixture δ L hδ hL j b.2 r‖ ≤
      spatialFourierCost δ L hδ hL j*d.inversePhasedBound j) ∧
    Integrable (fun r => ‖d.inverseSpatialMixture δ L hδ hL j b.2 r‖^2) μ := by
  have hd := d.inversePhasedForm_data hd he j hb
  exact continuous_shell_mixture_bound μ _
    (spatialFourierCoeff δ L hδ hL j).continuous.measurable
    (spatialFourierCoeff_integrable _ _ _ _ _) _ hd.1 (d.inversePhasedBound_nonneg j) hd.2

theorem inverseSpatialMixture_shell (d : RootShellData) (δ L : ℝ) (hδ : 0 < δ) (hL : 0 < L) [IsFiniteMeasure d.left.ρ] [IsFiniteMeasure d.right.ρ]
    (hd : 0 < d.left.Q.side) (he : 0 < d.right.Q.side) (j : ℕ) {b : ℂ × (RootMaskIndex → ℕ)}
    (hb : b ∈ inverseLeibnizTerms j (d.indices))
    (μ : Measure ℝ) [IsFiniteMeasure μ] {B : ℝ}
    (hB : ∀ ξ, (∫ r, ‖d.inversePhasedForm b.2 ξ r‖^2 ∂μ) ≤ B) :
    (∫ r, ‖d.inverseSpatialMixture δ L hδ hL j b.2 r‖^2 ∂μ) ≤
      (spatialFourierCost δ L hδ hL j)^2*B := by
  have hd := d.inversePhasedForm_data hd he j hb
  exact continuous_coefficient_shell_square μ _
    (spatialFourierCoeff δ L hδ hL j).continuous.measurable
    (spatialFourierCoeff_integrable _ _ _ _ _) _ hd.1 (d.inversePhasedBound_nonneg j) hd.2 hB

end RootShellData

end PlanarFalconer

end OAI
