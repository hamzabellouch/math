import OAI.MeasureTheory.Falconer.Shells.HighShellFourierError
import OAI.MeasureTheory.Falconer.Geometry.SeparatedSpatialDistanceForm
import OAI.MeasureTheory.Falconer.Graphs.ParentRetainedEnergy

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory Filter
namespace PositiveDistanceData

noncomputable def inverseDistanceEndpointKernel (d : PositiveDistanceData) (j : ℕ)
    (k : PairMaskIndex → ℕ) (r : ℝ) (z : Plane × Plane) : ℂ :=
  ((((dist z.1 z.2/(2:ℝ)^(-(d.a:ℝ)))⁻¹)^j:ℝ):ℂ) *
    sourceDistanceKernel
      (sourceConeCircle (sourceParentAxis (d.Q.descendant d.X) (d.Q.descendant d.Y)))
      (d.inverseEndpointSymbol k 0) (d.inverseEndpointSymbol k 1) r z.1 z.2

 theorem inverseDistanceEndpointKernel_measurable (d : PositiveDistanceData) (j : ℕ)
    (k : PairMaskIndex → ℕ) (r : ℝ) : Measurable (d.inverseDistanceEndpointKernel j k r) := by
  unfold inverseDistanceEndpointKernel
  apply Measurable.mul
  · fun_prop
  · exact (measurable_sourceDistanceKernel _ _ _ (measurable_sourceConeCircle (sourceParentAxis (d.Q.descendant d.X) (d.Q.descendant d.Y)))
      (d.inverseEndpointSymbol_measurable k 0) (d.inverseEndpointSymbol_measurable k 1)).comp
      (f := fun z : Plane × Plane => (r,z)) (measurable_const.prodMk measurable_id)

 theorem inverseDistanceEndpointKernel_integrable (d : PositiveDistanceData) [IsFiniteMeasure d.ρ]
    (hQ : 0 < d.Q.side) (hs : d.StronglySeparated) (j : ℕ)
    {b : ℂ × (PairMaskIndex → ℕ)} (hb : b ∈ inverseLeibnizTerms j (pairMaskIndices d.inverseDescriptorList))
    (r : ℝ) : Integrable (d.inverseDistanceEndpointKernel j b.2 r) d.cellPair := by
  let C := symbolDerivativeConstant (2*j)^(2*j)
  have hC : 0 ≤ C := pow_nonneg (zero_le_one.trans (symbolDerivativeConstant_one_le _)) _
  refine Integrable.of_bound (d.inverseDistanceEndpointKernel_measurable j b.2 r).aestronglyMeasurable
    (1*C*C*sourceArcLength.real univ) ?_
  filter_upwards [d.ae_cellPair_mem] with z hz
  have hd := (d.separated_distance_ratio hQ hs (z := z) hz.1 hz.2).1
  have hdist : 1 ≤ dist z.1 z.2/(2:ℝ)^(-(d.a:ℝ)) := by linarith
  have hinv : (dist z.1 z.2/(2:ℝ)^(-(d.a:ℝ)))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hdist
  have hn : ‖((((dist z.1 z.2/(2:ℝ)^(-(d.a:ℝ)))⁻¹)^j:ℝ):ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact pow_le_one₀ (by positivity) hinv
  have hk := sourceDistanceKernel_norm_le _ _ _ (by norm_num : (0:ℝ) ≤ 1) hC hC
    (sourceConeCircle_norm_le (sourceParentAxis (d.Q.descendant d.X) (d.Q.descendant d.Y))) (d.inverseEndpointSymbol_norm hQ j hb 0)
    (d.inverseEndpointSymbol_norm hQ j hb 1) r z.1 z.2
  change ‖_ * _‖ ≤ _
  rw [norm_mul]
  exact (mul_le_mul_of_nonneg_right hn (norm_nonneg _)).trans (by simpa only [one_mul] using hk)

 theorem inverseDistanceEndpointKernel_form (d : PositiveDistanceData) [IsFiniteMeasure d.ρ]
    (hQ : 0 < d.Q.side) (hs : d.StronglySeparated) (j : ℕ)
    {b : ℂ × (PairMaskIndex → ℕ)} (hb : b ∈ inverseLeibnizTerms j (pairMaskIndices d.inverseDescriptorList))
    (r : ℝ) :
    (d.levelMass^(-2:ℤ):ℝ) • (∫ z, d.inverseDistanceEndpointKernel j b.2 r z ∂d.cellPair) =
      ∫ ξ, spatialFourierCoeff 96 2004 (by norm_num) (by norm_num) j ξ *
        sourceParentDistanceF (d.Q.descendant d.X) (d.Q.descendant d.Y)
          d.ρ d.ρ d.levelMass d.levelMass
          (spatialPhasedSymbol ((2:ℝ)^(-(d.a:ℝ))) ξ (d.inverseEndpointSymbol b.2 0))
          (spatialPhasedSymbol ((2:ℝ)^(-(d.a:ℝ))) ξ (d.inverseEndpointSymbol b.2 1)) r := by
  have hC : 0 ≤ symbolDerivativeConstant (2*j)^(2*j) :=
    pow_nonneg (zero_le_one.trans (symbolDerivativeConstant_one_le _)) _
  have he := separatedSpatialDistanceForm 96 2004 (by norm_num) (by norm_num) j
    (s := (2:ℝ)^(-(d.a:ℝ))) (by positivity) d.ρ d.ρ
    (d.Q.descendant d.X).carrier (d.Q.descendant d.Y).carrier
    (d.Q.descendant d.X).measurable (d.Q.descendant d.Y).measurable
    (fun x hx y hy => d.separated_distance_ratio hQ hs (z := (x,y)) hx hy)
    d.levelMass d.levelMass _ _ _ (measurable_sourceConeCircle (sourceParentAxis (d.Q.descendant d.X) (d.Q.descendant d.Y)))
    (d.inverseEndpointSymbol_measurable b.2 0) (d.inverseEndpointSymbol_measurable b.2 1)
    (by norm_num : (0:ℝ) ≤ 1) hC hC (sourceConeCircle_norm_le (sourceParentAxis (d.Q.descendant d.X) (d.Q.descendant d.Y)))
    (d.inverseEndpointSymbol_norm hQ j hb 0) (d.inverseEndpointSymbol_norm hQ j hb 1) r
  simpa only [sourceParentDistanceF, inverseDistanceEndpointKernel, cellPair,
    zpow_neg,zpow_ofNat,pow_two,inv_pow,Complex.ofReal_inv,Complex.ofReal_pow] using he

end PositiveDistanceData

end PlanarFalconer

end OAI
