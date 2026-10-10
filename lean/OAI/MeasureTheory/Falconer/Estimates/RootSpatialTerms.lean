import OAI.MeasureTheory.Falconer.Fourier.RootFourierError
import OAI.MeasureTheory.Falconer.Geometry.SeparatedSpatialDistanceForm
import OAI.MeasureTheory.Falconer.Graphs.ParentRetainedEnergy

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory Filter

noncomputable def rootDistanceEndpointKernel (d e : RootEndpointData) (N : ℕ) (sig : ℝ)
    (U V : DyadicSquare) (j : ℕ) (k : RootMaskIndex → ℕ) (r : ℝ) (z : Plane × Plane) : ℂ :=
  (((dist z.1 z.2)⁻¹)^j:ℝ) * sourceDistanceKernel (sourceConeCircle (sourceParentAxis U V))
    (rootLeftSymbol d N sig k) (rootRightSymbol e N sig k) r z.1 z.2

theorem rootDistanceEndpointKernel_measurable (d e : RootEndpointData) (N : ℕ) (sig : ℝ)
    (U V : DyadicSquare) (j : ℕ) (k : RootMaskIndex → ℕ) (r : ℝ) :
    Measurable (rootDistanceEndpointKernel d e N sig U V j k r) := by
  unfold rootDistanceEndpointKernel
  apply Measurable.mul
  · fun_prop
  · exact (measurable_sourceDistanceKernel _ _ _ (measurable_sourceConeCircle _)
      (rootLeftSymbol_measurable d N sig k) (rootRightSymbol_measurable e N sig k)).comp
      (f := fun z : Plane × Plane => (r,z)) (measurable_const.prodMk measurable_id)

theorem rootDistanceEndpointKernel_integrable (d e : RootEndpointData)
    [IsFiniteMeasure d.ρ] [IsFiniteMeasure e.ρ] (N : ℕ) (sig : ℝ)
    (hd : 0 < d.Q.side) (he : 0 < e.Q.side) (U V : DyadicSquare)
    {δ : ℝ} (hδ : 0 < δ) (hsep : ∀ᵐ z ∂d.ρ.prod e.ρ, δ ≤ dist z.1 z.2)
    (j : ℕ) {b : ℂ × (RootMaskIndex → ℕ)}
    (hb : b ∈ inverseLeibnizTerms j (rootMaskIndices d e)) (r : ℝ) :
    Integrable (rootDistanceEndpointKernel d e N sig U V j b.2 r) (d.ρ.prod e.ρ) := by
  let C := symbolDerivativeConstant (2*j)^(2*j)
  have hC : 0 ≤ C := pow_nonneg (zero_le_one.trans (symbolDerivativeConstant_one_le _)) _
  refine Integrable.of_bound (rootDistanceEndpointKernel_measurable d e N sig U V j b.2 r).aestronglyMeasurable
    (δ⁻¹^j*(1*C*C*sourceArcLength.real univ)) ?_
  filter_upwards [hsep] with z hz
  have hinv := inv_anti₀ hδ hz
  have hn : ‖((((dist z.1 z.2)⁻¹)^j:ℝ):ℂ)‖ ≤ δ⁻¹^j := by
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by positivity)]
    exact pow_le_pow_left₀ (by positivity) hinv j
  have hk := sourceDistanceKernel_norm_le (sourceConeCircle (sourceParentAxis U V)) _ _ (by norm_num : (0:ℝ) ≤ 1) hC hC
    (sourceConeCircle_norm_le (sourceParentAxis U V)) (rootLeftSymbol_norm d e hd N j sig hb)
    (rootRightSymbol_norm d e he N j sig hb) r z.1 z.2
  change ‖_ * _‖ ≤ _
  rw [norm_mul]
  exact mul_le_mul hn hk (norm_nonneg _) (by positivity)

theorem rootDistanceEndpointKernel_form (δ L : ℝ) (hδ : 0 < δ) (hL : 0 < L)
    (d e : RootEndpointData) [IsFiniteMeasure d.ρ] [IsFiniteMeasure e.ρ]
    (N : ℕ) (sig : ℝ) (hd : 0 < d.Q.side) (he : 0 < e.Q.side) (U V : DyadicSquare)
    (hcarry₁ : ∀ᵐ x ∂d.ρ, x ∈ U.carrier) (hcarry₂ : ∀ᵐ y ∂e.ρ, y ∈ V.carrier)
    (hsep : ∀ x ∈ U.carrier, ∀ y ∈ V.carrier, δ ≤ dist x y ∧ dist x y ≤ L)
    (j : ℕ) {b : ℂ × (RootMaskIndex → ℕ)}
    (hb : b ∈ inverseLeibnizTerms j (rootMaskIndices d e)) (r : ℝ) :
    (∫ z, rootDistanceEndpointKernel d e N sig U V j b.2 r z ∂d.ρ.prod e.ρ) =
      ∫ ξ, spatialFourierCoeff δ L hδ hL j ξ *
        sourceParentDistanceF U V d.ρ e.ρ 1 1
          (spatialPhasedSymbol 1 ξ (rootLeftSymbol d N sig b.2))
          (spatialPhasedSymbol 1 ξ (rootRightSymbol e N sig b.2)) r := by
  have hC : 0 ≤ symbolDerivativeConstant (2*j)^(2*j) :=
    pow_nonneg (zero_le_one.trans (symbolDerivativeConstant_one_le _)) _
  have hh := separatedSpatialDistanceForm δ L hδ hL j (s := 1) (by norm_num)
    d.ρ e.ρ U.carrier V.carrier U.measurable V.measurable
    (fun x hx y hy => by simpa only [div_one] using hsep x hx y hy)
    1 1 _ _ _ (measurable_sourceConeCircle (sourceParentAxis U V))
    (rootLeftSymbol_measurable d N sig b.2) (rootRightSymbol_measurable e N sig b.2)
    (by norm_num : (0:ℝ) ≤ 1) hC hC (sourceConeCircle_norm_le _)
    (rootLeftSymbol_norm d e hd N j sig hb) (rootRightSymbol_norm d e he N j sig hb) r
  rw [Measure.restrict_eq_self_of_ae_mem hcarry₁,Measure.restrict_eq_self_of_ae_mem hcarry₂] at hh
  simpa only [one_mul,inv_one,one_smul,div_one,inv_pow,rootDistanceEndpointKernel,sourceParentDistanceF] using hh

end PlanarFalconer

end OAI
