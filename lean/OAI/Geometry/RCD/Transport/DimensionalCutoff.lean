import OAI.Geometry.RCD.Transport.DimensionalH1

namespace OAI

/-! # The actual heat cutoff secant retains the dimensional entropy rate -/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology NNReal ENNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] [SeparableSpace X]

theorem NoncollapsedRCD.dimensional_cutoff_heat_secant
    (K : ℝ) (n : ℕ) [IsLocallyFiniteMeasure (hausdorff n X)] (hn : 2 ≤ n)
    (hX : NoncollapsedRCD K n X) (hK : K ≤ 0) {N : ℝ} (hN : (n:ℝ) ≤ N) (p : X) {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hvol : ∀ R : ℝ, 1 ≤ R → (hausdorff n X).real (closedBall p (2*R)) ≤ A*Real.exp (B*R))
    (f : Lp ℝ 2 (hausdorff n X)) (C : ℝ≥0) (hf0 : 0 ≤ f)
    (hfC : ∀ᵐ x ∂hausdorff n X, f x ≤ C)
    (hfi : Integrable f (hausdorff n X)) (hfm : ∫x, f x ∂hausdorff n X = 1)
    {r : ℝ} (hfs : ∀ᵐ x ∂hausdorff n X, f x ≠ 0 → dist p x ≤ r)
    (ν : Measure X) [IsProbabilityMeasure ν] (hν : ν ≤ ENNReal.ofReal C • hausdorff n X)
    {R t h : ℝ} (hR : 1 ≤ R) (ht : 0 < t) (hh : 0 < h)
    (hνS : ∀ᵐ x ∂ν, dist x p ≤ 2*R)
    (hm : (1:ℝ)/2 ≤ ∫x, radialCutoff p R x*heatAt (hausdorff n X) hX.quadratic (t+h) f x ∂hausdorff n X) :
    let μ := hausdorff n X
    let η := radialHeatMeasure μ hX.quadratic p R (t+h) f
    let ρ := radialHeatSobolev μ hX.quadratic p (zero_lt_one.trans_le hR) (add_pos ht hh) f C
    ((wassersteinSq η ν).toReal-(wassersteinSq (heatMeasure μ hX.quadratic t f) ν).toReal)/(2*h) ≤
      entropyPowerRate N (-(K*(wassersteinSq η ν).toReal/N))
        (Real.exp (-boltzmannEntropy μ η/N)) (Real.exp (-boltzmannEntropy μ ν/N))+
      (1000*(A+1)*Real.exp ((12*B+4)*R)) *
        (((2*(1+1/(t/2)))^2*‖f‖*h)+(h⁻¹+2)*‖ρ-heatSobolev μ hX.quadratic (t+h) (add_pos ht hh) f‖) := by
  let μ := hausdorff n X
  let η := radialHeatMeasure μ hX.quadratic p R (t+h) f
  let ρ := radialHeatSobolev μ hX.quadratic p (zero_lt_one.trans_le hR) (add_pos ht hh) f C
  have hd := radialHeatMeasure_data μ hX.quadratic p hA hB hvol f C hf0 hfC hfi hfm
    (zero_lt_one.trans_le hR) (add_pos ht hh) hm
  let : IsProbabilityMeasure η := hd.1
  have hv := radialHeatSobolev_data μ hX.quadratic p hA hB hvol f C hf0 hfC hfi hfm
    (zero_lt_one.trans_le hR) (add_pos ht hh) hm
  have hη := radialHeatSobolev_measure μ hX.quadratic p (zero_lt_one.trans_le hR) (add_pos ht hh) f C hf0 hfC
  have hν' : ν ≤ ENNReal.ofReal (2*C) • μ := hν.trans (by gcongr ; nlinarith [C.coe_nonneg])
  obtain ⟨u,φ,ψ,hφ,hψ,hφb,hψb,hφS,hψS,hφs,hψs,hu,had,hdual,hE⟩ :=
    hX.quantitative_H1_dimensional_subgradient K n hn hK hN η ν ENNReal.ofReal_ne_top hd.2.1 hν'
      p (by positivity : 0 ≤ 2*R) hd.2.2 hνS ρ (2*C) hv.1 hv.2.1 hv.2.2.2 hη
  have hνac : ν ≪ μ := (Measure.absolutelyContinuous_of_le hν).trans Measure.smul_absolutelyContinuous
  have hm2 := heatAt_finiteSecondMoment μ hX.quadratic p hA hB hvol f hf0 hfs ht.le
  let : IsProbabilityMeasure (heatMeasure μ hX.quadratic t f) := by
    apply realDensity_probability μ (heatAt_integrable μ hX.quadratic t f hfi)
      ((Lp.coeFn_nonneg _).mpr (heatAt_nonneg μ hX.quadratic t f hf0))
    exact (heatAt_integral_eq_of_exponential_volume μ hX.quadratic p hA hB hvol f hf0 hfi ht.le).trans hfm
  have hs := heat_cutoff_dual_secant μ hX.quadratic hX.cd f hf0 ν hνac
    (finiteSecondMoment_of_ae_dist_le ν p hνS) ht hh hm2 ρ u η (hv.1.mono fun _ hx => hx.1)
    hη hφ.continuous hψ.continuous hφs hψs hu had hdual hE
  have hun : ‖u‖ ≤ 1000*(A+1)*Real.exp ((12*B+4)*R) := by
    have hb := SobolevSpace.linearRadiusPotential_norm_le μ hX.quadratic p hA hB hvol
      (by linarith : 1 ≤ 2*R) u hφ hφb hφS hu
    convert hb using 1
    congr 1
    congr 1
    ring
  change _ ≤ _+_ at hs ⊢
  calc
    _ ≤ _ := hs
    _ = (entropyPowerRate N (-(K*(wassersteinSq η ν).toReal/N))
        (Real.exp (-boltzmannEntropy μ η/N)) (Real.exp (-boltzmannEntropy μ ν/N)))+
        ‖u‖*(((2*(1+1/(t/2)))^2*‖f‖*h)+(h⁻¹+2)*‖ρ-heatSobolev μ hX.quadratic (t+h) (add_pos ht hh) f‖) := by ring
    _ ≤ _ := by
      apply add_le_add le_rfl
      apply mul_le_mul_of_nonneg_right hun
      positivity


end RegularPointCoordinates

end

end OAI
