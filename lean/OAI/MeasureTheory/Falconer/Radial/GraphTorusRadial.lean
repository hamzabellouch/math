import OAI.MeasureTheory.Falconer.Graphs.GraphTorusArcLength
import OAI.MeasureTheory.Falconer.Radial.GraphRadialNormalization

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

theorem continuous_radial_interval_integral
    {X : Type*} [TopologicalSpace X] [FirstCountableTopology X] [LocallyCompactSpace X]
    {f : X → ℝ → ℂ} (hf : Continuous (Function.uncurry f)) {a b : ℝ} (hab : a ≤ b) :
    Continuous (fun x => ∫ t in a..b, f x t) := by
  have h := continuous_parametric_integral_of_continuous (μ := volume) (s := Icc a b) hf isCompact_Icc
  simpa only [intervalIntegral.integral_of_le hab, integral_Icc_eq_integral_Ioc] using h

theorem circle_pair_radial_interval_swap {F : ℝ → UnitCircle → UnitCircle → ℂ}
    (hF : Continuous (fun p : ℝ × (UnitCircle × UnitCircle) => F p.1 p.2.1 p.2.2))
    {a b : ℝ} (hab : a ≤ b) :
    (∫ t in a..b, ∫ u, ∫ v, F t u v ∂sourceArcLength ∂sourceArcLength) =
      ∫ u, ∫ v, (∫ t in a..b, F t u v) ∂sourceArcLength ∂sourceArcLength := by
  let μ := sourceArcLength.prod sourceArcLength
  have hi : Integrable (fun p : ℝ × (UnitCircle × UnitCircle) => F p.1 p.2.1 p.2.2)
      ((volume.restrict (Ioc a b)).prod μ) := by
    have hc : IntegrableOn (fun p : ℝ × (UnitCircle × UnitCircle) => F p.1 p.2.1 p.2.2)
        ((Icc a b) ×ˢ univ) (volume.prod μ) :=
      hF.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_univ)
    rw [show (volume.restrict (Ioc a b)).prod μ =
      (volume.prod μ).restrict ((Ioc a b) ×ˢ univ) by
        simpa only [Measure.restrict_univ] using Measure.prod_restrict (μ := volume) (ν := μ) (Ioc a b) univ]
    exact hc.mono_set (Set.prod_mono Ioc_subset_Icc_self (Subset.refl _))
  have hs (t : ℝ) : Integrable (fun p : UnitCircle × UnitCircle => F t p.1 p.2) μ := by
    have hc : Continuous (fun p : UnitCircle × UnitCircle => F t p.1 p.2) :=
      hF.comp (continuous_const.prodMk continuous_id)
    simpa only [integrableOn_univ] using
      (hc.continuousOn.integrableOn_compact (μ := μ) isCompact_univ)
  simp only [intervalIntegral.integral_of_le hab]
  calc
    _ = ∫ t in Ioc a b, ∫ p, F t p.1 p.2 ∂μ := by
      apply integral_congr_ae
      filter_upwards with t
      exact (integral_prod _ (hs t)).symm
    _ = ∫ p, (∫ t in Ioc a b, F t p.1 p.2) ∂μ := integral_integral_swap hi
    _ = _ := integral_prod _ hi.integral_prod_right

theorem sourceArcLength_pair_graph_radial_interval
    {F : ℝ → UnitCircle → UnitCircle → ℂ}
    (hF : Continuous (fun p : ℝ × (UnitCircle × UnitCircle) => F p.1 p.2.1 p.2.2))
    {a b : ℝ} (hab : a ≤ b) :
    (∫ t in a..b, ∫ u, ∫ v, F t u v ∂sourceArcLength ∂sourceArcLength) =
      ∫ z : ℝ, (Real.sqrt (1+z^2))⁻¹ • ∫ φ in (-Real.pi)..Real.pi,
        ∫ ρ in (2*a/Real.sqrt (1+z^2))..(2*b/Real.sqrt (1+z^2)),
          F (ρ*Real.sqrt (1+z^2)/2)
            (sourceUnitDirection (φ+Real.arctan z))
            (sourceUnitDirection (φ-Real.arctan z)) := by
  let G : UnitCircle → UnitCircle → ℂ := fun u v => ∫ t in a..b, F t u v
  have hc : Continuous (Function.uncurry G) :=
    continuous_radial_interval_integral (f := fun (p : UnitCircle × UnitCircle) t => F t p.1 p.2)
      (hF.comp continuous_swap) hab
  rw [circle_pair_radial_interval_swap hF hab]
  change (∫ u, ∫ v, G u v ∂sourceArcLength ∂sourceArcLength) = _
  rw [sourceArcLength_pair_graph_angles hc.measurable
    (hc.comp (continuous_sourceUnitDirection.prodMap continuous_sourceUnitDirection))]
  apply integral_congr_ae
  filter_upwards with z
  rw [← intervalIntegral.integral_smul, ← intervalIntegral.integral_smul]
  apply intervalIntegral.integral_congr
  intro φ hφ
  exact graph_radial_angular_density_interval
    (fun t => F t (sourceUnitDirection (φ+Real.arctan z))
      (sourceUnitDirection (φ-Real.arctan z))) z a b

end PlanarFalconer

end OAI
