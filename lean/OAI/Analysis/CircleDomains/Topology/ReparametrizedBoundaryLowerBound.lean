import OAI.Analysis.CircleDomains.Topology.ReparametrizedBoundaryPairing
import OAI.Analysis.CircleDomains.Topology.MeanBoundaryCollar
import OAI.Analysis.CircleDomains.Topology.CompactArcBoundary

namespace OAI

/-! A positive starting-point law gives the lower bound on any sufficiently
close smooth inward circuit. The boundary angle parameter need not be smooth. -/

open Set Function Filter MeasureTheory
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

 theorem smooth_reparametrized_boundary_integral_lower_bound
    (β : ProbabilityMeasure UnitAddCircle) [NullSingletonClass (β : Measure UnitAddCircle)]
    (q : ℝ ≃o ℝ) (hq0 : q 0 = 0) (hq1 : q 1 = 1)
    (φ dφ u du : ℝ → ℝ)
    (hφ : ∀ x, HasDerivAt φ (dφ x) x) (hdφ : Continuous dφ) (hφperiod : φ 1 = φ 0)
    (hu : ∀ x ∈ uIcc (0 : ℝ) 1, HasDerivAt u (du x) x)
    (hdu : IntervalIntegrable du volume 0 1) (huperiod : u 1 = u 0 + 1)
    (δ c : ℝ) (hclose : ∀ x ∈ Icc (0 : ℝ) 1, |u x - boundaryIndexMean β (q x)| ≤ δ)
    (hpositive : ∀ᵐ a : UnitAddCircle ∂(β : Measure UnitAddCircle),
      c ≤ φ (q.symm (unitCircleCut a))) :
    c ≤ (∫ x in (0 : ℝ)..1, φ x * du x) + δ * ∫ x in (0 : ℝ)..1, |dφ x| := by
  have hφc : Continuous φ := continuous_iff_continuousAt.mpr fun x => (hφ x).continuousAt
  obtain ⟨C, hC⟩ := (isCompact_Icc : IsCompact (Icc (0 : ℝ) 1)).exists_bound_of_continuousOn
    hφc.continuousOn
  have hi : Integrable (fun a : UnitAddCircle => φ (q.symm (unitCircleCut a)))
      (β : Measure UnitAddCircle) := by
    apply Integrable.of_bound (hφc.measurable.comp
      (q.symm.continuous.measurable.comp measurable_unitCircleCut)).aestronglyMeasurable C
    apply Eventually.of_forall
    intro a
    apply hC
    constructor
    · apply q.le_iff_le.mp
      simpa only [Function.comp_apply, hq0, q.apply_symm_apply] using (unitCircleCut_mem a).1
    · apply q.le_iff_le.mp
      simpa only [Function.comp_apply, hq1, q.apply_symm_apply] using (unitCircleCut_mem a).2.le
  have hc : c ≤ ∫ a, φ (q.symm (unitCircleCut a)) ∂(β : Measure UnitAddCircle) := by
    calc
      c = ∫ _a : UnitAddCircle, c ∂(β : Measure UnitAddCircle) := by simp
      _ ≤ _ := integral_mono_ae (integrable_const c) hi hpositive
  have huc : ContinuousOn u (Icc (0 : ℝ) 1) := by
    intro x hx
    exact (hu x (by simpa only [uIcc_of_le zero_le_one] using hx)).continuousAt.continuousWithinAt
  have hvperiod : boundaryIndexMean β (q 1) = boundaryIndexMean β (q 0) + 1 := by
    simpa only [hq0, hq1, zero_add] using boundaryIndexMean_add_one β 0
  have hsame : u 1 - u 0 = (boundaryIndexMean β ∘ q) 1 - (boundaryIndexMean β ∘ q) 0 := by
    simp only [Function.comp_apply]
    rw [huperiod, hvperiod]
    ring
  have hs := liftedBoundaryPairing_stability φ dφ u (boundaryIndexMean β ∘ q) hφperiod hsame
    huc ((continuous_boundaryIndexMean β).comp q.continuous).continuousOn
    (hdφ.intervalIntegrable 0 1) δ hclose
  rw [liftedBoundaryPairing_eq_integral φ dφ u du (fun x _ => hφ x) hu
    (hdφ.intervalIntegrable 0 1) hdu,
    liftedBoundaryPairing_reparametrized_boundaryIndexMean β q hq0 hq1 φ dφ hφ hdφ hφperiod] at hs
  linarith [neg_abs_le ((∫ x in (0 : ℝ)..1, φ x * du x) -
    ∫ a, φ (q.symm (unitCircleCut a)) ∂(β : Measure UnitAddCircle))]

 theorem exists_mean_collar_boundary_lower_bound
    (hsch : PlanarSchoenflies) (hsep : UnitDiskCrosscutSeparation)
    (K : Set C(PathTime, ℂ)) (hK : IsCompact K) (hKS : K ⊆ diskTerminalArcSet)
    (η : ProbabilityMeasure K)
    [NullSingletonClass (compactArcStartingAngleLaw K η : Measure UnitAddCircle)]
    (q : ℝ ≃o ℝ) (hq0 : q 0 = 0) (hq1 : q 1 = 1)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ (L : ℝ → ClosedUpperHalfPlane) (φ dφ u du : ℝ → ℝ),
      (∀ x, HasDerivAt φ (dφ x) x) → Continuous dφ → φ 1 = φ 0 →
      (∀ x ∈ uIcc (0 : ℝ) 1, HasDerivAt u (du x) x) →
      IntervalIntegrable du volume 0 1 → u 1 = u 0 + 1 →
      (∀ x ∈ Icc (0 : ℝ) 1, dist (L x).val (q x : ℂ) < δ) →
      (∀ x ∈ Icc (0 : ℝ) 1, |u x - meanGeometricIndex hsch K hKS η (L x)| ≤ ε) →
      ∀ c : ℝ, (∀ᵐ a : UnitAddCircle ∂(compactArcStartingAngleLaw K η : Measure UnitAddCircle),
        c ≤ φ (q.symm (unitCircleCut a))) →
      c ≤ (∫ x in (0 : ℝ)..1, φ x * du x) + (2 * ε) * ∫ x in (0 : ℝ)..1, |dφ x| := by
  obtain ⟨δ, hδ, hd⟩ := mean_uniform_boundary_approximation_of_dist hsch hsep K hK hKS η
    (fun x _ => compactArc_boundary_avoidance K hKS η x) hε
  refine ⟨δ, hδ, ?_⟩
  intro L φ dφ u du hφ hdφ hφperiod hu hdu huperiod hL herror c hpositive
  apply smooth_reparametrized_boundary_integral_lower_bound
    (compactArcStartingAngleLaw K η) q hq0 hq1 φ dφ u du hφ hdφ hφperiod
    hu hdu huperiod (2 * ε) c ?_ hpositive
  intro x hx
  have hqx : q x ∈ Icc (0 : ℝ) 1 := by
    constructor
    · simpa only [hq0] using q.monotone hx.1
    · simpa only [hq1] using q.monotone hx.2
  have hb := hd (q x) hqx (L x) (hL x hx)
  have he := herror x hx
  calc
    |u x - boundaryIndexMean (compactArcStartingAngleLaw K η) (q x)| =
        |(u x - meanGeometricIndex hsch K hKS η (L x)) +
          (meanGeometricIndex hsch K hKS η (L x) -
            boundaryIndexMean (compactArcStartingAngleLaw K η) (q x))| := by congr 1; ring
    _ ≤ |u x - meanGeometricIndex hsch K hKS η (L x)| +
        |meanGeometricIndex hsch K hKS η (L x) -
          boundaryIndexMean (compactArcStartingAngleLaw K η) (q x)| := abs_add_le _ _
    _ ≤ 2 * ε := by linarith

end CircleDomainRigidity

end

end OAI
