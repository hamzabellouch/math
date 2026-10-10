import OAI.Analysis.CircleDomains.Topology.CenteredBoundary

namespace OAI

/-! The Stieltjes boundary integral is the integral over the starts of the
original spherical arcs, with no change of law hidden in the identity. -/

open Set Function Filter MeasureTheory
open scoped Topology ENNReal

noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩
variable [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]

theorem centeredArcLaw_start_atomless (K : ℂ ≃ₜ ℂ) {b : Sphere}
    (hb : b ∈ ((↑) : ℂ → Sphere) '' jordanInterior K)
    (F : C(Sphere, ℂ))
    (hF : EqOn F (centeredJordanCoordinate K b)
      (closure (((↑) : ℂ → Sphere) '' jordanInterior K)))
    (η : ProbabilityMeasure C(PathTime, Sphere))
    (hη : ∀ᵐ γ ∂(η : Measure C(PathTime, Sphere)),
      γ ∈ terminalArcSet (((↑) : ℂ → Sphere) '' jordanInterior K) b)
    (havoid : ∀ x ∈ frontier (((↑) : ℂ → Sphere) '' jordanInterior K),
      pathHitProbability η x = 0) :
    NullSingletonClass (arcStartingAngleLaw (centeredArcLaw η F) : Measure UnitAddCircle) := by
  apply diskStartingAngleLaw_atomless
  · rw [centeredArcLaw, ProbabilityMeasure.toMeasure_map]
    apply (ae_map_iff F.continuous_postcomp.measurable.aemeasurable
      (measurableSet_eq_fun ((continuous_eval_const 0).norm.measurable) measurable_const)).mpr
    exact hη.mono fun _ h => (centeredJordanPath_mem K hb F hF h).2.1
  · intro z hz
    let x := centeredJordanBoundary K b (normalizedArgument z)
    have hx : x ∈ frontier (((↑) : ℂ → Sphere) '' jordanInterior K) :=
      centeredJordanBoundary_mem_frontier K hb _
    have he : centeredJordanCoordinate K b x = z := by
      rw [centeredJordanCoordinate_boundary K hb, standardCirclePoint_normalizedArgument hz]
    rw [← he, centeredArcLaw_hit K hb F hF η hη (frontier_subset_closure hx)]
    exact havoid x hx

def arcBoundaryStieltjes (K : ℂ ≃ₜ ℂ) {b : Sphere}
    (hb : b ∈ ((↑) : ℂ → Sphere) '' jordanInterior K)
    (F : C(Sphere, ℂ))
    (hF : EqOn F (centeredJordanCoordinate K b)
      (closure (((↑) : ℂ → Sphere) '' jordanInterior K)))
    (η : ProbabilityMeasure C(PathTime, Sphere))
    (hη : ∀ᵐ γ ∂(η : Measure C(PathTime, Sphere)),
      γ ∈ terminalArcSet (((↑) : ℂ → Sphere) '' jordanInterior K) b)
    (havoid : ∀ x ∈ frontier (((↑) : ℂ → Sphere) '' jordanInterior K),
      pathHitProbability η x = 0) : StieltjesFunction ℝ := by
  letI := centeredArcLaw_start_atomless K hb F hF η hη havoid
  exact boundaryIndexStieltjes (arcStartingAngleLaw (centeredArcLaw η F))

theorem arcBoundaryStieltjes_unit_mass (K : ℂ ≃ₜ ℂ) {b : Sphere}
    (hb : b ∈ ((↑) : ℂ → Sphere) '' jordanInterior K)
    (F : C(Sphere, ℂ))
    (hF : EqOn F (centeredJordanCoordinate K b)
      (closure (((↑) : ℂ → Sphere) '' jordanInterior K)))
    (η : ProbabilityMeasure C(PathTime, Sphere))
    (hη : ∀ᵐ γ ∂(η : Measure C(PathTime, Sphere)),
      γ ∈ terminalArcSet (((↑) : ℂ → Sphere) '' jordanInterior K) b)
    (havoid : ∀ x ∈ frontier (((↑) : ℂ → Sphere) '' jordanInterior K),
      pathHitProbability η x = 0) (t : ℝ) :
    (arcBoundaryStieltjes K hb F hF η hη havoid).measure (Ioc t (t + 1)) = 1 := by
  let := centeredArcLaw_start_atomless K hb F hF η hη havoid
  exact boundaryIndexStieltjes_unit_mass _ t

theorem arcBoundaryStieltjes_integral (K : ℂ ≃ₜ ℂ) {b : Sphere}
    (hb : b ∈ ((↑) : ℂ → Sphere) '' jordanInterior K)
    (F : C(Sphere, ℂ))
    (hF : EqOn F (centeredJordanCoordinate K b)
      (closure (((↑) : ℂ → Sphere) '' jordanInterior K)))
    (η : ProbabilityMeasure C(PathTime, Sphere))
    (hη : ∀ᵐ γ ∂(η : Measure C(PathTime, Sphere)),
      γ ∈ terminalArcSet (((↑) : ℂ → Sphere) '' jordanInterior K) b)
    (havoid : ∀ x ∈ frontier (((↑) : ℂ → Sphere) '' jordanInterior K),
      pathHitProbability η x = 0) (φ : C(Sphere, ℝ)) :
    ∫ t in Ioc (0 : ℝ) 1, φ (centeredJordanBoundary K b (t : UnitAddCircle))
        ∂(arcBoundaryStieltjes K hb F hF η hη havoid).measure =
      ∫ γ, φ (γ 0) ∂(η : Measure C(PathTime, Sphere)) := by
  let := centeredArcLaw_start_atomless K hb F hF η hη havoid
  have hc := φ.continuous.comp (continuous_centeredJordanBoundary K hb)
  change ∫ t in Ioc (0 : ℝ) 1, φ (centeredJordanBoundary K b (t : UnitAddCircle))
      ∂(boundaryIndexStieltjes (arcStartingAngleLaw (centeredArcLaw η F))).measure = _
  rw [boundaryIndexStieltjes_integral, ProbabilityMeasure.toMeasure_map]
  have hreal : Continuous (fun t : ℝ => φ (centeredJordanBoundary K b (t : UnitAddCircle))) :=
    hc.comp (AddCircle.continuous_mk' (1 : ℝ))
  rw [integral_map measurable_unitCircleCut.aemeasurable hreal.aestronglyMeasurable]
  simp only [unitCircleCut, AddCircle.coe_equivIco]
  have hcircle : Continuous (fun θ => φ (centeredJordanBoundary K b θ)) := hc
  rw [arcStartingAngleLaw, ProbabilityMeasure.toMeasure_map,
    integral_map measurable_arcStartingAngle.aemeasurable hcircle.aestronglyMeasurable]
  have hpath : Measurable (fun γ : C(PathTime, ℂ) =>
      φ (centeredJordanBoundary K b (normalizedArgument (γ 0)))) :=
    hcircle.measurable.comp measurable_arcStartingAngle
  rw [centeredArcLaw, ProbabilityMeasure.toMeasure_map,
    integral_map F.continuous_postcomp.measurable.aemeasurable hpath.aestronglyMeasurable]
  apply integral_congr_ae
  filter_upwards [hη] with γ hγ
  change φ (centeredJordanBoundary K b (normalizedArgument (F (γ ⊥)))) = φ (γ ⊥)
  rw [hF (frontier_subset_closure hγ.2.1), centeredJordanBoundary_inverse K hb hγ.2.1]

end CircleDomainRigidity

end

end OAI
