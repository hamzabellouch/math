import OAI.Analysis.CircleDomains.Probability.ArcBoundaryMeasure
import OAI.Analysis.CircleDomains.Topology.CompactArcBoundary

namespace OAI

/-! The boundary starting law of the compact disk-arc family is the actual
pushed-forward law of the original arc starts. Gate inequalities and
atomlessness therefore pass to the mean construction without an extra
hypothesis about its boundary measure. -/

open Set Function Filter MeasureTheory
open scoped Topology

noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩
variable [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]

 theorem compact_startingLaw_eq_centered
    (A : Set C(PathTime, Sphere)) (K : Set C(PathTime, ℂ)) (η : ProbabilityMeasure A)
    (F : C(Sphere, ℂ)) (f : A → K) (hf : Measurable f)
    (hmap : ∀ γ : A, (f γ).val = F.comp γ.val) :
    compactArcStartingAngleLaw K (η.map f) =
      arcStartingAngleLaw (centeredArcLaw (η.map Subtype.val) F) := by
  apply ProbabilityMeasure.toMeasure_injective
  simp only [compactArcStartingAngleLaw, arcStartingAngleLaw, centeredArcLaw,
    ProbabilityMeasure.toMeasure_map]
  rw [Measure.map_map (measurable_compactArcStartingAngle K) hf,
    Measure.map_map measurable_arcStartingAngle F.continuous_postcomp.measurable,
    Measure.map_map (measurable_arcStartingAngle.comp F.continuous_postcomp.measurable)
      measurable_subtype_coe]
  apply Measure.map_congr
  exact Eventually.of_forall (fun γ => by simp only [Function.comp_apply, hmap γ, ContinuousMap.comp_apply])

 theorem compact_startingLaw_atomless
    (J : ℂ ≃ₜ ℂ) {b : Sphere} (hb : b ∈ ((↑) : ℂ → Sphere) '' jordanInterior J)
    (A : Set C(PathTime, Sphere)) (K : Set C(PathTime, ℂ)) (η : ProbabilityMeasure A)
    (hAS : A ⊆ terminalArcSet (((↑) : ℂ → Sphere) '' jordanInterior J) b)
    (F : C(Sphere, ℂ))
    (hF : EqOn F (centeredJordanCoordinate J b)
      (closure (((↑) : ℂ → Sphere) '' jordanInterior J)))
    (f : A → K) (hf : Measurable f) (hmap : ∀ γ : A, (f γ).val = F.comp γ.val)
    (havoid : ∀ x ∈ frontier (((↑) : ℂ → Sphere) '' jordanInterior J),
      pathHitProbability (η.map Subtype.val) x = 0) :
    NullSingletonClass (compactArcStartingAngleLaw K (η.map f) : Measure UnitAddCircle) := by
  rw [compact_startingLaw_eq_centered A K η F f hf hmap]
  apply centeredArcLaw_start_atomless J hb F hF (η.map Subtype.val) _ havoid
  rw [ProbabilityMeasure.toMeasure_map]
  apply (ae_map_iff measurable_subtype_coe.aemeasurable (measurableSet_terminalArcSet _ (OnePoint.isOpen_image_coe.mpr (jordanInterior_isOpen J)) b)).mpr
  exact Eventually.of_forall fun γ => hAS γ.property

omit [BorelSpace C(PathTime, Sphere)] in
 theorem compact_startingLaw_gate
    (J : ℂ ≃ₜ ℂ) {b : Sphere} (hb : b ∈ ((↑) : ℂ → Sphere) '' jordanInterior J)
    (A : Set C(PathTime, Sphere)) (K : Set C(PathTime, ℂ)) (η : ProbabilityMeasure A)
    (hAS : A ⊆ terminalArcSet (((↑) : ℂ → Sphere) '' jordanInterior J) b)
    (F : C(Sphere, ℂ))
    (hF : EqOn F (centeredJordanCoordinate J b)
      (closure (((↑) : ℂ → Sphere) '' jordanInterior J)))
    (f : A → K) (hf : Measurable f) (hmap : ∀ γ : A, (f γ).val = F.comp γ.val)
    (ψ : Sphere → ℝ) (hψ : Measurable ψ) (c : ℝ)
    (hgate : ∀ᵐ γ : A ∂(η : Measure A), c ≤ ψ (γ.val 0)) :
    ∀ᵐ θ : UnitAddCircle ∂(compactArcStartingAngleLaw K (η.map f) : Measure UnitAddCircle),
      c ≤ ψ (centeredJordanBoundary J b θ) := by
  have hm : Measurable (fun θ => ψ (centeredJordanBoundary J b θ)) :=
    hψ.comp (continuous_centeredJordanBoundary J hb).measurable
  have hs := measurableSet_le (measurable_const (a := c)) hm
  rw [compactArcStartingAngleLaw, ProbabilityMeasure.toMeasure_map]
  apply (ae_map_iff (measurable_compactArcStartingAngle K).aemeasurable hs).mpr
  rw [ProbabilityMeasure.toMeasure_map]
  apply (ae_map_iff hf.aemeasurable (hs.preimage (measurable_compactArcStartingAngle K))).mpr
  filter_upwards [hgate] with γ hγ
  change c ≤ ψ (centeredJordanBoundary J b (normalizedArgument ((f γ).val 0)))
  rw [hmap γ, ContinuousMap.comp_apply]
  change c ≤ ψ (centeredJordanBoundary J b (normalizedArgument (F (γ.val ⊥))))
  rw [hF (frontier_subset_closure (hAS γ.property).2.1),
    centeredJordanBoundary_inverse J hb (hAS γ.property).2.1]
  exact hγ

end CircleDomainRigidity

end

end OAI
