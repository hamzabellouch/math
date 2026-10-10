import OAI.Analysis.CircleDomains.Topology.SphereJordanCoordinates
import OAI.Analysis.CircleDomains.Probability.CountableCodedCollarLaws

namespace OAI

/-! The coded-law countability argument on an actual spherical Jordan collar.
Its disk coordinates and boundary probability transport are constructed here. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩
variable [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]

theorem countable_of_small_jordan_collar_meetings {I : Type*} [LinearOrder I]
    (hcross : UnitDiskAlternatingContinua) (S : Set I) (K : ℂ ≃ₜ ℂ)
    (Ω : I → Type*) [∀ i, MeasurableSpace (Ω i)]
    (μ : ∀ i, ProbabilityMeasure (Ω i)) (a : ∀ i, Ω i → C(PathTime, Sphere))
    (ha : ∀ i, Measurable (a i)) (p : I → Sphere)
    (hp : ∀ i ∈ S, p i ∈ ((↑) : ℂ → Sphere) '' jordanInterior K)
    (hends : ∀ i ∈ S, ∀ᵐ z ∂(μ i : Measure (Ω i)),
      a i z ⊥ ∉ ((↑) : ℂ → Sphere) '' jordanInterior K ∧ a i z ⊤ = p i)
    (hatom : ∀ i ∈ S, NullSingletonClass
      (lastEntryLaw ((μ i).map (a i)) (((↑) : ℂ → Sphere) '' jordanInterior K) : Measure Sphere))
    (hsmall : ∀ i ∈ S, ∀ j ∈ S, i < j →
      4 * ((μ i : Measure (Ω i)).prod (μ j : Measure (Ω j)))
        {z | ∃ x ∈ ((↑) : ℂ → Sphere) '' jordanInterior K,
          x ∈ range (a i z.1) ∧ x ∈ range (a j z.2)} < (1 / 10 : ℝ≥0∞) ^ 4) :
    S.Countable := by
  let V := ((↑) : ℂ → Sphere) '' jordanInterior K
  have hV : IsOpen V := OnePoint.isOpen_image_coe.mpr (jordanInterior_isOpen K)
  let c := sphereJordanBoundary K
  let hc := measurableEmbedding_sphereJordanBoundary K
  apply countable_of_uniformly_small_coded_collar_meetings hcross S V hV
    (sphereJordanCoordinate K) (sphereJordanCoordinate_continuousOn K)
    (sphereJordanCoordinate_injOn K) (sphereJordanCoordinate_mapsTo K)
    hc.invFun hc.measurable_invFun (sphereJordanCoordinate_boundary_inverse K)
    Ω μ a ha p hp hends _ hsmall
  intro i hi
  have := hatom i hi
  apply lastEntryCircleLaw_nullSingletonClass ((μ i).map (a i)) V c hc
  rw [range_sphereJordanBoundary]
  apply lastEntryLaw_boundary_support _ V hV
  change ∀ᵐ γ ∂((μ i : Measure (Ω i)).map (a i)), γ ⊥ ∉ V ∧ γ ⊤ ∈ V
  apply (ae_map_iff (ha i).aemeasurable
    (((continuous_eval_const ⊥).measurable hV.measurableSet).compl.inter
      ((continuous_eval_const ⊤).measurable hV.measurableSet))).mpr
  filter_upwards [hends i hi] with z hz
  refine ⟨hz.1, ?_⟩
  change (a i z) ⊤ ∈ V
  rw [hz.2]
  exact hp i hi

end CircleDomainRigidity

end

end OAI
