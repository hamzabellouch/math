import OAI.Analysis.CircleDomains.Rigidity.ExactTraceTests
import OAI.Analysis.CircleDomains.Transfer.RetainedOriginalTest

namespace OAI

/-! A whole finite list has simultaneous exact-trace replacements. The
original pair-null condition passes unchanged to these actual coordinates,
and a retained model of them is a Sobolev model of every original test. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩
variable [MeasurableSpace C(PathTime, Sphere)]

 theorem exists_exact_trace_family
    (d : PathCodeData Sphere Sphere) (hG : IsOpen d.physicalDomain)
    (he : ∀ x : d.physicalDomain, (d.domainEquiv x).val = x.val)
    (hne : (physicalPlaneDomain d.physicalDomain)ᶜ.Nonempty)
    {m : ℕ} (u : Fin m → EuclideanPlane → ℝ)
    (hu : ∀ i, Continuous (u i)) (hs : ∀ i, HasCompactSupport (u i))
    (hunit : ∀ i x, u i x ∈ Icc 0 1)
    (H : ∀ i, DeGiorgi.MemW1pWitness 2 (u i) (physicalPlaneDomain d.physicalDomain))
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ T : ∀ i, ExactTraceTest d (u i), ∀ i j,
      eLpNorm (fun x => (T i).error.weakGrad x j) 2 volume < ε := by
  classical
  choose T hT using fun i => exists_exact_trace_test d hG he hne (hu i) (hs i) (hunit i) (H i) hε
  exact ⟨T, hT⟩

 theorem exactTraceFamily_pair_null
    {d : PathCodeData Sphere Sphere} {m : ℕ} {u : Fin m → EuclideanPlane → ℝ}
    (T : ∀ i, ExactTraceTest d (u i)) (hB : d.dust ⊆ d.physicalDomainᶜ)
    (hpair : ∀ i j, i ≠ j → volume
      ((fun p => (sphereFromPlaneFunction (u i) p, sphereFromPlaneFunction (u j) p)) '' d.dust) = 0) :
    ∀ i j, i ≠ j → volume
      ((fun p => ((T i).coordinate.quotient p, (T j).coordinate.quotient p)) '' d.dust) = 0 := by
  intro i j hij
  have he : (fun p => ((T i).coordinate.quotient p, (T j).coordinate.quotient p)) '' d.dust =
      (fun p => (sphereFromPlaneFunction (u i) p, sphereFromPlaneFunction (u j) p)) '' d.dust := by
    apply image_congr
    intro p hp
    exact Prod.ext ((T i).trace_on_sphere (hB hp)) ((T j).trace_on_sphere (hB hp))
  rw [he]
  exact hpair i j hij

namespace RetainedRealCircleModel

 theorem exactTraceTest_original_witness
    (harea : ExteriorCoefficientAreaTheorem) (hsch : PlanarSchoenflies)
    {d : PathCodeData Sphere Sphere} (hG : IsOpen d.physicalDomain)
    (hc : ∀ q p, p ∈ connectedComponentIn d.physicalDomainᶜ q → p = q)
    {m : ℕ} {u : Fin m → EuclideanPlane → ℝ} (T : ∀ i, ExactTraceTest d (u i))
    (R : RetainedRealCircleModel d id (fun i => (T i).coordinate))
    (hu : ∀ i, Continuous (u i)) (hs : ∀ i, HasCompactSupport (u i)) (i : Fin m) :
    ∃ H : DeGiorgi.MemW1pWitness 2
      (fun x => R.projectedPlaneFunction hG (u i) (planeSphere x)) univ,
      ∀ j : Fin 2, ∀ᵐ x ∂volume, x ∉ physicalPlaneDomain
        (extendAtInfinity R.limit.function '' d.physicalDomain) →
          H.weakGrad x j = 0 :=
  R.original_test_witness harea hsch hG hc i (hu i) (hs i) (T i).continuous (T i).compact
    (T i).coordinate_eq (T i).trace (T i).error

end RetainedRealCircleModel
end CircleDomainRigidity

end

end OAI
