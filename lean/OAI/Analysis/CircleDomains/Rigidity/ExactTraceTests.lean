import OAI.Analysis.CircleDomains.Topology.PrescribedPlaneCoordinate

namespace OAI

/-! Actual smooth replacements of the original scalar tests. Their full
boundary traces, continuous representatives and global Sobolev errors
are retained together for the circle-model construction. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩
variable [MeasurableSpace C(PathTime, Sphere)]

structure ExactTraceTest (d : PathCodeData Sphere Sphere) (u : EuclideanPlane → ℝ) where
  smooth : EuclideanPlane → ℝ
  continuous : Continuous smooth
  compact : HasCompactSupport smooth
  contDiff : ContDiffOn ℝ (⊤ : ℕ∞) smooth (physicalPlaneDomain d.physicalDomain)
  unit : ∀ x, smooth x ∈ Icc 0 1
  partial_memLp : ∀ i : Fin 2, MemLp (fun x => fderiv ℝ smooth x (EuclideanSpace.single i 1)) 2
    (volume.restrict (physicalPlaneDomain d.physicalDomain))
  trace : EqOn smooth u (physicalPlaneDomain d.physicalDomain)ᶜ
  coordinate : PhysicalRealCoordinate d id
  coordinate_eq : coordinate.quotient = sphereFromPlaneFunction smooth
  coordinate_continuous : Continuous coordinate.quotient
  error : DeGiorgi.MemW1pWitness 2 (fun x => u x - smooth x) univ

 theorem exists_exact_trace_test
    (d : PathCodeData Sphere Sphere) (hG : IsOpen d.physicalDomain)
    (he : ∀ x : d.physicalDomain, (d.domainEquiv x).val = x.val)
    (hne : (physicalPlaneDomain d.physicalDomain)ᶜ.Nonempty)
    {u : EuclideanPlane → ℝ} (hu : Continuous u) (hs : HasCompactSupport u)
    (hunit : ∀ x, u x ∈ Icc 0 1)
    (H : DeGiorgi.MemW1pWitness 2 u (physicalPlaneDomain d.physicalDomain))
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ T : ExactTraceTest d u, ∀ i : Fin 2,
      eLpNorm (fun x => T.error.weakGrad x i) 2 volume < ε := by
  let Ω : TopologicalSpace.Opens EuclideanPlane :=
    ⟨physicalPlaneDomain d.physicalDomain, isOpen_physicalPlaneDomain hG⟩
  obtain ⟨v, hvc, hvs, hvsm, hvunit, hvtrace, hvgrad⟩ :=
    exists_exact_trace_smoothing Ω hne hu hs hunit H hε
  let V := smoothPlaneSobolevWitness Ω.isOpen (hvsm.of_le (by simp))
    ((hvc.memLp_of_hasCompactSupport hvs).restrict Ω) (fun i => (hvgrad i).1)
  let D := H.sub V
  have hz : ∀ x ∉ (Ω : Set EuclideanPlane), u x - v x = 0 := by
    intro x hx
    rw [hvtrace hx, sub_self]
  let K := zeroTraceWitness Ω.isOpen (hu.sub hvc) (hs.sub hvs) hz D
  obtain ⟨Q, hQ, hQc, _⟩ := exists_prescribed_plane_coordinate d hG he v hvc hvs hvsm hvunit
    (fun i => (hvgrad i).1)
  refine ⟨⟨v, hvc, hvs, hvsm, hvunit, (fun i => (hvgrad i).1), hvtrace, Q, hQ, hQc, K⟩, ?_⟩
  intro i
  change eLpNorm (fun x => K.weakGrad x i) 2 volume < ε
  rw [zeroTraceWitness_component_eLpNorm]
  have hd : (fun x => D.weakGrad x i) =
      -(fun x => fderiv ℝ v x (EuclideanSpace.single i 1) - H.weakGrad x i) := by
    funext x
    change H.weakGrad x i + (-1) * fderiv ℝ v x (EuclideanSpace.single i 1) = _
    simp only [Pi.neg_apply]
    ring
  rw [hd, eLpNorm_neg]
  exact (hvgrad i).2

namespace ExactTraceTest
variable {d : PathCodeData Sphere Sphere} {u : EuclideanPlane → ℝ}
  (T : ExactTraceTest d u)

 theorem trace_on_sphere {p : Sphere} (hp : p ∈ d.physicalDomainᶜ) :
    T.coordinate.quotient p = sphereFromPlaneFunction u p := by
  change p ∉ d.physicalDomain at hp
  rw [T.coordinate_eq]
  cases p using OnePoint.rec with
  | infty => simp [sphereFromPlaneFunction]
  | coe z =>
    simp only [sphereFromPlaneFunction_coe]
    apply T.trace
    change (complexPlaneCoordinates (complexPlaneCoordinates.symm z) : Sphere) ∉ d.physicalDomain
    simpa only [ContinuousLinearEquiv.apply_symm_apply] using hp

end ExactTraceTest
end CircleDomainRigidity

end

end OAI
