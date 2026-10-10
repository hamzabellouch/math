import OAI.Analysis.CircleDomains.Topology.OpenMeanCorrection
import OAI.Analysis.CircleDomains.Selection.PerturbedMeanPeriodGraph
import OAI.Analysis.CircleDomains.Selection.MappedPointAvoidance
import OAI.Analysis.CircleDomains.Sobolev.CircleComplexEnergy
import OAI.Analysis.CircleDomains.Sobolev.PeriodBranchPhysicalEnergy

namespace OAI

/-! A single constructed mean-period coordinate retains its real atlas,
closed masked levels, vanishing correction, and actual smooth physical
representative. The analytic and topological data come from one law. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology NNReal

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩

structure SmoothMeanPeriodData
    (hsch : PlanarSchoenflies) (K : Set C(PathTime, ℂ)) (hKS : K ⊆ diskTerminalArcSet)
    (η : ProbabilityMeasure K) (F : C(Sphere, ℂ))
    (G U S M : Set Sphere) (b : Sphere) (π : Sphere → Sphere) where
  Index : Type
  countableIndex : Countable Index
  patch : Index → Set Sphere
  angle : Index → ℝ
  bound : Index → ℝ
  branch : Index → Sphere → ℝ
  error : Sphere → ℝ
  physical : ℂ → UnitAddCircle
  euclidean : EuclideanPlane → UnitAddCircle
  physical_eq : physical = euclidean ∘ complexPlaneCoordinates.symm
  cover : S ⊆ ⋃ i, patch i
  patch_open : ∀ i, IsOpen (patch i)
  patch_closure : ∀ i, closure (patch i) ⊆ S
  log_continuous : ∀ i, ContinuousOn
    (fun x => logarithmicCutChart (angle i) (F x)) (closure (patch i))
  bounded : ∀ i x, |branch i x| ≤ bound i
  continuous : ∀ i, ContinuousOn (branch i) (U ∩ patch i)
  branch_value : ∀ i x, x ∈ patch i → branch i x =
    meanGeometricIndex hsch K hKS η
      (upperHalfPlaneClamp (logarithmicCutChart (angle i) (F x))) + error x
  transition : ∀ i j x, x ∈ patch i → x ∈ patch j →
    ∃ k : ℤ, branch j =ᶠ[𝓝[U] x] fun y => branch i y + k
  closed : IsClosed (periodBandGraph U M b patch branch)
  domain_value : ∀ x ∈ U, ∀ θ : UnitAddCircle,
    (x, θ) ∈ periodBandGraph U M b patch branch ↔
      x ∈ M ∧ diskMeanCircle hsch K hKS η (F x) + (error x : UnitAddCircle) = θ
  error_continuous : ContinuousOn error (U ∩ S)
  error_bound : ∀ x, |error x| ≤ 1
  error_vanishes : ∀ x ∈ Uᶜ, Tendsto error (𝓝 x) (𝓝 0)
  physical_smooth : FiniteTransfer.SmoothCircleOn physical
    (((↑) : ℂ → Sphere) ⁻¹' G ∩ (fun z : ℂ => π (z : Sphere)) ⁻¹' S)
  physical_value : ∀ z : ℂ, (z : Sphere) ∈ G → π (z : Sphere) ∈ S →
    physical z = diskMeanCircle hsch K hKS η (F (π (z : Sphere))) +
      (error (π (z : Sphere)) : UnitAddCircle)
  physical_energy : (∫⁻ z in ((↑) : ℂ → Sphere) ⁻¹' G ∩
    (fun z : ℂ => π (z : Sphere)) ⁻¹' S,
    ENNReal.ofReal ‖FiniteTransfer.circleFDeriv physical z‖ ^ 2) < ∞
  branch_smooth : ∀ i, ContDiffOn ℝ 1 (fun z : ℂ => branch i (π (z : Sphere)))
    (((↑) : ℂ → Sphere) ⁻¹' G ∩ (fun z : ℂ => π (z : Sphere)) ⁻¹' patch i)
  branch_energy : ∀ i, (∫⁻ z in ((↑) : ℂ → Sphere) ⁻¹' G ∩
    (fun z : ℂ => π (z : Sphere)) ⁻¹' patch i,
    ENNReal.ofReal ‖fderiv ℝ (fun z : ℂ => branch i (π (z : Sphere))) z‖ ^ 2) < ∞

variable [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]

theorem exists_smooth_mean_period_data
    (hsch : PlanarSchoenflies) (hsep : UnitDiskCrosscutSeparation)
    (hcoarea : PlanarLipschitzFiberCoarea)
    {G U S M : Set Sphere} (e : G ≃ₜ U) (hG : IsOpen G) (hU : IsOpen U)
    (hS : IsOpen S) (hM : IsClosed M) (b : Sphere) (hbS : b ∉ S) (hbU : b ∉ U)
    (hMS : M \ {b} ⊆ S) (y₀ : Sphere)
    (π : Sphere → Sphere) (hπ : Continuous π) (he : ∀ y : G, (e y).val = π y.val)
    (hinf : π OnePoint.infty ∉ S)
    (A : Set C(PathTime, Sphere)) (hA : ∀ γ ∈ A, Injective γ)
    (η : ProbabilityMeasure A) (hfinite : ∀ γ ∈ A, physicalDomainLength e y₀ γ < ∞)
    (g : Sphere → ℝ≥0∞) (hg : Measurable g)
    (hocc : meanPhysicalOccupation e y₀ (η.map Subtype.val) = sphericalArea.withDensity g)
    (henergy : (∫⁻ p, g p ^ 2 ∂sphericalArea) < ∞)
    (K : Set C(PathTime, ℂ)) (hK : IsCompact K) (hKS : K ⊆ diskTerminalArcSet)
    (F : C(Sphere, ℂ)) (f : A → K) (hf : Measurable f)
    (hmap : ∀ γ : A, (f γ).val = F.comp γ.val)
    (B : ℝ≥0) (hB : LipschitzOnWith B finiteCoord
      (((↑) : ℂ → Sphere) '' (((↑) : ℂ → Sphere) ⁻¹' G ∩
        (fun z : ℂ => π (z : Sphere)) ⁻¹' S)))
    (h0 : ∀ x ∈ S, F x ≠ 0) (h1 : ∀ x ∈ S, ‖F x‖ ≤ 1)
    (hF : ∀ γ : A, InjOn F (range γ.val ∪ S)) (hinj : InjOn F S)
    (hmiss : ∀ x ∈ U ∩ S, ∀ᵐ γ : A ∂(η : Measure A), x ∉ range γ.val)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ Q : SmoothMeanPeriodData hsch K hKS (η.map f) F G U S M b π,
      (∀ x, |Q.error x| ≤ dustSmoothingTolerance id Uᶜ δ x) ∧
      ∀ i : Fin 2,
        MemLp (fun x => FiniteTransfer.circleFDeriv Q.euclidean x (EuclideanSpace.single i 1))
          2 (volume.restrict (planeSphere ⁻¹' (G ∩ π ⁻¹' S))) ∧
        eLpNorm (fun x => FiniteTransfer.circleFDeriv Q.euclidean x (EuclideanSpace.single i 1))
          2 (volume.restrict (planeSphere ⁻¹' (G ∩ π ⁻¹' S))) ≤ ε +
          eLpNorm (fun x : EuclideanPlane => (sliceChartDensity B g ⟨x 0, x 1⟩).toReal)
            2 (volume.restrict (planeSphere ⁻¹' (G ∩ π ⁻¹' S))) := by
  obtain ⟨w, R, hw, hRc, hRtol, hRb, hRlim, hwp, hwgrad⟩ := exists_open_mean_circle_correction
    hsch hsep hcoarea e hG hU hS y₀ π hπ he hinf ⟨b, hbU⟩ A hA η hfinite
    g hg hocc henergy K hK hKS F f hf hmap B hB h0 h1 hF hinj hmiss δ hδ hδ1 hε
  have hmissK : ∀ x ∈ U ∩ S, ∀ᵐ γ : K ∂((η.map f : ProbabilityMeasure K) : Measure K),
      F x ∉ range γ.val := by
    intro x hx
    exact mapped_arc_point_avoidance A K η F f hf hmap x
      (fun γ => (hF γ).mono (union_subset_union Subset.rfl (singleton_subset_iff.mpr hx.2)))
      (hmiss x hx)
  obtain ⟨I, hI, V, a, C, u, hcover, hV, hlog, hbound, hcont, hu, htrans, hclosed, hdomain⟩ :=
    exists_perturbed_mean_period_graph hsch hsep K hK hKS (η.map f) F S U M hS hU hM
      b hbS hbU hMS h0 h1 hmissK R hRc hRb
  let Ω : Set EuclideanPlane := planeSphere ⁻¹' (G ∩ π ⁻¹' S)
  have hΩ : IsOpen Ω := (hG.inter (hS.preimage hπ)).preimage continuous_planeSphere
  obtain ⟨hwc, hwE⟩ := smooth_circle_complex_energy_finite hΩ w hw (fun i => (hwgrad i).1)
  let v := w ∘ complexPlaneCoordinates.symm
  have hv (z : ℂ) (hzG : (z : Sphere) ∈ G) (hzS : π (z : Sphere) ∈ S) :
      v z = diskMeanCircle hsch K hKS (η.map f) (F (π (z : Sphere))) +
        (R (π (z : Sphere)) : UnitAddCircle) := by
    have hplane : planeSphere (complexPlaneCoordinates.symm z) = (z : Sphere) :=
      congrArg ((↑) : ℂ → Sphere) (complexPlaneCoordinates.apply_symm_apply z)
    have hp : complexPlaneCoordinates.symm z ∈ Ω := by
      change planeSphere (complexPlaneCoordinates.symm z) ∈ G ∩ π ⁻¹' S
      rw [hplane]
      exact ⟨hzG, hzS⟩
    simpa only [v, Function.comp_apply, hplane] using hwp _ hp
  have hDom : complexPlaneCoordinates.symm ⁻¹' Ω =
      ((↑) : ℂ → Sphere) ⁻¹' G ∩ (fun z : ℂ => π (z : Sphere)) ⁻¹' S := by
    ext z
    change planeSphere (complexPlaneCoordinates.symm z) ∈ G ∩ π ⁻¹' S ↔ _
    have hp : planeSphere (complexPlaneCoordinates.symm z) = (z : Sphere) :=
      congrArg ((↑) : ℂ → Sphere) (complexPlaneCoordinates.apply_symm_apply z)
    rw [hp]
    rfl
  rw [hDom] at hwc hwE
  have hve : (∫⁻ z in ((↑) : ℂ → Sphere) ⁻¹' G ∩
      (fun z : ℂ => π (z : Sphere)) ⁻¹' S,
      ENNReal.ofReal ‖FiniteTransfer.circleFDeriv v z‖ ^ 2) < ∞ := hwE
  have hvs : FiniteTransfer.SmoothCircleOn v
      (((↑) : ℂ → Sphere) ⁻¹' G ∩ (fun z : ℂ => π (z : Sphere)) ⁻¹' S) := hwc
  have hproj (i : I) (z : ℂ) (hzG : (z : Sphere) ∈ G) (hzV : π (z : Sphere) ∈ V i) :
      (u i (π (z : Sphere)) : UnitAddCircle) = v z := by
    have hzS := (hV i).2 (subset_closure hzV)
    have hp : diskRayProjection
        (upperHalfPlaneClamp (logarithmicCutChart (a i) (F (π (z : Sphere))))).val =
        F (π (z : Sphere)) := by
      rw [upperHalfPlaneClamp_val (logarithmicCutChart_nonneg (a i) (h1 _ hzS))]
      exact logarithmicCutChart_projection (a i) (h0 _ hzS)
    rw [hu i _ hzV, AddCircle.coe_add, hv z hzG hzS]
    congr 1
    have hm := (diskMeanCircle_projection hsch hsep K hK hKS (η.map f)
      (upperHalfPlaneClamp (logarithmicCutChart (a i) (F (π (z : Sphere)))))).symm
    rw [hp] at hm
    exact hm
  have hbranches (i : I) := period_branch_physical_energy e hG (hV i).1
    (fun x hx => (hV i).2 (subset_closure hx)) π hπ he (u i) (hcont i) v hvs (hproj i) hve
  exact ⟨{
    Index := I, countableIndex := hI, patch := V, angle := a, bound := C,
    branch := u, error := R, physical := v, euclidean := w, physical_eq := rfl, cover := hcover,
    patch_open := fun i => (hV i).1, patch_closure := fun i => (hV i).2,
    log_continuous := hlog, bounded := hbound, continuous := hcont,
    branch_value := hu, transition := htrans, closed := hclosed, domain_value := hdomain,
    error_continuous := hRc, error_bound := hRb, error_vanishes := hRlim, physical_smooth := hvs,
    physical_value := hv, physical_energy := hve,
    branch_smooth := fun i => (hbranches i).1, branch_energy := fun i => (hbranches i).2 },
    hRtol, hwgrad⟩

end CircleDomainRigidity

end

end OAI
