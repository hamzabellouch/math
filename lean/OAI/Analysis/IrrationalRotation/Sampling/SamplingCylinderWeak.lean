import OAI.Analysis.IrrationalRotation.Model.ProductSampling
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.Topology.Instances.Real.Lemmas

namespace OAI

noncomputable section
open MeasureTheory Filter Set TopologicalSpace
open scoped Topology ENNReal

namespace Invariant233.SamplingCylinderWeak

theorem tendsto_finiteMeasure_of_piSystem
    {X ι : Type*} [Nonempty X] [MeasurableSpace X] [TopologicalSpace X]
    [SecondCountableTopology X] [OpensMeasurableSpace X]
    {S : Set (Set X)} (hS : IsPiSystem S)
    {μ : ι → FiniteMeasure X} {ν : FiniteMeasure X}
    {l : Filter ι} [l.IsCountablyGenerated]
    (hmeas : ∀ s ∈ S, MeasurableSet s)
    (hbasis : ∀ u : Set X, IsOpen u → ∀ x ∈ u,
      ∃ s ∈ S, s ∈ 𝓝 x ∧ s ⊆ u)
    (hmass : Tendsto (fun i => (μ i).mass) l (𝓝 ν.mass))
    (hconv : ∀ s ∈ S, Tendsto (fun i => μ i s) l (𝓝 (ν s))) :
    Tendsto μ l (𝓝 ν) := by
  by_cases hν : ν = 0
  · subst ν
    exact FiniteMeasure.tendsto_zero_of_tendsto_zero_mass (by simpa using hmass)
  have hνmass : ν.mass ≠ 0 := (FiniteMeasure.mass_nonzero_iff ν).mpr hν
  have hnonzero : ∀ᶠ i in l, μ i ≠ 0 := by
    filter_upwards [(tendsto_order.1 hmass).1 0 (pos_iff_ne_zero.mpr hνmass)] with i hi
    exact (FiniteMeasure.mass_nonzero_iff (μ i)).mp (ne_of_gt hi)
  have hnorm : Tendsto (fun i => (μ i).normalize) l (𝓝 ν.normalize) := by
    apply hS.tendsto_probabilityMeasure_of_tendsto_of_mem hmeas hbasis
    intro s hs
    have h := (hmass.inv₀ hνmass).mul (hconv s hs)
    rw [← ν.normalize_eq_of_nonzero hν s] at h
    apply h.congr'
    filter_upwards [hnonzero] with i hi
    exact ((μ i).normalize_eq_of_nonzero hi s).symm
  exact FiniteMeasure.tendsto_of_tendsto_normalize_testAgainstNN_of_tendsto_mass hnorm hmass

abbrev CylinderTest (ι : Type*) := Finset (ι × ℚ × ℚ)

def cylinder {ι : Type*} (t : CylinderTest ι) : Set (ι → ℝ) :=
  {x | ∀ v ∈ t, (v.2.1 : ℝ) < x v.1 ∧ x v.1 < (v.2.2 : ℝ)}

@[simp] theorem cylinder_empty {ι : Type*} :
    cylinder (∅ : CylinderTest ι) = univ := by
  ext x
  simp [cylinder]

@[simp] theorem cylinder_union {ι : Type*} [DecidableEq ι] (s t : CylinderTest ι) :
    cylinder (s ∪ t) = cylinder s ∩ cylinder t := by
  classical
  ext x
  change (∀ v ∈ s ∪ t, _) ↔ ((∀ v ∈ s, _) ∧ (∀ v ∈ t, _))
  constructor
  · intro h
    exact ⟨fun v hv => h v (Finset.mem_union_left t hv),
      fun v hv => h v (Finset.mem_union_right s hv)⟩
  · rintro ⟨hs, ht⟩ v hv
    exact (Finset.mem_union.mp hv).elim (hs v) (ht v)

theorem cylinder_isOpen {ι : Type*} (t : CylinderTest ι) :
    IsOpen (cylinder t) := by
  have heq : cylinder t = ⋂ v ∈ t,
      (fun x : ι → ℝ => x v.1) ⁻¹' Ioo (v.2.1 : ℝ) (v.2.2 : ℝ) := by
    ext x
    simp [cylinder]
  rw [heq]
  exact isOpen_biInter_finset fun v _ => isOpen_Ioo.preimage (continuous_apply v.1)

theorem cylinder_piSystem {ι : Type*} :
    IsPiSystem (Set.range (cylinder (ι := ι))) := by
  classical
  rintro _ ⟨s, rfl⟩ _ ⟨t, rfl⟩ _
  exact ⟨s ∪ t, cylinder_union s t⟩

theorem exists_cylinder_nhds_subset {ι : Type*} (u : Set (ι → ℝ))
    (hu : IsOpen u) (x : ι → ℝ) (hx : x ∈ u) :
    ∃ t : CylinderTest ι, cylinder t ∈ 𝓝 x ∧ cylinder t ⊆ u := by
  classical
  obtain ⟨v, ⟨U, F, hU, rfl⟩, hxv, hvu⟩ :=
    (isTopologicalBasis_pi (fun _ : ι => Real.isTopologicalBasis_Ioo_rat)).exists_subset_of_mem_open hx hu
  have hchoices : ∀ i : F, ∃ a b : ℚ, a < b ∧ U i = Ioo (a : ℝ) (b : ℝ) := by
    intro i
    have hi := hU i i.property
    simpa only [mem_iUnion, mem_singleton_iff, exists_prop, eq_comm] using hi
  choose a b hab hinterval using hchoices
  let t : CylinderTest ι := F.attach.image (fun i => (i.val, a i, b i))
  have heq : cylinder t = (F : Set ι).pi U := by
    ext y
    simp only [cylinder, mem_ofPred_eq, t, Finset.mem_image, Finset.mem_attach,
      true_and, Set.mem_pi, Finset.mem_coe]
    constructor
    · intro h i hi
      have hv := h (i, a ⟨i, hi⟩, b ⟨i, hi⟩) ⟨⟨i, hi⟩, rfl⟩
      simpa only [hinterval ⟨i, hi⟩, mem_Ioo] using hv
    · intro h v hv
      obtain ⟨i, rfl⟩ := hv
      simpa only [hinterval i, mem_Ioo] using h i i.property
  refine ⟨t, ?_, heq ▸ hvu⟩
  exact (cylinder_isOpen t).mem_nhds (heq.symm ▸ hxv)

theorem tendsto_finiteMeasure_of_cylinders
    {κ ι : Type*} [Countable κ] {l : Filter ι} [l.IsCountablyGenerated]
    {μ : ι → FiniteMeasure (κ → ℝ)} {ν : FiniteMeasure (κ → ℝ)}
    (h : ∀ t : CylinderTest κ,
      Tendsto (fun i => μ i (cylinder t)) l (𝓝 (ν (cylinder t)))) :
    Tendsto μ l (𝓝 ν) := by
  apply tendsto_finiteMeasure_of_piSystem cylinder_piSystem
  · rintro _ ⟨t, rfl⟩
    exact (cylinder_isOpen t).measurableSet
  · intro u hu x hx
    obtain ⟨t, htx, htu⟩ := exists_cylinder_nhds_subset u hu x hx
    exact ⟨cylinder t, ⟨t, rfl⟩, htx, htu⟩
  · simpa only [cylinder_empty, FiniteMeasure.mass] using h ∅
  · rintro _ ⟨t, rfl⟩
    exact h t

open ProductModel

local instance : OpensMeasurableSpace EndpointPair := inferInstance

def cutCoordinates (xy : EndpointPair) : Bool × ℕ → ℝ :=
  fun i => circleRepresentative (if i.1 then xy.2 i.2 else xy.1 i.2)

def quotientCoordinates (x : Bool × ℕ → ℝ) : EndpointPair :=
  (fun i => (x (false, i) : Circle), fun i => (x (true, i) : Circle))

theorem cutCoordinates_measurable : Measurable cutCoordinates := by
  have hr : Measurable circleRepresentative :=
    measurable_subtype_coe.comp (AddCircle.measurableEquivIco (1 : ℝ) 0).measurable
  apply Measurable.of_eval
  rintro ⟨b, i⟩
  cases b
  · exact hr.comp ((measurable_pi_apply i).comp measurable_fst)
  · exact hr.comp ((measurable_pi_apply i).comp measurable_snd)

theorem quotientCoordinates_continuous : Continuous quotientCoordinates := by
  unfold quotientCoordinates
  fun_prop

@[simp] theorem quotient_cutCoordinates (xy : EndpointPair) :
    quotientCoordinates (cutCoordinates xy) = xy := by
  ext i <;> exact AddCircle.coe_equivIco

def endpointCylinder (t : CylinderTest (Bool × ℕ)) : Set EndpointPair :=
  cutCoordinates ⁻¹' cylinder t

theorem endpointCylinder_measurable (t : CylinderTest (Bool × ℕ)) :
    MeasurableSet (endpointCylinder t) :=
  (cylinder_isOpen t).measurableSet.preimage cutCoordinates_measurable

@[simp] theorem map_quotient_cut (μ : FiniteMeasure EndpointPair) :
    (μ.map cutCoordinates).map quotientCoordinates = μ := by
  apply Subtype.ext
  change Measure.map quotientCoordinates (Measure.map cutCoordinates (μ : Measure EndpointPair)) = _
  rw [Measure.map_map quotientCoordinates_continuous.measurable cutCoordinates_measurable]
  have heq : quotientCoordinates ∘ cutCoordinates = id := funext quotient_cutCoordinates
  rw [heq, Measure.map_id]
  rfl

theorem tendsto_endpoint_of_cylinders
    {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    {μ : ι → FiniteMeasure EndpointPair} {ν : FiniteMeasure EndpointPair}
    (h : ∀ t : CylinderTest (Bool × ℕ),
      Tendsto (fun i => μ i (endpointCylinder t)) l (𝓝 (ν (endpointCylinder t)))) :
    Tendsto μ l (𝓝 ν) := by
  have hlift : Tendsto (fun i => (μ i).map cutCoordinates) l
      (𝓝 (ν.map cutCoordinates)) := by
    apply tendsto_finiteMeasure_of_cylinders
    intro t
    simpa only [FiniteMeasure.map_apply _ cutCoordinates_measurable
      (cylinder_isOpen t).measurableSet, endpointCylinder] using h t
  have hquot := FiniteMeasure.tendsto_map_of_tendsto_of_continuous _ _ hlift
    quotientCoordinates_continuous
  simpa only [map_quotient_cut] using hquot

theorem weaklyConverges_of_cylinders
    {μ : ℕ → Measure EndpointPair} {ν : Measure EndpointPair}
    (hμ : ∀ n, IsFiniteMeasure (μ n)) (hν : IsFiniteMeasure ν)
    (h : ∀ t : CylinderTest (Bool × ℕ),
      Tendsto (fun n => μ n (endpointCylinder t)) atTop (𝓝 (ν (endpointCylinder t)))) :
    WeaklyConverges μ ν := by
  let μ' : ℕ → FiniteMeasure EndpointPair := fun n => ⟨μ n, hμ n⟩
  let ν' : FiniteMeasure EndpointPair := ⟨ν, hν⟩
  have hweak : Tendsto μ' atTop (𝓝 ν') := by
    apply tendsto_endpoint_of_cylinders
    intro t
    exact (ENNReal.tendsto_toNNReal (by let := hν; exact measure_ne_top _ _)).comp (h t)
  intro φ
  exact (FiniteMeasure.tendsto_iff_forall_integral_tendsto.mp hweak)
    (BoundedContinuousFunction.mkOfCompact φ)

theorem ae_weaklyConverges_of_cylinders
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {μ : Ω → ℕ → Measure EndpointPair} {ν : Measure EndpointPair}
    (hμ : ∀ ω n, IsFiniteMeasure (μ ω n)) (hν : IsFiniteMeasure ν)
    (h : ∀ t : CylinderTest (Bool × ℕ), ∀ᵐ ω ∂P,
      Tendsto (fun n => μ ω n (endpointCylinder t)) atTop (𝓝 (ν (endpointCylinder t)))) :
    ∀ᵐ ω ∂P, WeaklyConverges (μ ω) ν := by
  have hall := ae_all_iff.mpr h
  filter_upwards [hall] with ω hω
  exact weaklyConverges_of_cylinders (hμ ω) hν hω

theorem ae_all_weaklyConverges_of_cylinders
    {Ω J : Type*} [MeasurableSpace Ω] [Countable J] {P : Measure Ω}
    {μ : J → Ω → ℕ → Measure EndpointPair} {ν : J → Measure EndpointPair}
    (hμ : ∀ j ω n, IsFiniteMeasure (μ j ω n)) (hν : ∀ j, IsFiniteMeasure (ν j))
    (h : ∀ j (t : CylinderTest (Bool × ℕ)), ∀ᵐ ω ∂P,
      Tendsto (fun n => μ j ω n (endpointCylinder t)) atTop
        (𝓝 (ν j (endpointCylinder t)))) :
    ∀ᵐ ω ∂P, ∀ j, WeaklyConverges (μ j ω) (ν j) := by
  exact ae_all_iff.mpr fun j => ae_weaklyConverges_of_cylinders (hμ j) (hν j) (h j)

theorem ae_all_triangular_weaklyConverges_of_cylinders
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {μ : Finset ℕ → Ω → ℕ → Measure EndpointPair}
    (hμ : ∀ I ω n, IsFiniteMeasure (μ I ω n))
    (h : ∀ I (t : CylinderTest (Bool × ℕ)), ∀ᵐ ω ∂P,
      Tendsto (fun n => μ I ω n (endpointCylinder t)) atTop
        (𝓝 (triangularLaw I (endpointCylinder t)))) :
    ∀ᵐ ω ∂P, ∀ I, WeaklyConverges (μ I ω) (triangularLaw I) := by
  apply ae_all_weaklyConverges_of_cylinders hμ _ h
  intro I
  unfold triangularLaw
  infer_instance

end Invariant233.SamplingCylinderWeak

end

end OAI
