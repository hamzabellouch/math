import OAI.Analysis.IrrationalRotation.Model.ProductSampling
import OAI.Analysis.IrrationalRotation.Analysis.FiniteMeasureCylinderConvergence
import OAI.Analysis.IrrationalRotation.Sampling.SamplingCylinderError

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped Topology

namespace Invariant233.ProductModel.SamplingWeak

local instance : OpensMeasurableSpace EndpointPair := inferInstance

abbrev EndpointCoordinate := Bool × ℕ
abbrev RectangleTest := Finset (EndpointCoordinate × ℚ × ℚ)

abbrev representative : EndpointPair → EndpointCoordinate → ℝ :=
  SamplingCylinderWeak.cutCoordinates

abbrev quotient : (EndpointCoordinate → ℝ) → EndpointPair :=
  SamplingCylinderWeak.quotientCoordinates

@[fun_prop] theorem measurable_representative : Measurable representative := by
  exact SamplingCylinderWeak.cutCoordinates_measurable

@[fun_prop] theorem continuous_quotient : Continuous quotient := by
  exact SamplingCylinderWeak.quotientCoordinates_continuous

@[simp] theorem quotient_representative (xy : EndpointPair) :
    quotient (representative xy) = xy := by
  exact SamplingCylinderWeak.quotient_cutCoordinates xy

def rectangle (F : RectangleTest) : Set EndpointPair :=
  representative ⁻¹' Invariant233.SamplingWeak.rationalCylinder F

theorem measurableSet_rectangle (F : RectangleTest) : MeasurableSet (rectangle F) :=
  (Invariant233.SamplingWeak.rationalCylinder_isOpen F).measurableSet.preimage
    measurable_representative

@[simp] theorem rectangle_empty : rectangle ∅ = Set.univ := by
  simp [rectangle]

private theorem map_quotient_representative (μ : FiniteMeasure EndpointPair) :
    (μ.map representative).map quotient = μ := by
  exact SamplingCylinderWeak.map_quotient_cut μ

theorem tendsto_finiteMeasure_of_rectangles
    {J : Type*} {l : Filter J} [l.IsCountablyGenerated]
    {μ : J → FiniteMeasure EndpointPair} {ν : FiniteMeasure EndpointPair}
    (h : ∀ F : RectangleTest,
      Tendsto (fun j => μ j (rectangle F)) l (𝓝 (ν (rectangle F)))) :
    Tendsto μ l (𝓝 ν) := by
  exact SamplingCylinderWeak.tendsto_endpoint_of_cylinders h

theorem weaklyConverges_of_rectangle_real
    {η : ℕ → Measure EndpointPair} {ν : Measure EndpointPair}
    (hη : ∀ n, IsFiniteMeasure (η n)) (hν : IsFiniteMeasure ν)
    (h : ∀ F : RectangleTest,
      Tendsto (fun n => (η n).real (rectangle F)) atTop (𝓝 (ν.real (rectangle F)))) :
    WeaklyConverges η ν := by
  exact SamplingCylinderWeak.weaklyConverges_of_real_cylinders hη hν h

theorem weaklyConverges_of_rectangles
    {η : ℕ → Measure EndpointPair} {ν : Measure EndpointPair}
    (hη : ∀ n, IsFiniteMeasure (η n)) (hν : IsFiniteMeasure ν)
    (h : ∀ F : RectangleTest,
      Tendsto (fun n => η n (rectangle F)) atTop (𝓝 (ν (rectangle F)))) :
    WeaklyConverges η ν := by
  exact SamplingCylinderWeak.weaklyConverges_of_cylinders hη hν h

theorem ae_weaklyConverges_of_ae_rectangle_real
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {η : Ω → ℕ → Measure EndpointPair} {ν : Measure EndpointPair}
    (hη : ∀ ω n, IsFiniteMeasure (η ω n)) (hν : IsFiniteMeasure ν)
    (h : ∀ F : RectangleTest, ∀ᵐ ω ∂P,
      Tendsto (fun n => (η ω n).real (rectangle F)) atTop (𝓝 (ν.real (rectangle F)))) :
    ∀ᵐ ω ∂P, WeaklyConverges (η ω) ν := by
  filter_upwards [ae_all_iff.mpr h] with ω hω
  exact weaklyConverges_of_rectangle_real (hη ω) hν hω

theorem countable_rectangles : Set.Countable (Set.range rectangle) :=
  Set.countable_range rectangle

theorem ae_all_weaklyConverges_of_ae_rectangle_real
    {Ω K : Type*} [MeasurableSpace Ω] [Countable K] {P : Measure Ω}
    {η : K → Ω → ℕ → Measure EndpointPair} {ν : K → Measure EndpointPair}
    (hη : ∀ k ω n, IsFiniteMeasure (η k ω n)) (hν : ∀ k, IsFiniteMeasure (ν k))
    (h : ∀ k (F : RectangleTest), ∀ᵐ ω ∂P,
      Tendsto (fun n => (η k ω n).real (rectangle F)) atTop
        (𝓝 ((ν k).real (rectangle F)))) :
    ∀ᵐ ω ∂P, ∀ k, WeaklyConverges (η k ω) (ν k) :=
  ae_all_iff.mpr (fun k => ae_weaklyConverges_of_ae_rectangle_real (hη k) (hν k) (h k))

def box (D : Finset EndpointCoordinate) (a b : EndpointCoordinate → ℚ) : Set EndpointPair :=
  {xy | ∀ i ∈ D, (a i : ℝ) < representative xy i ∧ representative xy i < (b i : ℝ)}

theorem rectangle_eq_box (F : RectangleTest) :
    ∃ (D : Finset EndpointCoordinate) (a b : EndpointCoordinate → ℚ),
      rectangle F = box D a b := by
  obtain ⟨D, a, b, heq⟩ := Invariant233.SamplingWeak.rationalCylinder_normal_form F
  refine ⟨D, a, b, ?_⟩
  unfold rectangle
  rw [heq]
  rfl

theorem weaklyConverges_of_box_real
    {η : ℕ → Measure EndpointPair} {ν : Measure EndpointPair}
    (hη : ∀ n, IsFiniteMeasure (η n)) (hν : IsFiniteMeasure ν)
    (h : ∀ (D : Finset EndpointCoordinate) (a b : EndpointCoordinate → ℚ),
      Tendsto (fun n => (η n).real (box D a b)) atTop (𝓝 (ν.real (box D a b)))) :
    WeaklyConverges η ν := by
  apply weaklyConverges_of_rectangle_real hη hν
  intro F
  obtain ⟨D, a, b, heq⟩ := rectangle_eq_box F
  simpa only [heq] using h D a b

theorem ae_all_weaklyConverges_of_ae_box_real
    {Ω K : Type*} [MeasurableSpace Ω] [Countable K] {P : Measure Ω}
    {η : K → Ω → ℕ → Measure EndpointPair} {ν : K → Measure EndpointPair}
    (hη : ∀ k ω n, IsFiniteMeasure (η k ω n)) (hν : ∀ k, IsFiniteMeasure (ν k))
    (h : ∀ k (D : Finset EndpointCoordinate) (a b : EndpointCoordinate → ℚ), ∀ᵐ ω ∂P,
      Tendsto (fun n => (η k ω n).real (box D a b)) atTop
        (𝓝 ((ν k).real (box D a b)))) :
    ∀ᵐ ω ∂P, ∀ k, WeaklyConverges (η k ω) (ν k) := by
  apply ae_all_weaklyConverges_of_ae_rectangle_real hη hν
  intro k F
  obtain ⟨D, a, b, heq⟩ := rectangle_eq_box F
  simpa only [heq] using h k D a b

end Invariant233.ProductModel.SamplingWeak

end

end OAI
