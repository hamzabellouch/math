import OAI.Combinatorics.EditApproximation.Refinement.PhysicalCommonSource
import OAI.Combinatorics.EditApproximation.Probability.RejectionArrayLaw
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-! Each common array source is realized by scalar exact uniform draws.
Regrouping finite coordinates recovers the common source law; unused
coordinates belong only to the probability space. -/

namespace EditApproximation

open MeasureTheory ProbabilityTheory

theorem finite_pi_curry {ι : Type*} [Fintype ι] {κ : ι → Type*} [∀ i, Fintype (κ i)]
    {X : (i : ι) → κ i → Type*} [∀ i j, MeasurableSpace (X i j)]
    (μ : ∀ i j, Measure (X i j)) [∀ i j, IsProbabilityMeasure (μ i j)] :
    (Measure.pi fun p : Sigma κ => μ p.1 p.2).map (fun draw i j => draw ⟨i, j⟩) =
      Measure.pi fun i => Measure.pi (μ i) := by
  have h := Measure.infinitePi_map_piCurry μ
  simp only [Measure.infinitePi_eq_pi, MeasurableEquiv.coe_piCurry] at h
  convert h using 1
  congr 1

theorem finite_uniform_three_curry {ι : Type*} [Fintype ι]
    {κ : ι → Type*} [∀ i, Fintype (κ i)]
    {κ₂ : (i : ι) → κ i → Type*} [∀ i j, Fintype (κ₂ i j)]
    (M : ℕ) [NeZero M] :
    (Measure.pi fun _ : Σ i, Σ j : κ i, κ₂ i j => (PMF.uniformOfFintype (Fin M)).toMeasure).map
      (fun draw i j k => draw ⟨i, j, k⟩) =
    Measure.pi fun i => Measure.pi fun j : κ i => Measure.pi fun _ : κ₂ i j =>
      (PMF.uniformOfFintype (Fin M)).toMeasure := by
  let μ := fun (i : ι) (_ : Σ j : κ i, κ₂ i j) => (PMF.uniformOfFintype (Fin M)).toMeasure
  have hfirst := finite_pi_curry μ
  have hsecond := Measure.pi_map_pi
    (μ := fun i => Measure.pi (μ i))
    (f := fun (i : ι) (draw : (Σ j : κ i, κ₂ i j) → Fin M) (j : κ i) (k : κ₂ i j) => draw ⟨j, k⟩)
    (fun _ => (measurable_of_finite _).aemeasurable)
  have heach (i : ι) := finite_pi_curry (fun (j : κ i) (_ : κ₂ i j) =>
    (PMF.uniformOfFintype (Fin M)).toMeasure)
  dsimp only [μ] at hsecond
  simp_rw [heach] at hsecond
  rw [← hfirst, Measure.map_map (by fun_prop) (by fun_prop)] at hsecond
  exact hsecond











abbrev PhysicalScalarDraw (M J N n exponent F Q R B : ℕ) :=
  ∀ key : PhysicalScalarKey M J N n exponent F Q R B,
    Fin (physicalScalarRange M J N n exponent F Q R B key)

noncomputable def physicalScalarLaw (M J N n exponent F Q R B : ℕ) [NeZero M] :
    Measure (PhysicalScalarDraw M J N n exponent F Q R B) :=
  Measure.pi fun key => (PMF.uniformOfFintype
    (Fin (physicalScalarRange M J N n exponent F Q R B key))).toMeasure

instance physicalScalarLaw_probability (M J N n exponent F Q R B : ℕ) [NeZero M] :
    IsProbabilityMeasure (physicalScalarLaw M J N n exponent F Q R B) := by
  unfold physicalScalarLaw
  infer_instance

def physicalScalarCoordinatePack (M J N n exponent F Q R B : ℕ)
    (key : PhysicalCommonKey M J N n exponent B)
    (draw : ∀ index : PhysicalScalarIndex M J N n exponent F Q R B key,
      Fin (physicalScalarRange M J N n exponent F Q R B ⟨key, index⟩)) :
    PhysicalCommonCoordinate M J N n exponent F Q R B key :=
  match key with
  | .inl _ => draw
  | .inr _ => fun time scale sample => draw ⟨time, scale, sample⟩

def physicalScalarPack (M J N n exponent F Q R B : ℕ)
    (draw : PhysicalScalarDraw M J N n exponent F Q R B) :
    PhysicalCommonDraw M J N n exponent F Q R B :=
  fun key => physicalScalarCoordinatePack M J N n exponent F Q R B key (fun index => draw ⟨key, index⟩)

section Laws

variable (M J N n exponent F Q R B : ℕ) [NeZero M]

 theorem physicalScalarCoordinatePack_law (key : PhysicalCommonKey M J N n exponent B) :
    (Measure.pi fun index : PhysicalScalarIndex M J N n exponent F Q R B key =>
      (PMF.uniformOfFintype (Fin (physicalScalarRange M J N n exponent F Q R B ⟨key, index⟩))).toMeasure).map
        (physicalScalarCoordinatePack M J N n exponent F Q R B key) =
      physicalCommonCoordinateLaw M J N n exponent F Q R B key := by
  cases key with
  | inl online => exact Measure.map_id
  | inr group => exact finite_uniform_three_curry M

 theorem physicalScalarPack_law :
    (physicalScalarLaw M J N n exponent F Q R B).map
        (physicalScalarPack M J N n exponent F Q R B) =
      physicalCommonLaw M J N n exponent F Q R B := by
  let μ := fun (key : PhysicalCommonKey M J N n exponent B)
      (index : PhysicalScalarIndex M J N n exponent F Q R B key) =>
    (PMF.uniformOfFintype (Fin (physicalScalarRange M J N n exponent F Q R B ⟨key, index⟩))).toMeasure
  have hfirst := finite_pi_curry μ
  have hsecond := Measure.pi_map_pi (μ := fun key => Measure.pi (μ key))
    (f := physicalScalarCoordinatePack M J N n exponent F Q R B)
    (fun _ => (measurable_of_finite _).aemeasurable)
  have heach := physicalScalarCoordinatePack_law M J N n exponent F Q R B
  dsimp only [μ] at hsecond
  simp_rw [heach] at hsecond
  rw [← hfirst, Measure.map_map (measurable_of_finite _) (measurable_of_finite _)] at hsecond
  exact hsecond

 theorem physicalRejectionArray_pack_law :
    (rejectionArrayLaw (physicalScalarRange M J N n exponent F Q R B)).map
      (fun execution => physicalScalarPack M J N n exponent F Q R B
        (rejectionArrayAccepted (physicalScalarRange M J N n exponent F Q R B) execution)) =
      physicalCommonLaw M J N n exponent F Q R B := by
  change (rejectionArrayLaw (physicalScalarRange M J N n exponent F Q R B)).map
    (physicalScalarPack M J N n exponent F Q R B ∘
      rejectionArrayAccepted (physicalScalarRange M J N n exponent F Q R B)) = _
  rw [← Measure.map_map (measurable_of_finite _) (by fun_prop)]
  rw [rejectionArrayLaw_accepted]
  exact physicalScalarPack_law M J N n exponent F Q R B

end Laws

end EditApproximation

end OAI
