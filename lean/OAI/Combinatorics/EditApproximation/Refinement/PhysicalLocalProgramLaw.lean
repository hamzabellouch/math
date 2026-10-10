import OAI.Combinatorics.EditApproximation.Refinement.PhysicalLocalGroupKeys

namespace OAI

/-! A single bounded-key product supplies both online and whole-cell
streams. Restriction to the complete program preserves their joint law,
including independence between the two kinds of stream. -/

namespace EditApproximation

open MeasureTheory ProbabilityTheory

abbrev PhysicalLocalProgramKey (M J N n exponent : ℕ) :=
  Sum (PhysicalLocalOnlineKey M J N n) (PhysicalLocalGroupKey M J N n exponent)

section Law

variable {α : Type*} [DecidableEq α] {M J R : ℕ}
  [NeZero M] [MeasurableSpace (Fin M)] [MeasurableSingletonClass (Fin M)]
  (source target : List α) (U : PhysicalEntry M J target.length → ℕ)
  (N P F : ℕ) (A : ℚ) (T exponent H Q : ℕ) (tau : ℚ)

abbrev PhysicalLocalProgramCoordinate
    (key : PhysicalLocalProgramKey M J N target.length exponent) : Type :=
  match key with
  | .inl online => Fin R → Fin (physicalLocalOnlineMass source target U N P F A T exponent H tau online)
  | .inr group => PhysicalLocalGroupArray M J N target.length exponent F Q R group

instance physicalLocalProgramCoordinateFintype
    (key : PhysicalLocalProgramKey M J N target.length exponent) :
    Fintype (PhysicalLocalProgramCoordinate (R := R) source target U N P F A T exponent H Q tau key) := by
  cases key <;> dsimp only [PhysicalLocalProgramCoordinate] <;> infer_instance

instance physicalLocalProgramCoordinateMeasurableSpace
    (key : PhysicalLocalProgramKey M J N target.length exponent) :
    MeasurableSpace (PhysicalLocalProgramCoordinate (R := R) source target U N P F A T exponent H Q tau key) := by
  cases key <;> dsimp only [PhysicalLocalProgramCoordinate] <;> infer_instance

instance physicalLocalProgramCoordinateMeasurableSingleton
    (key : PhysicalLocalProgramKey M J N target.length exponent) :
    MeasurableSingletonClass
      (PhysicalLocalProgramCoordinate (R := R) source target U N P F A T exponent H Q tau key) := by
  cases key <;> dsimp only [physicalLocalProgramCoordinateMeasurableSpace,
    PhysicalLocalProgramCoordinate] <;> infer_instance

noncomputable def physicalLocalProgramCoordinateLaw
    (key : PhysicalLocalProgramKey M J N target.length exponent) :
    Measure (PhysicalLocalProgramCoordinate (R := R) source target U N P F A T exponent H Q tau key) :=
  match key with
  | .inl online => Measure.pi fun _ : Fin R =>
      (PMF.uniformOfFintype
        (Fin (physicalLocalOnlineMass source target U N P F A T exponent H tau online))).toMeasure
  | .inr group => physicalLocalGroupArrayLaw M J N target.length exponent F Q R group

instance physicalLocalProgramCoordinateLaw_probability
    (key : PhysicalLocalProgramKey M J N target.length exponent) :
    IsProbabilityMeasure
      (physicalLocalProgramCoordinateLaw (R := R) source target U N P F A T exponent H Q tau key) := by
  cases key <;> dsimp only [physicalLocalProgramCoordinateLaw,
    physicalLocalProgramCoordinateMeasurableSpace, PhysicalLocalProgramCoordinate] <;> infer_instance

abbrev PhysicalLocalProgramDraw := ∀ key : PhysicalLocalProgramKey M J N target.length exponent,
  PhysicalLocalProgramCoordinate (R := R) source target U N P F A T exponent H Q tau key

noncomputable def physicalLocalProgramDrawLaw :
    Measure (PhysicalLocalProgramDraw (R := R) source target U N P F A T exponent H Q tau) :=
  Measure.pi (physicalLocalProgramCoordinateLaw (R := R) source target U N P F A T exponent H Q tau)

def physicalLocalProgramOldKey
    (key : PhysicalProgramKey source target U N P F A exponent) :
    PhysicalLocalProgramKey M J N target.length exponent :=
  match key with
  | .inl online => .inl (physicalOnlineRawKey source target U N P F A online)
  | .inr group => .inr (physicalGroupRawKey source target U N P F exponent A group)

omit [NeZero M] [MeasurableSpace (Fin M)] [MeasurableSingletonClass (Fin M)] in
theorem physicalLocalProgramOldKey_injective :
    Function.Injective (physicalLocalProgramOldKey source target U N P F A exponent) := by
  intro first second heq
  cases first with
  | inl first =>
    cases second with
    | inl second =>
      exact congrArg Sum.inl
        (physicalOnlineRawKey_injective source target U N P F A (Sum.inl.inj heq))
    | inr second => exact False.elim (Sum.inl_ne_inr heq)
  | inr first =>
    cases second with
    | inl second => exact False.elim (Sum.inr_ne_inl heq)
    | inr second =>
      exact congrArg Sum.inr
        (physicalGroupRawKey_injective source target U N P F exponent A (Sum.inr.inj heq))

variable (hsize : source.length + target.length ≤ N) (hP : 66 ≤ P) (hF : 1 ≤ F) (hA : 1 ≤ A)
  (hseed : ∀ state, stateEditCost (physicalSource source state.1) target state.2 ≤ U state ∧
    (U state : ℚ) ≤ A * stateEditCost (physicalSource source state.1) target state.2)

def physicalLocalProgramCoordinateImage
    (key : PhysicalProgramKey source target U N P F A exponent) :
    PhysicalLocalProgramCoordinate (R := R) source target U N P F A T exponent H Q tau
        (physicalLocalProgramOldKey source target U N P F A exponent key) →
      PhysicalProgramCoordinate (R := R) source target U N P F A T exponent H Q tau key :=
  match key with
  | .inl online => fun array time => Fin.cast
      (physicalLocalOnlineMass_on_key source target U N P F A T exponent H tau hsize hP hF hA hseed online)
      (array time)
  | .inr _ => id

def physicalLocalProgramToComplete
    (draw : PhysicalLocalProgramDraw (R := R) source target U N P F A T exponent H Q tau) :
    PhysicalProgramDraw (R := R) source target U N P F A T exponent H Q tau :=
  fun key => physicalLocalProgramCoordinateImage source target U N P F A T exponent H Q tau
    hsize hP hF hA hseed key (draw (physicalLocalProgramOldKey source target U N P F A exponent key))

theorem physicalLocalProgramDrawLaw_map :
    (physicalLocalProgramDrawLaw (R := R) source target U N P F A T exponent H Q tau).map
      (physicalLocalProgramToComplete source target U N P F A T exponent H Q tau hsize hP hF hA hseed) =
    physicalProgramDrawLaw (R := R) source target U N P F A T exponent H Q tau := by
  have hmap := finite_pi_restrict_image_map
    (physicalLocalProgramCoordinateLaw (R := R) source target U N P F A T exponent H Q tau)
    (physicalLocalProgramOldKey source target U N P F A exponent)
    (physicalLocalProgramOldKey_injective source target U N P F A exponent)
    (physicalLocalProgramCoordinateImage source target U N P F A T exponent H Q tau hsize hP hF hA hseed)
    (fun _ => measurable_of_finite _)
  refine hmap.trans ?_
  unfold physicalProgramDrawLaw
  congr 1
  funext key
  cases key with
  | inl online =>
    exact finite_uniform_array_cast R _ _
      (physicalLocalOnlineMass_on_key source target U N P F A T exponent H tau hsize hP hF hA hseed online)
  | inr group => exact Measure.map_id

end Law

end EditApproximation

end OAI
