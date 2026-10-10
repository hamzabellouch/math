import OAI.Combinatorics.EditApproximation.Geometry.CommonRangeSource
import OAI.Combinatorics.EditApproximation.Refinement.PhysicalLocalProgramLaw
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-! The actual bounded physical program can share one source universe
across incoming seed tables. Online coordinates include their requested
range; group coordinates share whole-cell arrays. -/

namespace EditApproximation

open MeasureTheory ProbabilityTheory



abbrev PhysicalCommonCoordinate (M J N n exponent F Q R B : ℕ)
    (key : PhysicalCommonKey M J N n exponent B) : Type :=
  match key with
  | .inl online => Fin R → Fin online.2.val.val
  | .inr group => PhysicalLocalGroupArray M J N n exponent F Q R group

section Source

variable (M J N n exponent F Q R B : ℕ)
  [NeZero M] [MeasurableSpace (Fin M)] [MeasurableSingletonClass (Fin M)]

instance physicalCommonCoordinateFintype (key : PhysicalCommonKey M J N n exponent B) :
    Fintype (PhysicalCommonCoordinate M J N n exponent F Q R B key) := by
  cases key <;> dsimp only [PhysicalCommonCoordinate] <;> infer_instance

instance physicalCommonCoordinateMeasurable (key : PhysicalCommonKey M J N n exponent B) :
    MeasurableSpace (PhysicalCommonCoordinate M J N n exponent F Q R B key) := by
  cases key <;> dsimp only [PhysicalCommonCoordinate] <;> infer_instance

instance physicalCommonCoordinateSingleton (key : PhysicalCommonKey M J N n exponent B) :
    MeasurableSingletonClass (PhysicalCommonCoordinate M J N n exponent F Q R B key) := by
  cases key <;> dsimp only [PhysicalCommonCoordinate, physicalCommonCoordinateMeasurable] <;> infer_instance

noncomputable def physicalCommonCoordinateLaw (key : PhysicalCommonKey M J N n exponent B) :
    Measure (PhysicalCommonCoordinate M J N n exponent F Q R B key) :=
  match key with
  | .inl online => Measure.pi fun _ : Fin R =>
      (PMF.uniformOfFintype (Fin online.2.val.val)).toMeasure
  | .inr group => physicalLocalGroupArrayLaw M J N n exponent F Q R group

instance physicalCommonCoordinateLaw_probability (key : PhysicalCommonKey M J N n exponent B) :
    IsProbabilityMeasure (physicalCommonCoordinateLaw M J N n exponent F Q R B key) := by
  cases key <;> dsimp only [physicalCommonCoordinateLaw, PhysicalCommonCoordinate,
    physicalCommonCoordinateMeasurable] <;> infer_instance

abbrev PhysicalCommonDraw := ∀ key : PhysicalCommonKey M J N n exponent B,
  PhysicalCommonCoordinate M J N n exponent F Q R B key

noncomputable def physicalCommonLaw : Measure (PhysicalCommonDraw M J N n exponent F Q R B) :=
  Measure.pi (physicalCommonCoordinateLaw M J N n exponent F Q R B)

instance physicalCommonLaw_probability : IsProbabilityMeasure
    (physicalCommonLaw M J N n exponent F Q R B) := by
  unfold physicalCommonLaw
  infer_instance

end Source

section Selection

variable {α : Type*} [DecidableEq α] {M J : ℕ}
  [NeZero M] [MeasurableSpace (Fin M)] [MeasurableSingletonClass (Fin M)]
  (source target : List α) (U : PhysicalEntry M J target.length → ℕ)
  (N P F : ℕ) (A : ℚ) (T exponent H Q R B : ℕ) (tau : ℚ)
  (hbound : ∀ key, physicalLocalOnlineMass source target U N P F A T exponent H tau key ≤ B)

omit [NeZero M] [MeasurableSpace (Fin M)] [MeasurableSingletonClass (Fin M)] in
theorem physicalCommonMass_positive (key : PhysicalLocalOnlineKey M J N target.length) :
    0 < physicalLocalOnlineMass source target U N P F A T exponent H tau key :=
  optimizerTriangularMass_positive _
    (pow_pos (physicalLocalOnlineBandG_positive source target U N P F A T exponent H tau key) 80)

def physicalCommonSelectedOnlineKey (online : PhysicalLocalOnlineKey M J N target.length) :
    CommonRangeKey (PhysicalLocalOnlineKey M J N target.length) B :=
  (online, positiveDrawRangeOfLE B
    (physicalLocalOnlineMass source target U N P F A T exponent H tau online)
    (physicalCommonMass_positive source target U N P F A T exponent H tau online) (hbound online))

def physicalCommonSelectedKey (key : PhysicalLocalProgramKey M J N target.length exponent) :
    PhysicalCommonKey M J N target.length exponent B :=
  match key with
  | .inl online => .inl (physicalCommonSelectedOnlineKey source target U N P F A T exponent H B tau hbound online)
  | .inr group => .inr group

omit [NeZero M] [MeasurableSpace (Fin M)] [MeasurableSingletonClass (Fin M)] in
theorem physicalCommonSelectedKey_injective : Function.Injective
    (physicalCommonSelectedKey source target U N P F A T exponent H B tau hbound) := by
  intro left right heq
  cases left with
  | inl left =>
    cases right with
    | inl right => exact congrArg Sum.inl (congrArg Prod.fst (Sum.inl.inj heq))
    | inr right => exact False.elim (Sum.inl_ne_inr heq)
  | inr left =>
    cases right with
    | inl right => exact False.elim (Sum.inr_ne_inl heq)
    | inr right => exact congrArg Sum.inr (Sum.inr.inj heq)

omit [NeZero M] [MeasurableSpace (Fin M)] [MeasurableSingletonClass (Fin M)] in
theorem physicalCommonSelectedOnlineKey_range (online : PhysicalLocalOnlineKey M J N target.length) :
    (physicalCommonSelectedOnlineKey source target U N P F A T exponent H B tau hbound online).2.val.val =
      physicalLocalOnlineMass source target U N P F A T exponent H tau online := by
  exact positiveDrawRangeOfLE_val B _
    (physicalCommonMass_positive source target U N P F A T exponent H tau online) (hbound online)

def physicalCommonCoordinateImage (key : PhysicalLocalProgramKey M J N target.length exponent) :
    PhysicalCommonCoordinate M J N target.length exponent F Q R B
        (physicalCommonSelectedKey source target U N P F A T exponent H B tau hbound key) →
      PhysicalLocalProgramCoordinate (R := R) source target U N P F A T exponent H Q tau key :=
  match key with
  | .inl online => fun array time => Fin.cast
      (physicalCommonSelectedOnlineKey_range source target U N P F A T exponent H B tau hbound online)
      (array time)
  | .inr _ => id

def physicalCommonSample
    (draw : PhysicalCommonDraw M J N target.length exponent F Q R B) :
    PhysicalLocalProgramDraw (R := R) source target U N P F A T exponent H Q tau :=
  fun key => physicalCommonCoordinateImage source target U N P F A T exponent H Q R B tau hbound key
    (draw (physicalCommonSelectedKey source target U N P F A T exponent H B tau hbound key))

theorem physicalCommonSample_law :
    (physicalCommonLaw M J N target.length exponent F Q R B).map
        (physicalCommonSample source target U N P F A T exponent H Q R B tau hbound) =
      physicalLocalProgramDrawLaw (R := R) source target U N P F A T exponent H Q tau := by
  have h := finite_pi_restrict_image_map
    (physicalCommonCoordinateLaw M J N target.length exponent F Q R B)
    (physicalCommonSelectedKey source target U N P F A T exponent H B tau hbound)
    (physicalCommonSelectedKey_injective source target U N P F A T exponent H B tau hbound)
    (physicalCommonCoordinateImage source target U N P F A T exponent H Q R B tau hbound)
    (fun _ => measurable_of_finite _)
  refine h.trans ?_
  unfold physicalLocalProgramDrawLaw
  congr 1
  funext key
  cases key with
  | inl online =>
    exact finite_uniform_array_cast R _ _
      (physicalCommonSelectedOnlineKey_range source target U N P F A T exponent H B tau hbound online)
  | inr group => exact Measure.map_id

end Selection

end EditApproximation

end OAI
