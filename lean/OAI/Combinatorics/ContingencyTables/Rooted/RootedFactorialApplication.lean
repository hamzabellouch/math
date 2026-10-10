import OAI.Combinatorics.ContingencyTables.Rooted.RootedCountIdentification
import OAI.Combinatorics.ContingencyTables.Counting.CompanionFactorialApplication

namespace OAI

/-! # Actual factorial lifts of the selected-root completion count -/

namespace ContingencyTables.RootedFactorialApplication

open scoped BigOperators Classical Matrix
open CommonBasesFPRAS CompanionFactorialApplication
open LargePairEnumeration BalancedBox LabelledFactorial

variable {I J : Type*} [Fintype I] [Fintype J]

noncomputable def f (A : Instance I J) (R : RootedCompletion.Selection A.T) (alpha : ℝ) : Set (Labels A×Bool) → ℝ :=
  firstLift (TwoLiftStates.group (labelCell A)) (RootedCountIdentification.h A R alpha) (denominator A)

noncomputable def g (A : Instance I J) (R : RootedCompletion.Selection A.T) (alpha : ℝ) : Set (Labels A×Bool) → ℝ :=
  secondLift (TwoLiftStates.group (labelCell A)) (RootedCountIdentification.h A R alpha) (denominator A)

/-- The manuscript's actual factorial lift is positive on its degree and
has its omission signature, derived from the literal count. -/
theorem first_properties (A : Instance I J) (R : RootedCompletion.Selection A.T) (alpha : ℝ) (ha : 0≤alpha) :
    BinaryContraction.DegreePositive (f A R alpha) (Fintype.card (Labels A)) ∧
      BinaryContraction.OmissionProperty (f A R alpha) (Fintype.card (Labels A)) := by
  change BinaryContraction.DegreePositive
      (firstLift (TwoLiftStates.group (labelCell A)) (RootedCountIdentification.h A R alpha) (denominator A)) _ ∧
    BinaryContraction.OmissionProperty
      (firstLift (TwoLiftStates.group (labelCell A)) (RootedCountIdentification.h A R alpha) (denominator A)) _
  constructor
  · exact SliceFactorial.firstLift_degreePositive (TwoLiftStates.group (labelCell A))
      (RootedCountIdentification.h A R alpha) (denominator A) (Fintype.card (Labels A)) (denominator_positive A)
      (fun z _ _ => RootedCountIdentification.h_positive A R alpha z)
  · have hs : @RemovalSlice (View A) _ (Classical.decEq _)
        (RootedCountIdentification.h A R alpha) (groupCount (TwoLiftStates.group (labelCell A)) Set.univ)
        (Fintype.card (Labels A)) := by
      rw [label_capacity]
      convert RootedCountIdentification.h_removal A R alpha ha _ using 1
    convert SliceFactorial.firstLift_omission_slice (TwoLiftStates.group (labelCell A))
      (RootedCountIdentification.h A R alpha) (denominator A) (Fintype.card (Labels A)) (denominator_positive A)
      (fun z => (RootedCountIdentification.h_positive A R alpha z).le) hs using 1

/-- The dual factorial lift retains positivity and has its actual
addition signature from the globally reflected raw count. -/
theorem second_properties (A : Instance I J) (R : RootedCompletion.Selection A.T) (alpha : ℝ) (ha : 0≤alpha) :
    BinaryContraction.DegreePositive (g A R alpha) (Fintype.card (Labels A)) ∧
      BinaryContraction.AdditionProperty (g A R alpha) (Fintype.card (Labels A)) := by
  change BinaryContraction.DegreePositive
      (secondLift (TwoLiftStates.group (labelCell A)) (RootedCountIdentification.h A R alpha) (denominator A)) _ ∧
    BinaryContraction.AdditionProperty
      (secondLift (TwoLiftStates.group (labelCell A)) (RootedCountIdentification.h A R alpha) (denominator A)) _
  constructor
  · intro S _
    exact div_pos
      (mul_pos (RootedCountIdentification.h_positive A R alpha _) (FactorialSignatures.factorialProduct_positive _))
      (denominator_positive A)
  · have hs : @RemovalSlice (View A) _ (Classical.decEq _)
        (fun z => RootedCountIdentification.h A R alpha (IntegerReflection.reflect
          (groupCount (TwoLiftStates.group (labelCell A)) Set.univ) z))
        (groupCount (TwoLiftStates.group (labelCell A)) Set.univ)
        (Fintype.card (Labels A×Bool)-Fintype.card (Labels A)) := by
      rw [label_capacity]
      convert RootedCountIdentification.h_reflected A R alpha ha _ using 1
    convert ReflectedSlices.secondLift_addition_reflected_slice (TwoLiftStates.group (labelCell A))
      (RootedCountIdentification.h A R alpha) (denominator A) (Fintype.card (Labels A))
      (by simp only [Fintype.card_prod,Fintype.card_bool]; omega)
      (denominator_positive A) (fun z => (RootedCountIdentification.h_positive A R alpha z).le) hs using 1

/-- The actual paired-label chain has the required pointwise q=W²
comparison, with the source count appearing identically in both lifts. -/
theorem chain_comparison (A : Instance I J) (R : RootedCompletion.Selection A.T) (alpha : ℝ) (S : Set (Labels A×Bool))
    (hS : CommonBasesFPRAS.ChainState TwoLiftStates.pairs S) :
    (1/(A.W:ℝ)^2)*f A R alpha S≤g A R alpha S ∧ g A R alpha S≤(A.W:ℝ)^2*f A R alpha S := by
  apply TwoLiftStates.chain_lifts_compare (labelCell A) (RootedCountIdentification.h A R alpha) S hS A.W
    (by have hW := A.hW; omega)
  · intro s
    rw [label_width]
    exact A.hsmall _ _ s.property
  · exact (RootedCountIdentification.h_positive A R alpha _).le

end ContingencyTables.RootedFactorialApplication

end OAI
