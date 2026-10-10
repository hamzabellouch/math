import OAI.LinearAlgebra.MatrixMultiplication.ComplexBounds.CW75ReorderedWords
import OAI.LinearAlgebra.MatrixMultiplication.Entropy.ComplexConditionalHierarchyStage
import OAI.LinearAlgebra.MatrixMultiplication.Separation.ComplexPrefixSeparationOrientations
import OAI.LinearAlgebra.MatrixMultiplication.Tensor.ComplexGeometricStageCoordinates

namespace OAI

/-! Explicit complex square and rectangular matrix multiplication bounds. -/

noncomputable section

namespace MatrixMultiplication.CW75ReorderedGeometricValues

open MatrixMultiplication.Foundation
open ComplexWitness CW75LabelHierarchy CW75ReorderedWords ConditionalPrefixWords
open ConditionalHierarchyStage PrefixSeparationPolynomialStage PrefixSeparationOrientations
open StageHierarchyResources
open scoped Classical

variable {Position : Type*} [Fintype Position] {counts : Scalar → ℕ} {n t : ℕ}

abbrev size (counts : Scalar → ℕ) (n t : ℕ) := stageRefinementCount counts curveLabels n t

theorem actualPool_decode (old : ExactPrefix counts curveLabels n t Position)
    (code : Fin (size counts n t)) :
    decodePool (actualPool counts curveLabels n t id) (size counts n t)
      (actualPool_card counts curveLabels n t id) old code =
        ((conditionalPoolEquivFin old).symm code).val := rfl

theorem decode_eq_iff_eligible (old : ExactPrefix counts curveLabels n t Position)
    (code : Fin (size counts n t)) (u v w : LongWord Position)
    (word : Position → Scalar) (hword : Represents id old u v w word) :
    decodePool (actualPool counts curveLabels n t id) (size counts n t)
      (actualPool_card counts curveLabels n t id) old code = (fun i => curveLabels n (word i)) ↔
        eligible id (appendCode old code) u v w := by
  rw [actualPool_decode]
  exact (eligible_appendCode_iff_of_represents old code u v w word hword).symm

private theorem first_read (old : ExactPrefix counts curveLabels n t Position)
    (u v w : LongWord Position) (word : Position → Scalar) (hn : n < 5)
    (hword : Represents id old u v w word) :
    firstRead id old (coordinateOf (curveFirstSide n) u v w) = fun i => curveLabels n (word i) := by
  rw [hword.1, hword.2.1, hword.2.2.1, coordinateOf_original]
  exact firstRead_on_original_word id old word hn hword.2.2.2

private theorem second_read (old : ExactPrefix counts curveLabels n t Position)
    (u v w : LongWord Position) (word : Position → Scalar) (hn : n < 5)
    (hword : Represents id old u v w word) :
    secondRead id old (coordinateOf (curveSecondSide n) u v w) = fun i => curveLabels n (word i) := by
  rw [hword.1, hword.2.1, hword.2.2.1, coordinateOf_original]
  exact secondRead_on_original_word id old word hn hword.2.2.2

theorem raw_XY_normal
    (old : ExactPrefix counts curveLabels n t Position) (hn : n < 5)
    (hfirst : curveFirstSide n = .x) (hsecond : curveSecondSide n = .y)
    (x : LongWord Position × InformedOutput (size counts n t))
    (y : LongWord Position × InformedOutput (size counts n t))
    (z : LongWord Position × MissingOutput (size counts n t))
    (word : Position → Scalar) (hword : Represents id old x.1 y.1 z.1 word) :
    rawPoolLeading (actualPool counts curveLabels n t id) (size counts n t)
      (stageRefinementCount_pos counts curveLabels n t) (actualPool_card counts curveLabels n t id)
      (firstRead id) (secondRead id) old x y z =
        if x.2.1 = y.2.1 ∧ x.2.1 = z.2.1 ∧
          eligible id (appendCode old x.2.1) x.1 y.1 z.1 then
            (GeometricStageCoordinates.xy (size counts n t)).tensor x.2.2 y.2.2 z.2.2
        else 0 := by
  have hx := first_read old x.1 y.1 z.1 word hn hword
  have hy := second_read old x.1 y.1 z.1 word hn hword
  simp only [hfirst, coordinateOf] at hx
  simp only [hsecond, coordinateOf] at hy
  rw [rawPoolLeading_eq_decodedLeading
    (actualPool counts curveLabels n t id) (size counts n t)
    (stageRefinementCount_pos counts curveLabels n t) (actualPool_card counts curveLabels n t id)
    (firstRead id) (secondRead id) (fun _ _ _ _ => fun i => curveLabels n (word i))
    old x y z hx hy]
  unfold decodedLeading
  simp only [decode_eq_iff_eligible old x.2.1 x.1 y.1 z.1 word hword,
    GeometricStageCoordinates.xy_tensor_apply]
  simp only [ite_and]

theorem raw_XZ_normal
    (old : ExactPrefix counts curveLabels n t Position) (hn : n < 5)
    (hfirst : curveFirstSide n = .x) (hsecond : curveSecondSide n = .z)
    (x : LongWord Position × InformedOutput (size counts n t))
    (y : LongWord Position × MissingOutput (size counts n t))
    (z : LongWord Position × InformedOutput (size counts n t))
    (word : Position → Scalar) (hword : Represents id old x.1 y.1 z.1 word) :
    rawPoolLeadingXZ (actualPool counts curveLabels n t id) (size counts n t)
      (stageRefinementCount_pos counts curveLabels n t) (actualPool_card counts curveLabels n t id)
      (firstRead id) (secondRead id) old x y z =
        if x.2.1 = y.2.1 ∧ x.2.1 = z.2.1 ∧
          eligible id (appendCode old x.2.1) x.1 y.1 z.1 then
            (GeometricStageCoordinates.xz (size counts n t)).tensor x.2.2 y.2.2 z.2.2
        else 0 := by
  have hx := first_read old x.1 y.1 z.1 word hn hword
  have hz := second_read old x.1 y.1 z.1 word hn hword
  simp only [hfirst, coordinateOf] at hx
  simp only [hsecond, coordinateOf] at hz
  unfold rawPoolLeadingXZ
  rw [rawPoolLeading_eq_decodedLeading
    (actualPool counts curveLabels n t id) (size counts n t)
    (stageRefinementCount_pos counts curveLabels n t) (actualPool_card counts curveLabels n t id)
    (firstRead id) (secondRead id) (fun _ _ _ _ => fun i => curveLabels n (word i))
    old x z y hx hz]
  unfold decodedLeading
  simp only [decode_eq_iff_eligible old x.2.1 x.1 y.1 z.1 word hword,
    GeometricStageCoordinates.xz_tensor_apply]
  have hswap :
      (x.2.1 = z.2.1 ∧ x.2.1 = y.2.1 ∧
        eligible id (appendCode old x.2.1) x.1 y.1 z.1 ∧ x.2.2 = z.2.2) ↔
      (x.2.1 = y.2.1 ∧ x.2.1 = z.2.1 ∧
        eligible id (appendCode old x.2.1) x.1 y.1 z.1 ∧ x.2.2 = z.2.2) :=
    and_left_comm
  simp only [hswap, ite_and]

theorem raw_YZ_normal
    (old : ExactPrefix counts curveLabels n t Position) (hn : n < 5)
    (hfirst : curveFirstSide n = .y) (hsecond : curveSecondSide n = .z)
    (x : LongWord Position × MissingOutput (size counts n t))
    (y : LongWord Position × InformedOutput (size counts n t))
    (z : LongWord Position × InformedOutput (size counts n t))
    (word : Position → Scalar) (hword : Represents id old x.1 y.1 z.1 word) :
    rawPoolLeadingYZ (actualPool counts curveLabels n t id) (size counts n t)
      (stageRefinementCount_pos counts curveLabels n t) (actualPool_card counts curveLabels n t id)
      (firstRead id) (secondRead id) old x y z =
        if x.2.1 = y.2.1 ∧ x.2.1 = z.2.1 ∧
          eligible id (appendCode old x.2.1) x.1 y.1 z.1 then
            (GeometricStageCoordinates.yz (size counts n t)).tensor x.2.2 y.2.2 z.2.2
        else 0 := by
  have hy := first_read old x.1 y.1 z.1 word hn hword
  have hz := second_read old x.1 y.1 z.1 word hn hword
  simp only [hfirst, coordinateOf] at hy
  simp only [hsecond, coordinateOf] at hz
  unfold rawPoolLeadingYZ
  rw [rawPoolLeading_eq_decodedLeading
    (actualPool counts curveLabels n t id) (size counts n t)
    (stageRefinementCount_pos counts curveLabels n t) (actualPool_card counts curveLabels n t id)
    (firstRead id) (secondRead id) (fun _ _ _ _ => fun i => curveLabels n (word i))
    old y z x hy hz]
  have hguard :
      (y.2.1 = z.2.1 ∧ y.2.1 = x.2.1 ∧
        decodePool (actualPool counts curveLabels n t id) (size counts n t)
          (actualPool_card counts curveLabels n t id) old y.2.1 = (fun i => curveLabels n (word i)) ∧
        y.2.2 = z.2.2) ↔
      (x.2.1 = y.2.1 ∧ x.2.1 = z.2.1 ∧
        eligible id (appendCode old x.2.1) x.1 y.1 z.1 ∧ y.2.2 = z.2.2) := by
    constructor
    · rintro ⟨hyz, hyx, hdecode, hpair⟩
      refine ⟨hyx.symm, hyx.symm.trans hyz, ?_, hpair⟩
      apply (decode_eq_iff_eligible old x.2.1 x.1 y.1 z.1 word hword).mp
      simpa only [hyx] using hdecode
    · rintro ⟨hxy, hxz, he, hpair⟩
      refine ⟨hxy.symm.trans hxz, hxy.symm, ?_, hpair⟩
      have hdecode := (decode_eq_iff_eligible old x.2.1 x.1 y.1 z.1 word hword).mpr he
      simpa only [hxy] using hdecode
  unfold decodedLeading
  simp only [hguard, GeometricStageCoordinates.yz_tensor_apply]
  simp only [ite_and]

end MatrixMultiplication.CW75ReorderedGeometricValues

end

end OAI
