import OAI.LinearAlgebra.MatrixMultiplication.Completion.HierarchyWords
import OAI.LinearAlgebra.MatrixMultiplication.Entropy.ComplexConditionalHierarchyStage
import OAI.LinearAlgebra.MatrixMultiplication.Separation.ComplexPrefixSeparationOrientations
import OAI.LinearAlgebra.MatrixMultiplication.Tensor.ComplexGeometricStageCoordinates

namespace OAI

/-! Readable tensor completion and its finite arithmetic realization. -/

noncomputable section

namespace MatrixMultiplication.CompletionGeometricValues

open MatrixMultiplication.Foundation
open CompletionHierarchyWords ConditionalPrefixWords
open ConditionalHierarchyStage PrefixSeparationPolynomialStage PrefixSeparationOrientations
open StageHierarchyResources
open scoped Classical

variable {A X Y Z : Type*} [Fintype A] (H : ReadableHierarchy A X Y Z)
variable {Position : Type*} [Fintype Position] {counts : A → ℕ} {n t : ℕ}

abbrev size (counts : A → ℕ) (n t : ℕ) := stageRefinementCount counts H.labels n t

theorem actualPool_decode (old : ExactPrefix counts H.labels n t Position)
    (code : Fin (size H counts n t)) :
    decodePool (actualPool counts H.labels n t id) (size H counts n t)
      (actualPool_card counts H.labels n t id) old code =
        ((conditionalPoolEquivFin old).symm code).val := rfl

theorem decode_eq_iff_eligible (old : ExactPrefix counts H.labels n t Position)
    (code : Fin (size H counts n t))
    (u : Position → X) (v : Position → Y) (w : Position → Z)
    (word : Position → A) (hword : Represents H id old u v w word) :
    decodePool (actualPool counts H.labels n t id) (size H counts n t)
      (actualPool_card counts H.labels n t id) old code = (fun i => H.labels n (word i)) ↔
        eligible H id (appendCode old code) u v w := by
  rw [actualPool_decode]
  exact (eligible_appendCode_iff_of_represents H old code u v w word hword).symm

theorem raw_XY_normal
    (old : ExactPrefix counts H.labels n t Position) (hn : n < H.depth)
    (hp : H.pair n = .xy)
    (x : (Position → X) × InformedOutput (size H counts n t))
    (y : (Position → Y) × InformedOutput (size H counts n t))
    (z : (Position → Z) × MissingOutput (size H counts n t))
    (word : Position → A) (hword : Represents H id old x.1 y.1 z.1 word) :
    rawPoolLeading (actualPool counts H.labels n t id) (size H counts n t)
      (stageRefinementCount_pos counts H.labels n t) (actualPool_card counts H.labels n t id)
      (readXYX H id hp) (readXYY H id hp) old x y z =
        if x.2.1 = y.2.1 ∧ x.2.1 = z.2.1 ∧
          eligible H id (appendCode old x.2.1) x.1 y.1 z.1 then
            (GeometricStageCoordinates.xy (size H counts n t)).tensor x.2.2 y.2.2 z.2.2
        else 0 := by
  have hx : readXYX H id hp old x.1 = fun i => H.labels n (word i) := by
    rw [hword.1]
    exact readXYX_on_original_word H id hp old word hn hword.2.2.2
  have hy : readXYY H id hp old y.1 = fun i => H.labels n (word i) := by
    rw [hword.2.1]
    exact readXYY_on_original_word H id hp old word hn hword.2.2.2
  rw [rawPoolLeading_eq_decodedLeading
    (actualPool counts H.labels n t id) (size H counts n t)
    (stageRefinementCount_pos counts H.labels n t) (actualPool_card counts H.labels n t id)
    (readXYX H id hp) (readXYY H id hp) (fun _ _ _ _ => fun i => H.labels n (word i))
    old x y z hx hy]
  unfold decodedLeading
  simp only [decode_eq_iff_eligible H old x.2.1 x.1 y.1 z.1 word hword,
    GeometricStageCoordinates.xy_tensor_apply]
  simp only [ite_and]

theorem raw_XZ_normal
    (old : ExactPrefix counts H.labels n t Position) (hn : n < H.depth)
    (hp : H.pair n = .xz)
    (x : (Position → X) × InformedOutput (size H counts n t))
    (y : (Position → Y) × MissingOutput (size H counts n t))
    (z : (Position → Z) × InformedOutput (size H counts n t))
    (word : Position → A) (hword : Represents H id old x.1 y.1 z.1 word) :
    rawPoolLeadingXZ (actualPool counts H.labels n t id) (size H counts n t)
      (stageRefinementCount_pos counts H.labels n t) (actualPool_card counts H.labels n t id)
      (readXZX H id hp) (readXZZ H id hp) old x y z =
        if x.2.1 = y.2.1 ∧ x.2.1 = z.2.1 ∧
          eligible H id (appendCode old x.2.1) x.1 y.1 z.1 then
            (GeometricStageCoordinates.xz (size H counts n t)).tensor x.2.2 y.2.2 z.2.2
        else 0 := by
  have hx : readXZX H id hp old x.1 = fun i => H.labels n (word i) := by
    rw [hword.1]
    exact readXZX_on_original_word H id hp old word hn hword.2.2.2
  have hz : readXZZ H id hp old z.1 = fun i => H.labels n (word i) := by
    rw [hword.2.2.1]
    exact readXZZ_on_original_word H id hp old word hn hword.2.2.2
  unfold rawPoolLeadingXZ
  rw [rawPoolLeading_eq_decodedLeading
    (actualPool counts H.labels n t id) (size H counts n t)
    (stageRefinementCount_pos counts H.labels n t) (actualPool_card counts H.labels n t id)
    (readXZX H id hp) (readXZZ H id hp) (fun _ _ _ _ => fun i => H.labels n (word i))
    old x z y hx hz]
  unfold decodedLeading
  simp only [decode_eq_iff_eligible H old x.2.1 x.1 y.1 z.1 word hword,
    GeometricStageCoordinates.xz_tensor_apply]
  have hswap :
      (x.2.1 = z.2.1 ∧ x.2.1 = y.2.1 ∧
        eligible H id (appendCode old x.2.1) x.1 y.1 z.1 ∧ x.2.2 = z.2.2) ↔
      (x.2.1 = y.2.1 ∧ x.2.1 = z.2.1 ∧
        eligible H id (appendCode old x.2.1) x.1 y.1 z.1 ∧ x.2.2 = z.2.2) :=
    and_left_comm
  simp only [hswap, ite_and]

theorem raw_YZ_normal
    (old : ExactPrefix counts H.labels n t Position) (hn : n < H.depth)
    (hp : H.pair n = .yz)
    (x : (Position → X) × MissingOutput (size H counts n t))
    (y : (Position → Y) × InformedOutput (size H counts n t))
    (z : (Position → Z) × InformedOutput (size H counts n t))
    (word : Position → A) (hword : Represents H id old x.1 y.1 z.1 word) :
    rawPoolLeadingYZ (actualPool counts H.labels n t id) (size H counts n t)
      (stageRefinementCount_pos counts H.labels n t) (actualPool_card counts H.labels n t id)
      (readYZY H id hp) (readYZZ H id hp) old x y z =
        if x.2.1 = y.2.1 ∧ x.2.1 = z.2.1 ∧
          eligible H id (appendCode old x.2.1) x.1 y.1 z.1 then
            (GeometricStageCoordinates.yz (size H counts n t)).tensor x.2.2 y.2.2 z.2.2
        else 0 := by
  have hy : readYZY H id hp old y.1 = fun i => H.labels n (word i) := by
    rw [hword.2.1]
    exact readYZY_on_original_word H id hp old word hn hword.2.2.2
  have hz : readYZZ H id hp old z.1 = fun i => H.labels n (word i) := by
    rw [hword.2.2.1]
    exact readYZZ_on_original_word H id hp old word hn hword.2.2.2
  unfold rawPoolLeadingYZ
  rw [rawPoolLeading_eq_decodedLeading
    (actualPool counts H.labels n t id) (size H counts n t)
    (stageRefinementCount_pos counts H.labels n t) (actualPool_card counts H.labels n t id)
    (readYZY H id hp) (readYZZ H id hp) (fun _ _ _ _ => fun i => H.labels n (word i))
    old y z x hy hz]
  have hguard :
      (y.2.1 = z.2.1 ∧ y.2.1 = x.2.1 ∧
        decodePool (actualPool counts H.labels n t id) (size H counts n t)
          (actualPool_card counts H.labels n t id) old y.2.1 = (fun i => H.labels n (word i)) ∧
        y.2.2 = z.2.2) ↔
      (x.2.1 = y.2.1 ∧ x.2.1 = z.2.1 ∧
        eligible H id (appendCode old x.2.1) x.1 y.1 z.1 ∧ y.2.2 = z.2.2) := by
    constructor
    · rintro ⟨hyz, hyx, hdecode, hpair⟩
      refine ⟨hyx.symm, hyx.symm.trans hyz, ?_, hpair⟩
      apply (decode_eq_iff_eligible H old x.2.1 x.1 y.1 z.1 word hword).mp
      simpa only [hyx] using hdecode
    · rintro ⟨hxy, hxz, he, hpair⟩
      refine ⟨hxy.symm.trans hxz, hxy.symm, ?_, hpair⟩
      have hdecode := (decode_eq_iff_eligible H old x.2.1 x.1 y.1 z.1 word hword).mpr he
      simpa only [hxy] using hdecode
  unfold decodedLeading
  simp only [hguard, GeometricStageCoordinates.yz_tensor_apply]
  simp only [ite_and]

end MatrixMultiplication.CompletionGeometricValues

end

end OAI
