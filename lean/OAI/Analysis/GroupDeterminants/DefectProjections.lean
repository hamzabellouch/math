import OAI.Analysis.GroupDeterminants.BinaryMatrices

namespace OAI

noncomputable section
open scoped BigOperators Pointwise

namespace GroupRingDeterminant
open LampDraft LampProjectionDraft
variable {H : Type} [Group H]

def lampRingEmbedding (R : Type) [Semiring R] :
    MonoidAlgebra R H →+* MonoidAlgebra R (LampGroup H) :=
  MonoidAlgebra.mapDomainRingHom R (shift H)

lemma lampRingEmbedding_injective (R : Type) [Semiring R] :
    Function.Injective (lampRingEmbedding (H := H) R) := by
  exact MonoidAlgebra.mapDomain_injective (shift_injective H)

lemma binaryProjection_isolates {a : MonoidAlgebra (ZMod 2) H} {h : H} {S : Finset H}
    (he : MonoidAlgebra.single h⁻¹ 1 * a = 1 + ∑ s ∈ S, MonoidAlgebra.single s 1) :
    binaryProjection H S * LampProjectionDraft.shiftSymbol H h⁻¹ *
      lampRingEmbedding (ZMod 2) a * binaryProjection H S = binaryProjection H S := by
  have hmap := congrArg (lampRingEmbedding (H := H) (ZMod 2)) he
  simp only [map_mul, map_add, map_one, map_sum] at hmap
  have hn : LampProjectionDraft.shiftSymbol H h⁻¹ * lampRingEmbedding (ZMod 2) a =
      1 + ∑ s ∈ S, LampProjectionDraft.shiftSymbol H s := by
    simpa [lampRingEmbedding, LampProjectionDraft.shiftSymbol] using hmap
  rw [mul_assoc (binaryProjection H S), hn, mul_add, mul_one, add_mul,
    (binaryProjection_idempotent H S).eq, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_eq_zero (fun s hs => binaryProjection_separates H S hs), add_zero]

lemma binary_defect_factorization_lamp {d : Type} [Fintype d] [DecidableEq d]
    (X Y : Matrix d d (MonoidAlgebra (ZMod 2) H)) (hXY : X * Y = 1) (hYX : Y * X ≠ 1) :
    ∃ S : Finset H, 1 ∉ S ∧
      ∃ u : Matrix (d ⊕ Unit) d (MonoidAlgebra (ZMod 2) (LampGroup H)),
      ∃ v : Matrix d (d ⊕ Unit) (MonoidAlgebra (ZMod 2) (LampGroup H)),
        u * v = Matrix.fromBlocks 1 0 0 (fun _ _ : Unit => binaryProjection H S) := by
  classical
  let C := 1 - Y * X
  have hC : C ≠ 0 := sub_ne_zero.mpr (Ne.symm hYX)
  obtain ⟨i, j, hij⟩ : ∃ i j, C i j ≠ 0 := by
    by_contra! he
    exact hC (Matrix.ext fun i j => he i j)
  obtain ⟨h, S, hS, he⟩ := binary_coefficient_normalize (C i j) hij
  let φ := lampRingEmbedding (H := H) (ZMod 2)
  let Xm := X.map φ
  let Ym := Y.map φ
  let Cm := C.map φ
  let p := binaryProjection H S
  let f : Matrix Unit d (MonoidAlgebra (ZMod 2) (LampGroup H)) :=
    Matrix.single () i (p * LampProjectionDraft.shiftSymbol H h⁻¹)
  let w : Matrix d Unit (MonoidAlgebra (ZMod 2) (LampGroup H)) := Matrix.single j () p
  have hXYm : Xm * Ym = 1 := by
    change X.map φ * Y.map φ = 1
    rw [← Matrix.map_mul, hXY, Matrix.map_one _ (map_zero _) (map_one _)]
  have hCm : Cm = 1 - Ym * Xm := by
    dsimp [Cm, C, Ym, Xm]
    rw [Matrix.map_sub _ (map_sub _) _ _, Matrix.map_one _ (map_zero _) (map_one _), Matrix.map_mul]
  have hfcw : f * Cm * w = fun _ _ : Unit => p := by
    apply Matrix.ext
    intro a b
    cases a; cases b
    dsimp only [f, w]
    rw [Matrix.mul_single_apply_same, Matrix.single_mul_apply_same]
    exact binaryProjection_isolates he
  refine ⟨S, hS, Matrix.fromRows Xm (f * Cm), Matrix.fromCols Ym (Cm * w), ?_⟩
  rw [hCm, defect_factorization Xm Ym hXYm f w, ← hCm, hfcw]

end GroupRingDeterminant

end

end OAI
