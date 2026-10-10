import OAI.Analysis.KadisonKastler.FreeDiagonalNormalForm
import OAI.Analysis.KadisonKastler.FaithfulTracePullback
import OAI.Analysis.KadisonKastler.TracialFiniteAveraging

namespace OAI

/-! # The faithful tracial Hilbert space of the generated diagonal algebra -/

namespace KadisonKastler

open scoped InnerProductSpace

noncomputable section

section Trace
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem inner_traceStateVector (τ : FaithfulTracialState A) (a b : A) :
    inner ℂ (traceStateVector τ a) (traceStateVector τ b) = τ.toLinearMap (star a * b) := by
  simp only [traceStateVector, UniformSpace.Completion.inner_coe,
    PositiveLinearMap.preGNS_inner_def, PositiveLinearMap.ofPreGNS_toPreGNS]
  rfl

def traceStateVectorContinuous (τ : FaithfulTracialState A) : A →L[ℂ] TraceStateHilbert τ :=
  (traceStateVectorLinear τ).mkContinuous 1 (fun a => by
    change ‖traceStateVector τ a‖ ≤ 1 * ‖a‖
    rw [one_mul, norm_traceStateVector]
    exact traceTwoNorm_le_norm τ a)

end Trace

variable {B : Type*} [CStarAlgebra B] {r d : ℕ}
  (τ : FaithfulTracialState B) (e : Fin r → Fin d → B)

theorem generatedDiagonal_generatedProjection_eq_top :
    generatedDiagonal (generatedDiagonalProjection e) = ⊤ := by
  let A := generatedDiagonal e
  let D := generatedDiagonal (generatedDiagonalProjection e)
  let S := D.map A.subtype
  have hA : IsClosed (A : Set B) := StarSubalgebra.isClosed_topologicalClosure _
  have hD : IsClosed (D : Set (generatedDiagonal e)) :=
    StarSubalgebra.isClosed_topologicalClosure _
  have hclosed : IsClosed (S : Set B) := hA.isClosedMap_subtype_val _ hD
  have hle : A ≤ S := by
    apply StarSubalgebra.topologicalClosure_minimal _ hclosed
    apply StarAlgebra.adjoin_le
    rintro x ⟨⟨i, a⟩, rfl⟩
    exact ⟨generatedDiagonalProjection e i a,
      mem_generatedDiagonal (generatedDiagonalProjection e) i a, rfl⟩
  apply top_unique
  intro x _
  obtain ⟨y, hy, he⟩ := hle x.property
  have hyx : y = x := Subtype.ext he
  exact hyx ▸ hy

def generatedDiagonalTrace : FaithfulTracialState (generatedDiagonal e) :=
  τ.comap (generatedDiagonal e).subtype Subtype.val_injective

@[simp] theorem generatedDiagonalTrace_apply (a : generatedDiagonal e) :
    (generatedDiagonalTrace τ e).toLinearMap a = τ.toLinearMap (a : B) := rfl

theorem generatedDiagonalProjection_isProjection
    (hp : ∀ i a, IsStarProjection (e i a)) (i : Fin r) (a : Fin d) :
    IsStarProjection (generatedDiagonalProjection e i a) := by
  constructor
  · apply Subtype.ext
    exact (hp i a).isIdempotentElem.eq
  · apply Subtype.ext
    exact (hp i a).isSelfAdjoint.star_eq

theorem generatedDiagonalProjection_orthogonal
    (ho : ∀ i a b, a ≠ b → e i a * e i b = 0)
    (i : Fin r) (a b : Fin d) (hab : a ≠ b) :
    generatedDiagonalProjection e i a * generatedDiagonalProjection e i b = 0 := by
  apply Subtype.ext
  exact ho i a b hab

theorem generatedDiagonalProjection_sum (hs : ∀ i, ∑ a, e i a = 1) (i : Fin r) :
    ∑ a, generatedDiagonalProjection e i a = 1 := by
  apply Subtype.ext
  change (generatedDiagonal e).subtype (∑ a, generatedDiagonalProjection e i a) = _
  rw [map_sum]
  exact hs i

@[simp] theorem generatedDiagonalLinearCombination_coe (i : Fin r) (c : Fin d → ℂ) :
    (↑(diagonalLinearCombination (generatedDiagonalProjection e) i c) : B) =
      diagonalLinearCombination e i c := by
  change (generatedDiagonal e).subtype (diagonalLinearCombination _ i c) = _
  simp only [diagonalLinearCombination, map_sum, map_smul]
  rfl

theorem generatedDiagonal_scalarFree (hf : ScalarFreeDiagonal τ e) :
    ScalarFreeDiagonal (generatedDiagonalTrace τ e) (generatedDiagonalProjection e) := by
  intro n hn position c hadj hc
  change τ.toLinearMap ((generatedDiagonal e).subtype
    ((List.ofFn (fun i => diagonalLinearCombination (generatedDiagonalProjection e)
      (position i) (c i))).prod)) = 0
  rw [map_list_prod, List.map_ofFn]
  change τ.toLinearMap ((List.ofFn (fun i =>
    (↑(diagonalLinearCombination (generatedDiagonalProjection e) (position i) (c i)) : B))).prod) = 0
  simp_rw [generatedDiagonalLinearCombination_coe]
  exact hf n hn position c hadj hc

@[simp] theorem generatedDiagonalCentered_coe (i : Fin r) (a : Fin d) :
    (↑(diagonalCentered (generatedDiagonalProjection e) i a) : B) = diagonalCentered e i a := rfl

@[simp] theorem generatedDiagonalWord_coe (w : List (Fin r × Fin d)) :
    (↑(diagonalWord (generatedDiagonalProjection e) w) : B) = diagonalWord e w := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    change (↑(diagonalCentered (generatedDiagonalProjection e) a.1 a.2) : B) *
      (↑(diagonalWord (generatedDiagonalProjection e) w) : B) = _
    rw [generatedDiagonalCentered_coe, ih, diagonalWord_cons]

variable [NeZero d]

theorem generatedDiagonal_trace_reduced_word
    (hs : ∀ i, ∑ a, e i a = 1) (hf : ScalarFreeDiagonal τ e)
    {w : List (Fin r × Fin d)} (hw : ReducedDiagonalWord w) (hne : w ≠ []) :
    (generatedDiagonalTrace τ e).toLinearMap
      (diagonalWord (generatedDiagonalProjection e) w) = 0 := by
  rw [generatedDiagonalTrace_apply, generatedDiagonalWord_coe]
  exact trace_reducedDiagonalWord e τ hs hf hw hne

end

end KadisonKastler

end OAI
