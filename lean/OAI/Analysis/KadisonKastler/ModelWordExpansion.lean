import OAI.Analysis.KadisonKastler.OrderedWordRows
import OAI.Analysis.KadisonKastler.IndexedCuts
import OAI.Analysis.KadisonKastler.TupleSplitting

namespace OAI

/-!
# Indexed cuts of actual words in the free diagonal model

The copy positions and the ordered labels are kept separate. Injectivity
of the copy positions supplies the off-copy relations, while splitting
the finite position list identifies each cut with its actual prefix,
middle letter, and suffix.
-/

namespace KadisonKastler

open Finset
open scoped BigOperators

noncomputable section

private theorem ofFn_split {B : Type*} {p q : ℕ} (f : Fin (p + q) → B) :
    List.ofFn f = List.ofFn (fun i => f (Fin.castAdd q i)) ++
      List.ofFn (fun i => f (Fin.natAdd p i)) := by
  rw [← List.ofFn_fin_append, Fin.append_castAdd_natAdd]

def cutPrefixIndex (p q : ℕ) (i : Fin p) : Fin (p + 1 + q) :=
  Fin.castAdd q (Fin.castAdd 1 i)

def cutMiddleIndex (p q : ℕ) : Fin (p + 1 + q) :=
  Fin.castAdd q (Fin.natAdd p (0 : Fin 1))

def cutSuffixIndex (p q : ℕ) (i : Fin q) : Fin (p + 1 + q) :=
  Fin.natAdd (p + 1) i

private theorem ofFn_split_middle (p q : ℕ) :
    List.ofFn (id : Fin (p + 1 + q) → Fin (p + 1 + q)) =
      List.ofFn (cutPrefixIndex p q) ++ cutMiddleIndex p q ::
        List.ofFn (cutSuffixIndex p q) := by
  rw [ofFn_split (id : Fin (p + 1 + q) → Fin (p + 1 + q))]
  change List.ofFn (Fin.castAdd q) ++ List.ofFn (cutSuffixIndex p q) = _
  rw [ofFn_split (Fin.castAdd q : Fin (p + 1) → Fin (p + 1 + q))]
  simp only [List.ofFn_succ, List.ofFn_zero, List.append_assoc,
    List.singleton_append, cutMiddleIndex]
  rfl

private theorem noPreservationCut_ofFn {B : Type*} [Semiring B] {p q : ℕ}
    (C A : Fin (p + q) → B) :
    noPreservationCut C A (List.ofFn id) p =
      (List.ofFn (fun i => C (Fin.castAdd q i))).prod *
        (List.ofFn (fun i => A (Fin.natAdd p i))).prod := by
  rw [ofFn_split (id : Fin (p + q) → Fin (p + q))]
  have h := noPreservationCut_append C A (List.ofFn (Fin.castAdd q))
    (List.ofFn (Fin.natAdd p))
  simpa only [List.length_ofFn, annihilationProduct, List.map_ofFn, Function.comp_def, id_eq] using h

private theorem preservationCut_ofFn {B : Type*} [Semiring B] {p q : ℕ}
    (C D A : Fin (p + 1 + q) → B) :
    preservationCut C D A (List.ofFn id) p =
      (List.ofFn (fun i => C (cutPrefixIndex p q i))).prod * D (cutMiddleIndex p q) *
        (List.ofFn (fun i => A (cutSuffixIndex p q i))).prod := by
  rw [ofFn_split_middle]
  have h := preservationCut_append C D A (List.ofFn (cutPrefixIndex p q))
    (List.ofFn (cutSuffixIndex p q)) (cutMiddleIndex p q)
  simpa only [List.length_ofFn, annihilationProduct, List.map_ofFn, Function.comp_def] using h

namespace FreeDiagonalModel

variable {ι α H : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M : FreeDiagonalModel ι α H) (W : Finset α)

def centeredWord {r : ℕ} (position : Fin r → ι) (t : OrderedLabelTuple W r) : H →L[ℂ] H :=
  tupleOperatorProduct (fun i => M.centered (position i)) t.val

def noPreservationWordCut {r : ℕ} (position : Fin r → ι) (t : OrderedLabelTuple W r)
    (k : ℕ) : H →L[ℂ] H :=
  noPreservationCut (fun i => M.C (position i) (t.val i))
    (fun i => star (M.C (position i) (t.val i))) (List.ofFn id) k

def preservationWordCut {r : ℕ} (position : Fin r → ι) (t : OrderedLabelTuple W r)
    (k : ℕ) : H →L[ℂ] H :=
  preservationCut (fun i => M.C (position i) (t.val i)) (fun i => M.D (position i) (t.val i))
    (fun i => star (M.C (position i) (t.val i))) (List.ofFn id) k

/-- Actual centered words split into their `r+1` cuts without preservation
and their `r` cuts with preservation. -/
theorem centeredWord_eq_cuts {r : ℕ} (position : Fin r → ι)
    (hposition : Function.Injective position) (t : OrderedLabelTuple W r) :
    M.centeredWord W position t =
      (∑ k ∈ range (r + 1), M.noPreservationWordCut W position t k) +
        ∑ k ∈ range r, M.preservationWordCut W position t k := by
  let C : Fin r → H →L[ℂ] H := fun i => M.C (position i) (t.val i)
  let D : Fin r → H →L[ℂ] H := fun i => M.D (position i) (t.val i)
  let A : Fin r → H →L[ℂ] H := fun i => star (M.C (position i) (t.val i))
  have he : M.centeredWord W position t = centeredLetterProduct C D A (List.ofFn id) := by
    unfold centeredWord tupleOperatorProduct centeredLetterProduct
    rw [List.map_ofFn]
    apply congrArg List.prod
    apply congrArg List.ofFn
    funext i
    exact M.centered_eq (position i) (t.val i)
  have h := centeredLetterProduct_eq_indexedCuts C D A
    (fun i j hij => M.star_creation_mul_creation (fun h => hij (hposition h)) (t.val i) (t.val j))
    (fun i j hij => M.star_creation_mul_D (fun h => hij (hposition h)) (t.val i) (t.val j))
    (fun i j hij => M.D_mul_creation (fun h => hij (hposition h)) (t.val i) (t.val j))
    (fun i j hij => M.D_mul_D (fun h => hij (hposition h)) (t.val i) (t.val j))
    (List.ofFn id) (List.nodup_ofFn_ofInjective Function.injective_id)
  rw [he]
  simpa only [List.length_ofFn, noPreservationWordCut, preservationWordCut, C, D, A] using h

theorem sum_centeredWord_eq_cuts {r : ℕ} (position : Fin r → ι)
    (hposition : Function.Injective position) :
    (∑ t : OrderedLabelTuple W r, M.centeredWord W position t) =
      (∑ k ∈ range (r + 1), ∑ t : OrderedLabelTuple W r,
        M.noPreservationWordCut W position t k) +
      ∑ k ∈ range r, ∑ t : OrderedLabelTuple W r, M.preservationWordCut W position t k := by
  simp_rw [M.centeredWord_eq_cuts W position hposition]
  rw [sum_add_distrib]
  congr 1 <;> rw [sum_comm]

/-- The cut before position `p` is exactly the creation prefix times
the annihilation suffix, with their original copy positions. -/
theorem noPreservationWordCut_eq {p q : ℕ} (position : Fin (p + q) → ι)
    (t : OrderedLabelTuple W (p + q)) :
    M.noPreservationWordCut W position t p =
      M.creationWord W (position ∘ Fin.castAdd q) (tupleInitial t) *
        M.annihilationWord W (position ∘ Fin.natAdd p) (tupleFinal t) := by
  unfold noPreservationWordCut
  rw [noPreservationCut_ofFn]
  rfl

/-- The cut at the distinguished middle position is the creation prefix,
the compressed centered projection, and the annihilation suffix. -/
theorem preservationWordCut_eq {p q : ℕ} (position : Fin (p + 1 + q) → ι)
    (t : OrderedLabelTuple W (p + 1 + q)) :
    M.preservationWordCut W position t p =
      M.creationWord W (position ∘ cutPrefixIndex p q) (tupleDropMiddle t).val.1 *
        M.D (position (cutMiddleIndex p q)) (tupleMiddle t) *
          M.annihilationWord W (position ∘ cutSuffixIndex p q) (tupleDropMiddle t).val.2 := by
  unfold preservationWordCut
  rw [preservationCut_ofFn]
  rfl

theorem sum_noPreservationWordCut_eq {p q : ℕ} (position : Fin (p + q) → ι) :
    (∑ t : OrderedLabelTuple W (p + q), M.noPreservationWordCut W position t p) =
      ∑ t : OrderedLabelTuple W (p + q),
        M.creationWord W (position ∘ Fin.castAdd q) (tupleInitial t) *
          M.annihilationWord W (position ∘ Fin.natAdd p) (tupleFinal t) := by
  apply sum_congr rfl
  intro t _
  exact M.noPreservationWordCut_eq W position t

theorem sum_preservationWordCut_eq {p q : ℕ} (position : Fin (p + 1 + q) → ι) :
    (∑ t : OrderedLabelTuple W (p + 1 + q), M.preservationWordCut W position t p) =
      ∑ t : OrderedLabelTuple W (p + 1 + q),
        M.creationWord W (position ∘ cutPrefixIndex p q) (tupleDropMiddle t).val.1 *
          M.D (position (cutMiddleIndex p q)) (tupleMiddle t) *
            M.annihilationWord W (position ∘ cutSuffixIndex p q) (tupleDropMiddle t).val.2 := by
  apply sum_congr rfl
  intro t _
  exact M.preservationWordCut_eq W position t

end FreeDiagonalModel

end

end KadisonKastler

end OAI
