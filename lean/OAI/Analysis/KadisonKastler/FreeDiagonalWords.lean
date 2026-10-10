import OAI.Analysis.KadisonKastler.FreeDiagonalLetters
import Mathlib.Data.List.Chain
import Mathlib.Data.List.ChainOfFn

namespace OAI

/-! # Reduced centered words in the finite diagonal family -/

namespace KadisonKastler

open scoped BigOperators

noncomputable section

variable {B : Type*} [CStarAlgebra B] {r d : ℕ}
  (e : Fin r → Fin d → B)

def diagonalWord (w : List (Fin r × Fin d)) : B :=
  (w.map (fun a => diagonalCentered e a.1 a.2)).prod

def ReducedDiagonalWord (w : List (Fin r × Fin d)) : Prop :=
  w.IsChain (fun a b => a.1 ≠ b.1)

theorem ReducedDiagonalWord.reverse {w : List (Fin r × Fin d)}
    (hw : ReducedDiagonalWord w) : ReducedDiagonalWord w.reverse :=
  List.isChain_reverse.mpr (hw.imp (fun _ _ h => Ne.symm h))

theorem ReducedDiagonalWord.join_reverse
    {a b : Fin r × Fin d} {w v : List (Fin r × Fin d)}
    (hw : ReducedDiagonalWord (a :: w)) (hv : ReducedDiagonalWord (b :: v))
    (hab : a.1 ≠ b.1) : ReducedDiagonalWord ((a :: w).reverse ++ b :: v) := by
  apply hw.reverse.append hv
  simpa using hab

@[simp] theorem diagonalWord_nil : diagonalWord e [] = 1 := rfl

@[simp] theorem diagonalWord_cons (a : Fin r × Fin d) (w : List (Fin r × Fin d)) :
    diagonalWord e (a :: w) = diagonalCentered e a.1 a.2 * diagonalWord e w := rfl

theorem diagonalWord_append (w v : List (Fin r × Fin d)) :
    diagonalWord e (w ++ v) = diagonalWord e w * diagonalWord e v := by
  simp [diagonalWord]

theorem star_diagonalWord (hp : ∀ i a, IsStarProjection (e i a))
    (w : List (Fin r × Fin d)) : star (diagonalWord e w) = diagonalWord e w.reverse := by
  induction w with
  | nil => simp
  | cons a w ih =>
    simp only [diagonalWord_cons, star_mul, star_diagonalCentered e hp, ih,
      List.reverse_cons, diagonalWord_append]
    simp

variable [NeZero d]

theorem trace_reducedDiagonalWord (τ : FaithfulTracialState B)
    (hs : ∀ i, ∑ a, e i a = 1) (hf : ScalarFreeDiagonal τ e)
    {w : List (Fin r × Fin d)} (hw : ReducedDiagonalWord w) (hne : w ≠ []) :
    τ.toLinearMap (diagonalWord e w) = 0 := by
  have hadj : ∀ i j : Fin w.length, i.val + 1 = j.val →
      (w.get i).1 ≠ (w.get j).1 := by
    intro i j hij
    have h := (List.isChain_iff_getElem.mp hw) i.val (by omega)
    simpa only [List.get_eq_getElem, hij] using h
  have h := hf w.length (List.length_pos_iff.mpr hne)
    (fun i => (w.get i).1) (fun i => diagonalCenteredCoefficient (w.get i).2)
    hadj (fun i => by simpa only [Fintype.card_fin] using
      sum_diagonalCenteredCoefficient (w.get i).2)
  change τ.toLinearMap ((List.ofFn (fun i : Fin w.length =>
    diagonalLinearCombination e (w.get i).1 (diagonalCenteredCoefficient (w.get i).2))).prod) = 0 at h
  simp_rw [← diagonalCentered_eq_linearCombination e hs] at h
  change τ.toLinearMap ((List.ofFn
    ((fun a : Fin r × Fin d => diagonalCentered e a.1 a.2) ∘ w.get)).prod) = 0 at h
  rw [← List.map_ofFn, List.ofFn_get] at h
  exact h

theorem trace_diagonalWord_cross (τ : FaithfulTracialState B)
    (hp : ∀ i a, IsStarProjection (e i a)) (hs : ∀ i, ∑ a, e i a = 1)
    (hf : ScalarFreeDiagonal τ e)
    {a b : Fin r × Fin d} {w v : List (Fin r × Fin d)}
    (hw : ReducedDiagonalWord (a :: w)) (hv : ReducedDiagonalWord (b :: v))
    (hab : a.1 ≠ b.1) :
    τ.toLinearMap (star (diagonalWord e (a :: w)) * diagonalWord e (b :: v)) = 0 := by
  rw [star_diagonalWord e hp, ← diagonalWord_append]
  exact trace_reducedDiagonalWord e τ hs hf (hw.join_reverse hv hab) (by simp)

end

end KadisonKastler

end OAI
