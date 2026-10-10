import OAI.Combinatorics.Ryser.Geometry.Basic
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.CardEmbedding
import Mathlib.Data.Finset.Card

namespace OAI

noncomputable section

namespace RyserCoveringCounterexample.LineCover

open scoped Classical

variable {F : Type*} [instFieldF : Field F] [instFintypeF : Fintype F] [instDecidableEqF : DecidableEq F]

abbrev LineTuple (F : Type*) (t : ℕ) := (Fin t ⊕ Fin t) ↪ AffineLine F

def crossPoints {t : ℕ} (a : LineTuple F t) : Finset (Point F) :=
  Finset.univ.filter fun x =>
    ∃ i j, Incidence x (a (Sum.inl i)) ∧ Incidence x (a (Sum.inr j))

def FiniteCrossings {t : ℕ} (a : LineTuple F t) : Prop :=
  ∀ i j, ∃ x, Incidence x (a (Sum.inl i)) ∧ Incidence x (a (Sum.inr j))

def tupleShapes {t : ℕ} (a : LineTuple F t) : Finset (Finset (Point F)) :=
  Finset.univ.image fun i => linePoints (a i)

def AdmissibleTuple (shapes : Finset (Finset (Point F))) (D h : ℕ)
    {t : ℕ} (a : LineTuple F t) : Prop :=
  FiniteCrossings a ∧ (crossPoints a).card = t * t ∧
    ∀ S ∈ shapes, S ∉ tupleShapes a → (S ∩ crossPoints a).card ≤ 2 * D * h

def SparseShapes (shapes : Finset (Finset (Point F))) (D : ℕ) : Prop :=
  ∀ S ∈ shapes, ∀ l : AffineLine F, S ≠ linePoints l →
    (S ∩ linePoints l).card ≤ D

def coverPencil (L : Finset (AffineLine F)) (p : ProjectivePoint F) :
    Finset (AffineLine F) :=
  L.filter fun l => ProjectiveIncidence p (some l)

@[simp] theorem mem_crossPoints {t : ℕ} (a : LineTuple F t) (x : Point F) :
    x ∈ crossPoints a ↔
      ∃ i j, Incidence x (a (Sum.inl i)) ∧ Incidence x (a (Sum.inr j)) := by
  simp only [crossPoints, Finset.mem_filter, Finset.mem_univ, true_and]

@[simp] theorem mem_tupleShapes {t : ℕ} (a : LineTuple F t)
    (S : Finset (Point F)) :
    S ∈ tupleShapes a ↔ ∃ i, linePoints (a i) = S := by
  simp only [tupleShapes, Finset.mem_image, Finset.mem_univ, true_and]

@[simp] theorem mem_coverPencil (L : Finset (AffineLine F))
    (p : ProjectivePoint F) (l : AffineLine F) :
    l ∈ coverPencil L p ↔ l ∈ L ∧ ProjectiveIncidence p (some l) := let _ := instFintypeF; by
  simp only [coverPencil, Finset.mem_filter]

theorem coverPencil_subset (L : Finset (AffineLine F)) (p : ProjectivePoint F) :
    coverPencil L p ⊆ L := let _ := instFintypeF; Finset.filter_subset _ _

theorem left_ne_right {t : ℕ} (a : LineTuple F t) (i j : Fin t) :
    a (Sum.inl i) ≠ a (Sum.inr j) := let _ := instFieldF; let _ := instFintypeF; let _ := instDecidableEqF; by
  intro h
  cases a.injective h

end RyserCoveringCounterexample.LineCover

end

end OAI
