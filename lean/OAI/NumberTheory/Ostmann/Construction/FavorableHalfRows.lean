import OAI.NumberTheory.Ostmann.Construction.FavorableGiant
import OAI.NumberTheory.Ostmann.Construction.HalfSupport

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Construction

def favorableHalfRow (d : Decomposition) (P : Finset ℕ) (D p : ℕ) (u : List SmallSlot)
    (t : ZMod (halfProduct p u)) : ℂ := if p∈P then halfRow d D p u t else 0

theorem halfTransform_favorable (d : Decomposition) (P : Finset ℕ) (D p : ℕ)
    (u : List SmallSlot) (v : ℤ) :
    halfTransform (residueTransform d) (favorableGiantResidueTransform d P) D v p u=
      if p∈P then halfTransform (residueTransform d) (giantResidueTransform d) D v p u else 0 := by
  by_cases hp : p∈P <;> simp [halfTransform,favorableGiantResidueTransform,hp]

theorem favorableHalfRow_modFraction (d : Decomposition) (P : Finset ℕ) (D p H : ℕ)
    (u : List SmallSlot) (v : ℤ) (hp : ∀i,0<halfModuli p u i)
    (hc : Pairwise (fun i j => (halfModuli p u i).Coprime (halfModuli p u j)))
    (hD : ∀i,D.Coprime (halfModuli p u i)) (hH : H.Coprime (halfProduct p u)) :
    favorableHalfRow d P D p u (modFraction (halfProduct p u) v H)=
      halfTransform (residueTransform d) (favorableGiantResidueTransform d P) (D*H) v p u := by
  rw [halfTransform_favorable]
  unfold favorableHalfRow
  by_cases he : p∈P
  · simpa only [he,ite_true] using halfRow_modFraction d D p H u v hp hc hD hH
  · simp only [he,ite_false]

def halfRowValid (D p : ℕ) (u : List SmallSlot) : Prop :=
  Pairwise (fun i j => (halfModuli p u i).Coprime (halfModuli p u j)) ∧
    ∀i,D.Coprime (halfModuli p u i)

def guardedFavorableHalfRow (d : Decomposition) (P : Finset ℕ) (D p : ℕ)
    (u : List SmallSlot) (t : ZMod (halfProduct p u)) : ℂ := by
  classical
  exact if halfRowValid D p u then favorableHalfRow d P D p u t else 0

theorem guardedFavorableHalfRow_sq_norm_le (d : Decomposition) (P : Finset ℕ)
    (D p : ℕ) (u : List SmallSlot) [NeZero (halfProduct p u)]
    (hp : ∀i,Nat.Prime (halfModuli p u i)) :
    (∑t:ZMod (halfProduct p u),‖guardedFavorableHalfRow d P D p u t‖^2)≤(halfProduct p u:ℝ) := by
  by_cases hc : halfRowValid D p u
  · by_cases he : p∈P
    · simp only [guardedFavorableHalfRow,hc,ite_true,favorableHalfRow,he]
      exact halfRow_sq_norm_le d D p u hp hc.1 hc.2
    · simp [guardedFavorableHalfRow,hc,favorableHalfRow,he]
  · simp [guardedFavorableHalfRow,hc]

theorem actualCoefficient_row_factorization (d : Decomposition) (P : Finset ℕ)
    (sources : SourceFamily) (seed : List SourceSlot) (V : ℕ→ℕ) (X G : ℝ)
    (bins : List ℕ→State→ℝ) (outside : List ℕ) (l : ℕ) (a : State)
    (u h : List SmallSlot) (hs : a.small.Perm (u++h))
    (hp : 0<a.giantPlus) (hq : 0<a.giantMinus)
    (hu : ∀q∈u,0<q.value) (hh : ∀q∈h,0<q.value) :
    regularTransform (residueTransform d) (favorableGiantResidueTransform d P) outside a *
        actualCoefficient sources seed V X G (residueTransform d) bins outside l a =
      guardedFavorableHalfRow d P (outsideProduct outside) a.giantPlus u
        (modFraction (halfProduct a.giantPlus u) a.frequency (halfProduct a.giantMinus h)) *
      (halfTransform (residueTransform d) (favorableGiantResidueTransform d P)
        (outsideProduct outside*halfProduct a.giantPlus u) a.frequency a.giantMinus h *
        actualCoefficient sources seed V X G (residueTransform d) bins outside l a) := by
  by_cases hA : actualCoefficient sources seed V X G (residueTransform d) bins outside l a=0
  · simp only [hA,mul_zero]
  · have hroot := actualCoefficient_root_support sources seed V X G (residueTransform d)
      bins outside l a hA
    have hc := state_coprime_halves a u h outside hs hroot.2.2.2.1
    have hvalid : halfRowValid (outsideProduct outside) a.giantPlus u := ⟨hc.1,hc.2.1⟩
    rw [regularTransform_halves _ _ outside a u h hs hp hq hu hh,
      guardedFavorableHalfRow,ite_eq_left hvalid,
      favorableHalfRow_modFraction d P (outsideProduct outside) a.giantPlus
        (halfProduct a.giantMinus h) u a.frequency (by
          intro i
          refine Fin.cases ?_ (fun j => ?_) i
          · exact hp
          · exact hu u[j] (List.getElem_mem j.isLt)) hc.1 hc.2.1 hc.2.2]
    ring

end Ostmann.Construction

end

end OAI
