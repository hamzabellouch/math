import OAI.LinearAlgebra.MatrixMultiplication.Tensor.ComplexTensorRestrictionComposition
import OAI.LinearAlgebra.MatrixMultiplication.Separation.FiniteCover
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Powerset

namespace OAI

/-! Finite orbit symmetries, masks and exact recovery operations. -/

open scoped BigOperators
open MatrixMultiplication.Foundation

namespace MatrixMultiplication.ExactRecovery

variable {K X Y Z I A B C : Type*} [CommSemiring K]

def delete (Q : Tensor K X Y Z) (px : X → Prop) (py : Y → Prop)
    (pz : Z → Prop) [DecidablePred px] [DecidablePred py] [DecidablePred pz] :
    Tensor K X Y Z := fun x y z => if px x ∧ py y ∧ pz z then Q x y z else 0

def presence [Fintype I] [DecidableEq I] (p : I → X → Prop)
    [∀ i, DecidablePred (p i)] (x : X) : Finset I :=
  Finset.univ.filter fun i => p i x

@[simp] theorem mem_presence [Fintype I] [DecidableEq I] (p : I → X → Prop)
    [∀ i, DecidablePred (p i)] (x : X) (i : I) :
    i ∈ presence p x ↔ p i x := by simp [presence]

theorem restrict_rectangles
    [Fintype X] [Fintype Y] [Fintype Z]
    [Fintype A] [Fintype B] [Fintype C]
    [DecidableEq X] [DecidableEq Y] [DecidableEq Z]
    [DecidableEq A] [DecidableEq B] [DecidableEq C]
    (Q H : Tensor K X Y Z) (cx : X → A) (cy : Y → B) (cz : Z → C)
    (fx : A × B × C → X → X) (fy : A × B × C → Y → Y)
    (fz : A × B × C → Z → Z)
    (h : ∀ x y z, H (fx (cx x, cy y, cz z) x)
      (fy (cx x, cy y, cz z) y) (fz (cx x, cy y, cz z) z) = Q x y z) :
    Tensor.restrict
      (fun x s => if cx x = s.1.1 ∧ s.2 = fx s.1 x then (1 : K) else 0)
      (fun y s => if cy y = s.1.2.1 ∧ s.2 = fy s.1 y then (1 : K) else 0)
      (fun z s => if cz z = s.1.2.2 ∧ s.2 = fz s.1 z then (1 : K) else 0)
      (Tensor.directSum (fun _ : A × B × C => H)) = Q := by
  funext x y z
  simp [Tensor.restrict, Tensor.directSum, Fintype.sum_prod_type,
    ite_and, ite_mul, mul_ite, h]

theorem repair_of_cover
    [Fintype X] [Fintype Y] [Fintype Z] [Fintype I] [DecidableEq I] [Nonempty I]
    (Q H : Tensor K X Y Z)
    (px : I → X → Prop) (py : I → Y → Prop) (pz : I → Z → Prop)
    (fx : I → X → X) (fy : I → Y → Y) (fz : I → Z → Z)
    (hshift : ∀ i x y z, H (fx i x) (fy i y) (fz i z) =
      @delete K X Y Z _ Q (px i) (py i) (pz i)
        (Classical.decPred _) (Classical.decPred _) (Classical.decPred _) x y z)
    (hcover : ∀ x y z, Q x y z ≠ 0 → ∃ i, px i x ∧ py i y ∧ pz i z) :
    ∃ (a : X → ((Finset I × Finset I × Finset I) × X) → K)
      (b : Y → ((Finset I × Finset I × Finset I) × Y) → K)
      (c : Z → ((Finset I × Finset I × Finset I) × Z) → K),
      Tensor.restrict a b c
        (Tensor.directSum (fun _ : Finset I × Finset I × Finset I => H)) = Q := by
  classical
  let pick : Finset I × Finset I × Finset I → I := fun r =>
    if h : ∃ i, i ∈ r.1 ∧ i ∈ r.2.1 ∧ i ∈ r.2.2 then Classical.choose h
    else Classical.choice inferInstance
  have hpick (r : Finset I × Finset I × Finset I)
      (hr : ∃ i, i ∈ r.1 ∧ i ∈ r.2.1 ∧ i ∈ r.2.2) :
      pick r ∈ r.1 ∧ pick r ∈ r.2.1 ∧ pick r ∈ r.2.2 := by
    simpa [pick, hr] using Classical.choose_spec hr
  let cx := presence px
  let cy := presence py
  let cz := presence pz
  have hrect (x : X) (y : Y) (z : Z) :
      H (fx (pick (cx x, cy y, cz z)) x)
        (fy (pick (cx x, cy y, cz z)) y)
        (fz (pick (cx x, cy y, cz z)) z) = Q x y z := by
    rw [hshift]
    by_cases hq : Q x y z = 0
    · simp [delete, hq]
    · rcases hcover x y z hq with ⟨i, hix, hiy, hiz⟩
      have hp := hpick (cx x, cy y, cz z)
        ⟨i, by simpa [cx] using hix, by simpa [cy] using hiy,
          by simpa [cz] using hiz⟩
      have hpx : px (pick (cx x, cy y, cz z)) x := by simpa [cx] using hp.1
      have hpy : py (pick (cx x, cy y, cz z)) y := by simpa [cy] using hp.2.1
      have hpz : pz (pick (cx x, cy y, cz z)) z := by simpa [cz] using hp.2.2
      simp [delete, hpx, hpy, hpz]
  exact ⟨_, _, _, restrict_rectangles Q H cx cy cz
    (fun r => fx (pick r)) (fun r => fy (pick r)) (fun r => fz (pick r)) hrect⟩

theorem card_mask_rectangles [Fintype I] :
    Fintype.card (Finset I × Finset I × Finset I) = 2 ^ (3 * Fintype.card I) := by
  classical
  simp only [Fintype.card_prod, Fintype.card_finset]
  rw [Nat.mul_comm 3 (Fintype.card I), pow_mul]
  simp [pow_succ, mul_assoc]

theorem repair_of_counting
    [Fintype X] [Fintype Y] [Fintype Z] [Fintype I]
    [DecidableEq X] [DecidableEq Y] [DecidableEq Z] [DecidableEq I]
    (Q H : Tensor K X Y Z)
    (px : I → X → Prop) (py : I → Y → Prop) (pz : I → Z → Prop)
    (fx : I → X → X) (fy : I → Y → Y) (fz : I → Z → Z)
    (hshift : ∀ i x y z, H (fx i x) (fy i y) (fz i z) =
      @delete K X Y Z _ Q (px i) (py i) (pz i)
        (Classical.decPred _) (Classical.decPred _) (Classical.decPred _) x y z)
    (t L : ℕ) (hL : 0 < L)
    (hbad : ∀ x y z, Q x y z ≠ 0 →
      (@Finset.filter I (fun i => ¬(px i x ∧ py i y ∧ pz i z))
        (Classical.decPred _) Finset.univ).card ≤ t)
    (hbudget : (@Finset.filter (X × Y × Z)
      (fun p => Q p.1 p.2.1 p.2.2 ≠ 0) (Classical.decPred _) Finset.univ).card * t ^ L <
        Fintype.card I ^ L) :
    ∃ (a : X → ((Finset (Fin L) × Finset (Fin L) × Finset (Fin L)) × X) → K)
      (b : Y → ((Finset (Fin L) × Finset (Fin L) × Finset (Fin L)) × Y) → K)
      (c : Z → ((Finset (Fin L) × Finset (Fin L) × Finset (Fin L)) × Z) → K),
      Tensor.restrict a b c
        (Tensor.directSum (fun _ : Finset (Fin L) × Finset (Fin L) × Finset (Fin L) => H)) = Q := by
  classical
  let support : Finset (X × Y × Z) := @Finset.filter (X × Y × Z)
    (fun p => Q p.1 p.2.1 p.2.2 ≠ 0) (Classical.decPred _) Finset.univ
  let good (i : I) (p : X × Y × Z) : Prop := px i p.1 ∧ py i p.2.1 ∧ pz i p.2.2
  have hbad' : ∀ p ∈ support, (Finset.univ.filter fun i => ¬good i p).card ≤ t := by
    intro p hp
    have heq : (Finset.univ.filter fun i => ¬good i p) =
        @Finset.filter I (fun i => ¬(px i p.1 ∧ py i p.2.1 ∧ pz i p.2.2))
          (Classical.decPred _) Finset.univ := by
      ext i
      simp only [Finset.mem_filter, good]
    rw [heq]
    apply hbad p.1 p.2.1 p.2.2
    simpa only [support, Finset.mem_filter, Finset.mem_univ, true_and] using hp
  obtain ⟨f, hf⟩ := FiniteCover.exists_cover support good t L hbad' hbudget
  let : Nonempty (Fin L) := ⟨⟨0, hL⟩⟩
  exact repair_of_cover Q H (fun i => px (f i)) (fun i => py (f i))
    (fun i => pz (f i)) (fun i => fx (f i)) (fun i => fy (f i))
    (fun i => fz (f i)) (fun i => hshift (f i))
    (fun x y z hq => hf (x, y, z) (by simp [support, hq]))

end MatrixMultiplication.ExactRecovery

end OAI
