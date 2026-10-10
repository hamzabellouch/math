import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumGridSlots
import Mathlib.Data.Nat.Dist
import Mathlib.Data.Int.NatAbs

namespace OAI

/-! Short, simple lattice paths between the bounded-density fine-grid sites. -/

namespace ContinuumCoulomb

def qmaAxisWalk (a b k : ℕ) : ℕ := if a ≤ b then a+k else a-k

@[simp] theorem qmaAxisWalk_zero (a b : ℕ) : qmaAxisWalk a b 0 = a := by
  simp [qmaAxisWalk]

@[simp] theorem qmaAxisWalk_last (a b : ℕ) : qmaAxisWalk a b (Nat.dist a b) = b := by
  unfold qmaAxisWalk Nat.dist
  split_ifs <;> omega

theorem qmaAxisWalk_distance (a b k : ℕ) (hk : k ≤ Nat.dist a b) :
    Nat.dist a (qmaAxisWalk a b k) = k := by
  unfold qmaAxisWalk Nat.dist at *
  split_ifs <;> omega

theorem qmaAxisWalk_step (a b k : ℕ) (hk : k < Nat.dist a b) :
    Nat.dist (qmaAxisWalk a b k) (qmaAxisWalk a b (k+1)) = 1 := by
  unfold qmaAxisWalk Nat.dist at *
  split_ifs <;> omega

theorem qmaAxisWalk_bounds (a b k : ℕ) (hk : k ≤ Nat.dist a b) :
    min a b ≤ qmaAxisWalk a b k ∧ qmaAxisWalk a b k ≤ max a b := by
  unfold qmaAxisWalk Nat.dist at *
  split_ifs <;> omega

def qmaManhattanLength (p q : ℕ × ℕ) : ℕ := Nat.dist p.1 q.1+Nat.dist p.2 q.2

def qmaManhattanPoint (p q : ℕ × ℕ) (k : ℕ) : ℕ × ℕ :=
  if k ≤ Nat.dist p.1 q.1 then (qmaAxisWalk p.1 q.1 k,p.2)
  else (q.1,qmaAxisWalk p.2 q.2 (k-Nat.dist p.1 q.1))

@[simp] theorem qmaManhattanPoint_zero (p q : ℕ × ℕ) : qmaManhattanPoint p q 0 = p := by
  simp [qmaManhattanPoint]

@[simp] theorem qmaManhattanPoint_last (p q : ℕ × ℕ) :
    qmaManhattanPoint p q (qmaManhattanLength p q) = q := by
  by_cases h : Nat.dist p.2 q.2 = 0
  · have he := Nat.eq_of_dist_eq_zero h
    simp [qmaManhattanLength,qmaManhattanPoint,he]
  · have hn : ¬qmaManhattanLength p q ≤ Nat.dist p.1 q.1 := by unfold qmaManhattanLength; omega
    simp only [qmaManhattanPoint,ite_eq_right hn]
    simp [qmaManhattanLength]

theorem qmaManhattanPoint_distance (p q : ℕ × ℕ) (k : ℕ) (hk : k ≤ qmaManhattanLength p q) :
    Nat.dist p.1 (qmaManhattanPoint p q k).1+
      Nat.dist p.2 (qmaManhattanPoint p q k).2 = k := by
  by_cases hx : k ≤ Nat.dist p.1 q.1
  · simp [qmaManhattanPoint,hx,qmaAxisWalk_distance _ _ _ hx]
  · have hy : k-Nat.dist p.1 q.1 ≤ Nat.dist p.2 q.2 := by unfold qmaManhattanLength at hk; omega
    simp only [qmaManhattanPoint,hx,ite_false]
    rw [qmaAxisWalk_distance _ _ _ hy]
    omega

theorem qmaManhattanPoint_step (p q : ℕ × ℕ) (k : ℕ) (hk : k < qmaManhattanLength p q) :
    Nat.dist (qmaManhattanPoint p q k).1 (qmaManhattanPoint p q (k+1)).1+
      Nat.dist (qmaManhattanPoint p q k).2 (qmaManhattanPoint p q (k+1)).2 = 1 := by
  by_cases hx : k < Nat.dist p.1 q.1
  · have hx0 : k ≤ Nat.dist p.1 q.1 := by omega
    have hx1 : k+1 ≤ Nat.dist p.1 q.1 := by omega
    simp [qmaManhattanPoint,hx0,hx1,qmaAxisWalk_step _ _ _ hx]
  · by_cases he : k = Nat.dist p.1 q.1
    · subst k
      have hy : 0 < Nat.dist p.2 q.2 := by unfold qmaManhattanLength at hk; omega
      simpa [qmaManhattanPoint] using qmaAxisWalk_step p.2 q.2 0 hy
    · have hx0 : ¬k ≤ Nat.dist p.1 q.1 := by omega
      have hx1 : ¬k+1 ≤ Nat.dist p.1 q.1 := by omega
      have hy : k-Nat.dist p.1 q.1 < Nat.dist p.2 q.2 := by unfold qmaManhattanLength at hk; omega
      have hs : k+1-Nat.dist p.1 q.1 = (k-Nat.dist p.1 q.1)+1 := by omega
      simp [qmaManhattanPoint,hx0,hx1,hs,qmaAxisWalk_step _ _ _ hy]

def qmaManhattanRoute (p q : ℕ × ℕ) : Fin (qmaManhattanLength p q+1) → ℕ × ℕ :=
  fun k => qmaManhattanPoint p q k.val

theorem qmaManhattanRoute_injective (p q : ℕ × ℕ) : Function.Injective (qmaManhattanRoute p q) := by
  intro a b hab
  apply Fin.ext
  have ha := qmaManhattanPoint_distance p q a.val (by omega)
  have hb := qmaManhattanPoint_distance p q b.val (by omega)
  change qmaManhattanPoint p q a.val = qmaManhattanPoint p q b.val at hab
  rw [hab] at ha
  omega

theorem qmaManhattanPoint_bounds (p q : ℕ × ℕ) (k : ℕ) (hk : k ≤ qmaManhattanLength p q) :
    min p.1 q.1 ≤ (qmaManhattanPoint p q k).1 ∧
    (qmaManhattanPoint p q k).1 ≤ max p.1 q.1 ∧
    min p.2 q.2 ≤ (qmaManhattanPoint p q k).2 ∧
    (qmaManhattanPoint p q k).2 ≤ max p.2 q.2 := by
  by_cases hx : k ≤ Nat.dist p.1 q.1
  · simpa only [qmaManhattanPoint,hx,ite_true] using
      And.intro (qmaAxisWalk_bounds _ _ _ hx).1
        (And.intro (qmaAxisWalk_bounds _ _ _ hx).2 (And.intro (min_le_left _ _) (le_max_left _ _)))
  · have hy : k-Nat.dist p.1 q.1 ≤ Nat.dist p.2 q.2 := by unfold qmaManhattanLength at hk; omega
    simpa only [qmaManhattanPoint,hx,ite_false] using
      And.intro (min_le_right _ _)
        (And.intro (le_max_right _ _) (qmaAxisWalk_bounds _ _ _ hy))

noncomputable def qmaFineGridPoint {Q : Type*} [Fintype Q] {rows width A : ℕ}
    (cell : Q → QMAGridCell rows width)
    (h : ∀ p, (Finset.univ.filter (fun q => cell q = p)).card ≤ A) (q : Q) : ℕ × ℕ :=
  ((qmaFineGridSite cell h q).1.val,(qmaFineGridSite cell h q).2.val)

theorem qmaFineGridPoint_length {Q : Type*} [Fintype Q] {rows width A : ℕ}
    (cell : Q → QMAGridCell rows width)
    (h : ∀ p, (Finset.univ.filter (fun q => cell q = p)).card ≤ A)
    (p q : Q) (a : QMAGridCell rows width)
    (hp : QMAGridCellsNear (cell p) a) (hq : QMAGridCellsNear (cell q) a) :
    qmaManhattanLength (qmaFineGridPoint cell h p) (qmaFineGridPoint cell h q) ≤ 3*A+2 := by
  obtain ⟨hp1,hp2,hp3,hp4⟩ := qmaFineGridSite_bounds cell h p a hp
  obtain ⟨hq1,hq2,hq3,hq4⟩ := qmaFineGridSite_bounds cell h q a hq
  simp only [Nat.add_mul] at hp1 hq1
  unfold qmaManhattanLength qmaFineGridPoint Nat.dist
  omega

theorem qmaNatDist_eq_int (a b : ℕ) : Nat.dist a b = Int.natAbs ((a:ℤ)-(b:ℤ)) := by
  by_cases h : a ≤ b
  · rw [Nat.dist_eq_sub_of_le h,Int.natAbs_natCast_sub_natCast_of_le h]
  · rw [Nat.dist_eq_sub_of_le_right (by omega),Int.natAbs_natCast_sub_natCast_of_ge (by omega)]

end ContinuumCoulomb

end OAI
