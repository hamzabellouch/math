import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumManhattanRoute

namespace OAI

/-! Finite lattice routes stay in the neighboring coarse cells of their endpoints. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical

abbrev QMAFineGrid (rows width A : ℕ) := Fin ((rows+1)*A) × Fin (width+1)

def qmaFineGridCell {rows width A : ℕ} (hA : 0 < A) (p : QMAFineGrid rows width A) :
    QMAGridCell rows width :=
  (⟨p.1.val/A,(Nat.div_lt_iff_lt_mul hA).mpr p.1.isLt⟩,p.2)

theorem qmaFineGridCell_site {Q : Type*} [Fintype Q] {rows width A : ℕ}
    (cell : Q → QMAGridCell rows width)
    (h : ∀ p, (Finset.univ.filter (fun q => cell q = p)).card ≤ A) (hA : 0 < A) (q : Q) :
    qmaFineGridCell hA (qmaFineGridSite cell h q) = cell q := by
  apply Prod.ext
  · apply Fin.ext
    change ((qmaGridSlot cell h q).val+A*(cell q).1.val)/A = (cell q).1.val
    rw [Nat.add_mul_div_left _ _ hA,Nat.div_eq_of_lt (qmaGridSlot cell h q).isLt,zero_add]
  · rfl

def qmaFineGridNat {rows width A : ℕ} (p : QMAFineGrid rows width A) : ℕ × ℕ :=
  (p.1.val,p.2.val)

def qmaFineRoute {rows width A : ℕ} (p q : QMAFineGrid rows width A)
    (k : Fin (qmaManhattanLength (qmaFineGridNat p) (qmaFineGridNat q)+1)) :
    QMAFineGrid rows width A :=
  let z := qmaManhattanPoint (qmaFineGridNat p) (qmaFineGridNat q) k.val
  let hb := qmaManhattanPoint_bounds (qmaFineGridNat p) (qmaFineGridNat q) k.val (by omega)
  (⟨z.1,lt_of_le_of_lt hb.2.1 (max_lt p.1.isLt q.1.isLt)⟩,
   ⟨z.2,lt_of_le_of_lt hb.2.2.2 (max_lt p.2.isLt q.2.isLt)⟩)

@[simp] theorem qmaFineRoute_nat {rows width A : ℕ} (p q : QMAFineGrid rows width A)
    (k : Fin (qmaManhattanLength (qmaFineGridNat p) (qmaFineGridNat q)+1)) :
    qmaFineGridNat (qmaFineRoute p q k) = qmaManhattanPoint (qmaFineGridNat p) (qmaFineGridNat q) k.val := rfl

theorem qmaFineRoute_injective {rows width A : ℕ} (p q : QMAFineGrid rows width A) :
    Function.Injective (qmaFineRoute p q) := by
  intro a b hab
  exact qmaManhattanRoute_injective (qmaFineGridNat p) (qmaFineGridNat q)
    (congrArg qmaFineGridNat hab)

@[simp] theorem qmaFineRoute_zero {rows width A : ℕ} (p q : QMAFineGrid rows width A) :
    qmaFineRoute p q ⟨0,by omega⟩ = p := by
  apply Prod.ext <;> apply Fin.ext
  · exact congrArg Prod.fst (qmaManhattanPoint_zero (qmaFineGridNat p) (qmaFineGridNat q))
  · exact congrArg Prod.snd (qmaManhattanPoint_zero (qmaFineGridNat p) (qmaFineGridNat q))

@[simp] theorem qmaFineRoute_last {rows width A : ℕ} (p q : QMAFineGrid rows width A) :
    qmaFineRoute p q (Fin.last (qmaManhattanLength (qmaFineGridNat p) (qmaFineGridNat q))) = q := by
  apply Prod.ext <;> apply Fin.ext
  · exact congrArg Prod.fst (qmaManhattanPoint_last (qmaFineGridNat p) (qmaFineGridNat q))
  · exact congrArg Prod.snd (qmaManhattanPoint_last (qmaFineGridNat p) (qmaFineGridNat q))

theorem qmaFineRoute_step {rows width A : ℕ} (p q : QMAFineGrid rows width A)
    (k : Fin (qmaManhattanLength (qmaFineGridNat p) (qmaFineGridNat q))) :
    Nat.dist (qmaFineRoute p q k.castSucc).1.val (qmaFineRoute p q k.succ).1.val+
      Nat.dist (qmaFineRoute p q k.castSucc).2.val (qmaFineRoute p q k.succ).2.val = 1 :=
  qmaManhattanPoint_step (qmaFineGridNat p) (qmaFineGridNat q) k.val k.isLt

theorem qmaQuotient_bounds (p q x A : ℕ) (hl : min p q ≤ x) (hu : x ≤ max p q) :
    min (p/A) (q/A) ≤ x/A ∧ x/A ≤ max (p/A) (q/A) := by
  by_cases hpq : p ≤ q
  · have hd := Nat.div_le_div_right (c := A) hpq
    rw [min_eq_left hpq] at hl
    rw [max_eq_right hpq] at hu
    rw [min_eq_left hd,max_eq_right hd]
    exact ⟨Nat.div_le_div_right hl,Nat.div_le_div_right hu⟩
  · have hqp : q ≤ p := by omega
    have hd := Nat.div_le_div_right (c := A) hqp
    rw [min_eq_right hqp] at hl
    rw [max_eq_left hqp] at hu
    rw [min_eq_right hd,max_eq_left hd]
    exact ⟨Nat.div_le_div_right hl,Nat.div_le_div_right hu⟩

theorem qmaFineRoute_local {rows width A : ℕ} (hA : 0 < A)
    (p q : QMAFineGrid rows width A) (a : QMAGridCell rows width)
    (hp : QMAGridCellsNear (qmaFineGridCell hA p) a)
    (hq : QMAGridCellsNear (qmaFineGridCell hA q) a)
    (k : Fin (qmaManhattanLength (qmaFineGridNat p) (qmaFineGridNat q)+1)) :
    QMAGridCellsNear (qmaFineGridCell hA (qmaFineRoute p q k)) a := by
  have hb := qmaManhattanPoint_bounds (qmaFineGridNat p) (qmaFineGridNat q) k.val (by omega)
  have hd := qmaQuotient_bounds p.1.val q.1.val
    (qmaManhattanPoint (qmaFineGridNat p) (qmaFineGridNat q) k.val).1 A hb.1 hb.2.1
  dsimp [QMAGridCellsNear,qmaFineGridCell] at hp hq ⊢
  change _/A ≤ _ ∧ _ ≤ _/A+1 ∧ _ ≤ _ ∧ _ ≤ _
  dsimp only [qmaFineRoute]
  dsimp [qmaFineGridNat] at hb hd ⊢
  omega

end ContinuumCoulomb

end

end OAI
