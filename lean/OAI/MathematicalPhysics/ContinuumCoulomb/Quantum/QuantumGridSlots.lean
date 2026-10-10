import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumGridNeighbors

namespace OAI

/-! A bounded cell fiber admits distinct fine-grid slots for all its qubits. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical
variable {Q : Type*} [Fintype Q] {rows width A : ℕ}

def qmaGridFiberSlot (cell : Q → QMAGridCell rows width)
    (h : ∀ p, (Finset.univ.filter (fun q => cell q = p)).card ≤ A)
    (p : QMAGridCell rows width) : {q // cell q = p} ↪ Fin A :=
  (Fintype.equivFin {q // cell q = p}).toEmbedding.trans {
    toFun := fun i => ⟨i.val,lt_of_lt_of_le i.isLt (by
      simpa only [Fintype.card_subtype] using h p)⟩
    inj' := fun _ _ he => Fin.ext (congrArg (fun i : Fin A => i.val) he) }

def qmaGridSlot (cell : Q → QMAGridCell rows width)
    (h : ∀ p, (Finset.univ.filter (fun q => cell q = p)).card ≤ A) (q : Q) : Fin A :=
  qmaGridFiberSlot cell h (cell q) ⟨q,rfl⟩

theorem qmaGridSlot_eq (cell : Q → QMAGridCell rows width)
    (h : ∀ p, (Finset.univ.filter (fun q => cell q = p)).card ≤ A)
    (q : Q) (p : QMAGridCell rows width) (hq : cell q = p) :
    qmaGridSlot cell h q = qmaGridFiberSlot cell h p ⟨q,hq⟩ := by
  subst p
  rfl

theorem qmaGridSlot_injective_on_cell (cell : Q → QMAGridCell rows width)
    (h : ∀ p, (Finset.univ.filter (fun q => cell q = p)).card ≤ A)
    {q r : Q} (hc : cell q = cell r) (hs : qmaGridSlot cell h q = qmaGridSlot cell h r) : q = r := by
  have he : qmaGridFiberSlot cell h (cell r) ⟨q,hc⟩ =
      qmaGridFiberSlot cell h (cell r) ⟨r,rfl⟩ := by
    rw [qmaGridSlot_eq cell h q (cell r) hc] at hs
    exact hs
  exact congrArg Subtype.val ((qmaGridFiberSlot cell h (cell r)).injective he)

def qmaFineGridSite (cell : Q → QMAGridCell rows width)
    (h : ∀ p, (Finset.univ.filter (fun q => cell q = p)).card ≤ A) (q : Q) :
    Fin ((rows+1)*A) × Fin (width+1) :=
  (finProdFinEquiv ((cell q).1,qmaGridSlot cell h q),(cell q).2)

theorem qmaFineGridSite_injective (cell : Q → QMAGridCell rows width)
    (h : ∀ p, (Finset.univ.filter (fun q => cell q = p)).card ≤ A) :
    Function.Injective (qmaFineGridSite cell h) := by
  intro q r he
  have hx := finProdFinEquiv.injective (congrArg Prod.fst he)
  have hcol := congrArg Prod.snd he
  have hrow := congrArg Prod.fst hx
  have hslot := congrArg Prod.snd hx
  apply qmaGridSlot_injective_on_cell cell h (Prod.ext hrow hcol) hslot

theorem qmaFineGridSite_bounds (cell : Q → QMAGridCell rows width)
    (h : ∀ p, (Finset.univ.filter (fun q => cell q = p)).card ≤ A)
    (q : Q) (p : QMAGridCell rows width) (hne : QMAGridCellsNear (cell q) p) :
    (qmaFineGridSite cell h q).1.val < (p.1.val+2)*A ∧
    p.1.val*A ≤ (qmaFineGridSite cell h q).1.val+A ∧
    (qmaFineGridSite cell h q).2.val ≤ p.2.val+1 ∧
    p.2.val ≤ (qmaFineGridSite cell h q).2.val+1 := by
  obtain ⟨hr,hr',hc,hc'⟩ := hne
  have hs := (qmaGridSlot cell h q).isLt
  have hm := Nat.mul_le_mul_right A hr
  have hm' := Nat.mul_le_mul_right A hr'
  change (qmaGridSlot cell h q).val+A*(cell q).1.val < (p.1.val+2)*A ∧
    p.1.val*A ≤ (qmaGridSlot cell h q).val+A*(cell q).1.val+A ∧ _
  exact ⟨by nlinarith,by nlinarith,hc,hc'⟩

end ContinuumCoulomb

end

end OAI
