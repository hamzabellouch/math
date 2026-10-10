import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumGridSlots

namespace OAI

/-! A constant number of spatial colors separates overlapping local interactions. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical
variable {E : Type*} [Fintype E] {rows width B : ℕ}

def qmaGridColor (anchor : E → QMAGridCell rows width)
    (h : ∀ p, (Finset.univ.filter (fun e => anchor e = p)).card ≤ B) (e : E) :
    Fin 3 × Fin 3 × Fin B :=
  (⟨(anchor e).1.val%3,Nat.mod_lt _ (by decide)⟩,
   ⟨(anchor e).2.val%3,Nat.mod_lt _ (by decide)⟩,qmaGridSlot anchor h e)

theorem qmaGridColor_eq (anchor : E → QMAGridCell rows width)
    (h : ∀ p, (Finset.univ.filter (fun e => anchor e = p)).card ≤ B)
    {e f : E} (hcolor : qmaGridColor anchor h e = qmaGridColor anchor h f)
    (hr : (anchor e).1.val ≤ (anchor f).1.val+2)
    (hr' : (anchor f).1.val ≤ (anchor e).1.val+2)
    (hc : (anchor e).2.val ≤ (anchor f).2.val+2)
    (hc' : (anchor f).2.val ≤ (anchor e).2.val+2) : e = f := by
  have hrow := congrArg (fun c : Fin 3 × Fin 3 × Fin B => c.1.val) hcolor
  have hcol := congrArg (fun c : Fin 3 × Fin 3 × Fin B => c.2.1.val) hcolor
  have hslot := congrArg (fun c : Fin 3 × Fin 3 × Fin B => c.2.2) hcolor
  change (anchor e).1.val%3 = (anchor f).1.val%3 at hrow
  change (anchor e).2.val%3 = (anchor f).2.val%3 at hcol
  apply qmaGridSlot_injective_on_cell anchor h _ hslot
  apply Prod.ext <;> apply Fin.ext <;> omega

theorem qmaGridColor_disjoint {Q : Type*} (cell : Q → QMAGridCell rows width)
    (anchor : E → QMAGridCell rows width) (sites : E → Finset Q)
    (h : ∀ p, (Finset.univ.filter (fun e => anchor e = p)).card ≤ B)
    (hlocal : ∀ e, ∀ q ∈ sites e, QMAGridCellsNear (cell q) (anchor e))
    {e f : E} (hef : e ≠ f) (hcolor : qmaGridColor anchor h e = qmaGridColor anchor h f) :
    Disjoint (sites e) (sites f) := by
  apply Finset.disjoint_left.mpr
  intro q he hf
  have ha := hlocal e q he
  have hb := hlocal f q hf
  apply hef
  apply qmaGridColor_eq anchor h hcolor <;> dsimp [QMAGridCellsNear] at ha hb <;> omega

theorem qmaGridColor_card : Fintype.card (Fin 3 × Fin 3 × Fin B) = 9*B := by
  simp only [Fintype.card_prod,Fintype.card_fin]
  omega

end ContinuumCoulomb

end

end OAI
