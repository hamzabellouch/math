import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumChosenSlots
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumOrdinalSlots

namespace OAI

/-! Apply explicit ordinal ranks to the cell-slot interface used by geometry. -/

noncomputable section
namespace ContinuumCoulomb.QuantumOrdinalPlacement

private theorem coordinates_eq {rows width : ℕ} (p q : QMAGridCell rows width) :
    (p.1.val,p.2.val) = (q.1.val,q.2.val) ↔ p=q := by
  constructor
  · intro h
    exact Prod.ext (Fin.ext (congrArg Prod.fst h)) (Fin.ext (congrArg Prod.snd h))
  · rintro rfl; rfl

 def coordinates {n rows width : ℕ} (cell : Fin n → QMAGridCell rows width) : Fin n → ℕ × ℕ :=
  fun q => ((cell q).1.val,(cell q).2.val)

 theorem fiber_card {n rows width : ℕ} (cell : Fin n → QMAGridCell rows width) (q : Fin n) :
    (Finset.univ.filter (fun r => coordinates cell r = coordinates cell q)).card =
      (Finset.univ.filter (fun r => cell r = cell q)).card := by
  congr 1
  apply Finset.filter_congr
  intro r _
  exact coordinates_eq _ _

 def slots {n rows width A : ℕ} (cell : Fin n → QMAGridCell rows width)
    (hd : ∀ p, (Finset.univ.filter (fun q => cell q=p)).card ≤ A) : QMACellSlots cell A where
  index q := ⟨QuantumOrdinalSlots.rank (coordinates cell) q,
    (QuantumOrdinalSlots.rank_lt_fiber (coordinates cell) q).trans_le
      (by rw [fiber_card]; exact hd (cell q))⟩
  injective := by
    intro q r hc hs
    apply QuantumOrdinalSlots.rank_injective_on_cell (coordinates cell)
    · exact (coordinates_eq _ _).mpr hc
    · exact congrArg Fin.val hs

end ContinuumCoulomb.QuantumOrdinalPlacement

end

end OAI
