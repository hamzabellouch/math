import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumRawCellLocality
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumFourSpatial

namespace OAI

/-! The literal four-spin vertex numbers have exactly four copies of each
logical cell. This connects the emitted numeric list to bounded cell density. -/

noncomputable section
namespace ContinuumCoulomb.QuantumRawCellLocality
open QuantumForkList
open scoped Classical

def extendCell {n rows width : ℕ} (cell : Fin n → QMAGridCell rows width)
    (v : ℕ) : QMAGridCell rows width :=
  if h : v<n then cell ⟨v,h⟩ else (0,0)

theorem extendCell_fin {n rows width : ℕ} (cell : Fin n → QMAGridCell rows width)
    (i : Fin n) : extendCell cell i.val=cell i := by
  simp only [extendCell,i.isLt,↓reduceDIte]

theorem blockCell_fin {n rows width : ℕ} (cell : Fin n → QMAGridCell rows width)
    (i : Fin (n*4)) : blockCell (extendCell cell) i.val=qmaFourBlockCell cell i := by
  obtain ⟨⟨q,b⟩,rfl⟩ := (finProdFinEquiv : Fin n × Fin 4 ≃ Fin (n*4)).surjective i
  rw [qmaFourBlockCell,Equiv.symm_apply_apply]
  change extendCell cell ((b.val+4*q.val)/4)=cell q
  have hd : (b.val+4*q.val)/4=q.val := by have := b.isLt; omega
  rw [hd,extendCell_fin]

theorem blockCell_density {n rows width A : ℕ} (cell : Fin n → QMAGridCell rows width)
    (hc : ∀ p, (Finset.univ.filter (fun i => cell i=p)).card ≤ A)
    (p : QMAGridCell rows width) :
    qmaCellMass (fun i : Fin (n*4) => blockCell (extendCell cell) i.val) p ≤ 4*A := by
  have he : (fun i : Fin (n*4) => blockCell (extendCell cell) i.val)=qmaFourBlockCell cell :=
    funext (blockCell_fin cell)
  rw [he]
  simpa only [qmaCellMass,Finset.card_filter] using qmaFourBlockCell_density cell hc p

end ContinuumCoulomb.QuantumRawCellLocality

end

end OAI
