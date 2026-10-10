import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumForkListInitialSpatial
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumRawCellDensity
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumOrderedSpatialComplete
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumHistoryDegree

namespace OAI

/-! Spatial input data for the actual six-stage and four-spin compiler,
using the exact numeric qubit order and full emitted bond list. -/

noncomputable section
namespace ContinuumCoulomb.QuantumOrderedOutputSpatial
open QuantumOrderedLabelTable QuantumOrderedSpatialComplete QuantumRawCellLocality
open scoped Classical
variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
variable {n m rows width : ℕ}

local instance gridDecision (r w : ℕ) : DecidableEq (QMAGridCell r w) := Classical.decEq _

def logicalCell (q : Fin n ≃ ι) (e : Fin m ≃ κ)
    (cell : ι → QMAGridCell rows width) (anchor : κ → QMAGridCell rows width) :
    Fin (finalCount n m) → QMAGridCell rows width :=
  fun i => cell6 cell anchor (qubits6 q e i)

def physicalCell (q : Fin n ≃ ι) (e : Fin m ≃ κ)
    (cell : ι → QMAGridCell rows width) (anchor : κ → QMAGridCell rows width) :
    ℕ → QMAGridCell rows width := blockCell (QuantumRawCellLocality.extendCell (logicalCell q e cell anchor))

omit [DecidableEq ι] [DecidableEq κ] in
theorem logical_density (q : Fin n ≃ ι) (e : Fin m ≃ κ)
    (cell : ι → QMAGridCell rows width) (anchor : κ → QMAGridCell rows width)
    {A B : ℕ} (hc : ∀ p, (Finset.univ.filter (fun i => cell i=p)).card ≤ A)
    (ha : ∀ p, (Finset.univ.filter (fun i => anchor i=p)).card ≤ B)
    (p : QMAGridCell rows width) :
    (Finset.univ.filter (fun i => logicalCell q e cell anchor i=p)).card ≤ A+3717*B := by
  have he : (Finset.univ.filter (fun i => logicalCell q e cell anchor i=p)).card =
      (Finset.univ.filter (fun i => cell6 cell anchor i=p)).card := by
    apply Finset.card_equiv (qubits6 q e)
    intro i
    constructor <;> intro h
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp h).2⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp h).2⟩
  rw [he]
  exact (complete_density (ι := ι) (κ := κ) (A := A) (B := B) cell anchor hc ha).1 p

theorem output_local (q : Fin n ≃ ι) (e : Fin m ≃ κ)
    (xs : κ → List ι) (w : κ → ι → Fin 4) (J : κ → ℚ)
    (hlen : ∀ a, (xs a).length ≤ 6) (hdup : ∀ a, (xs a).Nodup)
    (cell : ι → QMAGridCell rows width) (anchor : κ → QMAGridCell rows width)
    (hx : ∀ a i, i ∈ xs a → QMAGridCellsNear (cell i) (anchor a)) (N : ℕ) :
    QuantumForkList.BondLocal
      (QuantumOrderedLabelCompile.output (N,n,table e (index q) xs w J)).1
      (physicalCell q e cell anchor) QuantumForkList.CommonCell := by
  rw [QuantumOrderedLabelCompile.output_table q e xs w J hlen hdup N]
  apply QuantumRawCellLocality.output_local N _ _ _ _ (fun a => anchor6 anchor (terms6 e a))
  intro a i hi
  obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hi
  rw [extendCell_fin (logicalCell q e cell anchor) ((qubits6 q e).symm j)]
  change QMAGridCellsNear (cell6 cell anchor (qubits6 q e ((qubits6 q e).symm j))) _
  rw [Equiv.apply_symm_apply]
  exact complete_geometry xs w hlen cell anchor QMAGridCellsNear
    qmaGridCellsNear_refl hx (terms6 e a) j hj

def input (q : Fin n ≃ ι) (e : Fin m ≃ κ)
    (xs : κ → List ι) (w : κ → ι → Fin 4) (J : κ → ℚ)
    (hlen : ∀ a, (xs a).length ≤ 6) (hdup : ∀ a, (xs a).Nodup)
    (cell : ι → QMAGridCell rows width) (anchor : κ → QMAGridCell rows width)
    {A B D : ℕ} (hc : ∀ p, (Finset.univ.filter (fun i => cell i=p)).card ≤ A)
    (ha : ∀ p, (Finset.univ.filter (fun i => anchor i=p)).card ≤ B)
    (hx : ∀ a i, i ∈ xs a → QMAGridCellsNear (cell i) (anchor a))
    (hD : 1 ≤ D) (hi : QuantumOrderedIncidence.Bounded xs D) (N : ℕ) :
    QuantumForkList.SpatialInput rows width (4*(A+3717*B)) (6+22*(12544*D)) where
  n := QuantumOrderedLabelCompile.qubitCount (N,n,table e (index q) xs w J)
  bonds := (QuantumOrderedLabelCompile.output (N,n,table e (index q) xs w J)).1
  constant := (QuantumOrderedLabelCompile.output (N,n,table e (index q) xs w J)).2
  precision := N
  cell := physicalCell q e cell anchor
  bounded := fun b hb => ⟨(QuantumOrderedLabelCompile.output_valid q e xs w J hlen hdup N b hb).1,
    (QuantumOrderedLabelCompile.output_valid q e xs w J hlen hdup N b hb).2.1⟩
  noLoops := fun b hb => (QuantumOrderedLabelCompile.output_valid q e xs w J hlen hdup N b hb).2.2
  degree := fun v => QuantumOrderedLabelCompile.output_degree q e xs w J hlen hdup hD hi N v.val v.isLt
  density := by
    intro p
    have hn : QuantumOrderedLabelCompile.qubitCount (N,n,table e (index q) xs w J)=
        finalCount n m*4 := by
      rw [QuantumOrderedLabelCompile.qubitCount_table,finalCount_eq]
      omega
    rw [hn]
    apply blockCell_density (logicalCell q e cell anchor) ?_ p
    intro a
    convert logical_density q e cell anchor hc ha a using 1; congr
  locality := output_local q e xs w J hlen hdup cell anchor hx N

end ContinuumCoulomb.QuantumOrderedOutputSpatial

end

end OAI
