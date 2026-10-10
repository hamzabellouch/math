import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumRawIncidence
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumForkListSpatialPackage

namespace OAI

/-! The actual four-spin output list has a common neighboring coarse cell
for both endpoints of every bond, including all zero-weight terms. -/

noncomputable section
namespace ContinuumCoulomb.QuantumRawCellLocality
open QuantumRawExchange QuantumRawIncidence QuantumForkList MediatorListProgram
open scoped Classical

def blockCell {rows width : ℕ} (cell : ℕ → QMAGridCell rows width) (v : ℕ) := cell (v/4)

theorem penalty_local {rows width : ℕ} (n : ℕ) (r : ℚ)
    (cell : ℕ → QMAGridCell rows width) :
    BondLocal (penalty n r) (blockCell cell) CommonCell := by
  intro b hb
  obtain ⟨bs,hbs,hb⟩ := List.mem_flatten.mp hb
  obtain ⟨i,_,rfl⟩ := List.mem_map.mp hbs
  obtain ⟨e,rfl⟩ := List.mem_ofFn.mp hb
  change CommonCell (cell ((4*i+(qmaFourEdgeLeft e).val)/4))
    (cell ((4*i+(qmaFourEdgeRight e).val)/4))
  rw [slot_div,slot_div]
  exact commonCell_refl _

theorem term_local {n rows width : ℕ} (k : ℕ) (r : ℚ) (xs : List (Fin n))
    (w : Fin n → Fin 4) (J : ℚ) (cell : ℕ → QMAGridCell rows width)
    (anchor : QMAGridCell rows width)
    (hx : ∀ i ∈ xs, QMAGridCellsNear (cell i.val) anchor) :
    BondLocal (bonds ((k,r),pack (QuantumOrderedXZTerm.ofSites xs w) J))
      (blockCell cell) CommonCell := by
  intro b hb
  obtain ⟨i,hi,he⟩ := packed_origin k r _ J b hb b.1 (Or.inl rfl)
  obtain ⟨j,hj,hf⟩ := packed_origin k r _ J b hb b.2.1 (Or.inr rfl)
  refine ⟨anchor,?_,?_⟩
  · have h := hx i (ofSites_subset xs w i hi)
    simpa only [blockCell,he] using h
  · have h := hx j (ofSites_subset xs w j hj)
    simpa only [blockCell,hf] using h

theorem output_local {n m rows width : ℕ} (N : ℕ)
    (xs : Fin m → List (Fin n)) (w : Fin m → Fin n → Fin 4) (J : Fin m → ℚ)
    (cell : ℕ → QMAGridCell rows width) (anchor : Fin m → QMAGridCell rows width)
    (hx : ∀ e i, i ∈ xs e → QMAGridCellsNear (cell i.val) (anchor e)) :
    BondLocal (QuantumOrderedRawBlock.output N xs w J).1 (blockCell cell) CommonCell := by
  let env : Environment :=
    (bits (n,N,packed (QuantumOrderedRawBlock.terms xs w) J),
      scale N (packed (QuantumOrderedRawBlock.terms xs w) J))
  change BondLocal (penalty n env.2 ++ termBondsList
    (env,packed (QuantumOrderedRawBlock.terms xs w) J)) (blockCell cell) CommonCell
  intro b hb
  rcases List.mem_append.mp hb with hp | ht
  · exact penalty_local n env.2 cell b hp
  · obtain ⟨bs,hbs,hb⟩ := List.mem_flatten.mp ht
    obtain ⟨raw,hraw,rfl⟩ := List.mem_map.mp hbs
    obtain ⟨e,rfl⟩ := List.mem_ofFn.mp hraw
    exact term_local env.1 env.2 (xs e) (w e) (J e) cell (anchor e) (hx e) b hb

end ContinuumCoulomb.QuantumRawCellLocality

end

end OAI
