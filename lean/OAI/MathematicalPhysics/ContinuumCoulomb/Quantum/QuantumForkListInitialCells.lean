import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumForkListCellLocality

namespace OAI

/-! The initial subdivision assigns its two new spins to the original
endpoints. Its singlet bonds therefore have exactly the original cell locality. -/

noncomputable section
namespace ContinuumCoulomb.QuantumForkList
open MediatorListProgram
open scoped Classical

def initialCell {β : Type*} (n : ℕ) (bs : List Bond) (cell : ℕ → β) (v : ℕ) : β :=
  if v<n then cell v else cell (initialEndpoint bs (v-n))

theorem initialCell_old {β : Type*} (n : ℕ) (bs : List Bond) (cell : ℕ → β)
    (v : ℕ) (hv : v<n) : initialCell n bs cell v=cell v := by
  simp only [initialCell,hv,ite_true]

theorem initialCell_new {β : Type*} (n : ℕ) (bs : List Bond) (cell : ℕ → β) (j : ℕ) :
    initialCell n bs cell (n+j)=cell (initialEndpoint bs j) := by
  have hn : ¬n+j<n := by omega
  simp only [initialCell,hn,ite_false,Nat.add_sub_cancel_left]

theorem initial_cellAligned {β : Type*} (n : ℕ) (bs : List Bond) (c N : ℚ)
    (cell : ℕ → β) : CellAligned (initial n bs c N) (initialCell n bs cell) := by
  intro i j
  have hj₀ := j.isLt
  generalize hkj : j.val=k at hj₀ ⊢
  clear hkj j
  have hi : i.val<n := by simpa only [initial,List.length_map,List.length_range] using i.isLt
  have hg : groupAt (initial n bs c N).2.2.2 i.val=
      initialGroup n bs (initialScale N bs c) i.val := initial_groupAt _ _ _ _ hi
  have hj : k<(initialIndices bs i.val).length := by
    have hh := hj₀
    rw [hg] at hh
    simpa only [initialGroup,List.length_map] using hh
  rw [hg,initialGroup_portAt _ _ _ _ _ hj,initialCell_new,initialCell_old _ _ _ _ hi]
  have he := (initialIndices_mem bs i.val _ (List.getElem_mem hj)).2
  rw [he]

theorem initial_cellLocal {β : Type*} (n : ℕ) (bs : List Bond) (c N : ℚ)
    (cell : ℕ → β) (R : β → β → Prop) (hl : BondLocal bs cell R) :
    BondLocal (initial n bs c N).2.1 (initialCell n bs cell) R := by
  intro b hb
  obtain ⟨e,he,rfl⟩ := List.mem_map.mp hb
  have he' : e<bs.length := List.mem_range.mp he
  have hh := hl (bs[e]) (List.getElem_mem he')
  have hleft := initialEndpoint_even bs ⟨e,he'⟩
  have hright := initialEndpoint_odd bs ⟨e,he'⟩
  change R (initialCell n bs cell (n+2*e)) (initialCell n bs cell (n+2*e+1))
  rw [initialCell_new,show n+2*e+1=n+(2*e+1) by omega,initialCell_new,hleft,hright]
  exact hh

end ContinuumCoulomb.QuantumForkList

end

end OAI
