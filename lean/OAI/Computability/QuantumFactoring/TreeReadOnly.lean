import Mathlib
import OAI.Computability.QuantumFactoring.TreeQuarterPhysical
import OAI.Computability.QuantumFactoring.OracleReadOnly

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open BooleanNetwork Exactness

/-- Parallel fresh work does not alter the prefix protected by the left program. -/
lemma parallelProgram_prefix_target {p q n : ℕ} (P : List (Instruction p))
    (Q : List (Instruction q)) (hn : n≤p) (hP : ∀ o∈P,n≤o.target.val) :
    ∀ o∈parallelProgram P Q,n≤o.target.val := by
  intro o ho
  rcases List.mem_append.mp ho with ho|ho
  · obtain ⟨a,ha,rfl⟩:=List.mem_map.mp ho
    have ha':=hP a ha
    simpa only [Instruction.target_place,leftRegister,Function.Embedding.coeFn_mk,
      Fin.val_castAdd] using ha'
  · obtain ⟨a,_ha,rfl⟩:=List.mem_map.mp ho
    change n≤p+a.target.val
    omega

/-- The branch register preceding an otherwise read-only prefix introduces
only targets before that prefix, never in it. -/
lemma parallelProgram_interval_target {p q n : ℕ} (P : List (Instruction p))
    (Q : List (Instruction q)) (hQ : ∀ o∈Q,n≤o.target.val) :
    ∀ o∈parallelProgram P Q,o.target.val<p ∨ p+n≤o.target.val := by
  intro o ho
  rcases List.mem_append.mp ho with ho|ho
  · obtain ⟨a,_ha,rfl⟩:=List.mem_map.mp ho
    exact Or.inl a.target.isLt
  · obtain ⟨a,ha,rfl⟩:=List.mem_map.mp ho
    exact Or.inr (Nat.add_le_add_left (hQ a ha) p)

namespace PhysicalTree
lemma paddedProgram_prefix_target (n : ℕ) : ∀ o∈paddedProgram n,n≤o.target.val := by
  apply parallelProgram_prefix_target
  · dsimp only [launchWidth]
    omega
  · exact preparedOracle_target _ _ _

lemma quarterProgram_interval_target (n : ℕ) :
    ∀ o∈quarterProgram n,o.target.val<1 ∨ 1+n≤o.target.val := by
  apply parallelProgram_interval_target
  apply parallelProgram_prefix_target
  · dsimp only [paddedWidth,launchWidth]
    omega
  · exact paddedProgram_prefix_target n

/-- The original input is the n-wire interval immediately following the
fresh branch coin. This definition is independent of N. -/
def inputWires (n : ℕ) : Finset (Fin (quarterWidth n)) :=
  Finset.univ.filter (fun i => 1 ≤ i.val ∧ i.val < 1+n)

lemma quarterProgram_readOnly (n : ℕ) : ReadOnly (inputWires n) (quarterProgram n) := by
  intro o ho hi
  have ht:=quarterProgram_interval_target n o ho
  have hi':=(Finset.mem_filter.mp hi).2
  omega

/-- This is global input invariance, not merely a clean-input statement. -/
lemma quarterProgram_respects_input (n N : ℕ) :
    RespectsSector (inputSector (inputWires n) (quarterZero n N)) (programMatrix (quarterProgram n)) :=
  program_respects_input _ _ (quarterProgram_readOnly n) _

end PhysicalTree
end ExactQuantumFactoring


end

end OAI
