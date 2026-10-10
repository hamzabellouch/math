import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumRawCorrectness
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumRawFamilyProgram
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumSampleBudget

namespace OAI

/-! Exact correspondence between the emitted raw family and its certified finite Hamiltonian. -/

noncomputable section
namespace ContinuumCoulomb.QuantumRawExchange
open QuantumAxisSample MediatorListProgram
open scoped BigOperators Classical

theorem penalty_erase (n : ℕ) (r : ℚ) :
    (penaltyBonds n r).map erase = penalty n r := by
  have hrange : (List.range n).map (penaltyBlock r) =
      List.ofFn (fun i : Fin n => penaltyBlock r i.val) := by
    simpa only [List.length_range,List.getElem_range,Fin.val_cast] using
      (List.ofFn_getElem_eq_map (List.range n) (penaltyBlock r)).symm
  rw [penalty,hrange,penaltyBonds,List.map_ofFn,List.ofFn_mul]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext i
  apply congrArg List.ofFn
  funext j
  have he : (⟨i.val*6+j.val,by omega⟩ : Fin (n*6)) = finProdFinEquiv (i,j) := by
    apply Fin.ext
    change i.val*6+j.val = j.val+6*i.val
    omega
  simp only [he,Equiv.symm_apply_apply,Function.comp_apply,erase]
  change ((qmaFourEdgeLeft j).val+4*i.val,(qmaFourEdgeRight j).val+4*i.val,r^2) = _
  simp only [Nat.add_comm]

def packed {n m : ℕ} (t : Fin m → QMAXZTerm n) (J : Fin m → ℚ) : List Raw :=
  List.ofFn (fun e => pack (t e) (J e))

theorem fullBonds_packed {n m : ℕ} (k : ℕ) (r : ℚ) (t : Fin m → QMAXZTerm n) (J : Fin m → ℚ) :
    fullBonds (n,(k,r),packed t J) = (family k r t J).map erase := by
  simp only [fullBonds,family,List.map_append,penalty_erase,termBondsList,packed,
    List.map_flatten,List.map_ofFn,Function.comp_def,bonds_pack]

theorem fullScalar_packed {n m : ℕ} (k : ℕ) (r : ℚ) (t : Fin m → QMAXZTerm n) (J : Fin m → ℚ) :
    fullScalar (n,(k,r),packed t J) = scalarValue k r t J := by
  simp only [fullScalar,termScalarList,packed,List.map_ofFn,List.sum_ofFn,
    Function.comp_apply,scalar_pack,termScalar_sum]

theorem family_distinct {n m : ℕ} (k : ℕ) (r : ℚ) (t : Fin m → QMAXZTerm n) (J : Fin m → ℚ)
    (b : TypedBond (n*4)) (hb : b ∈ family k r t J) : b.1 ≠ b.2.1 := by
  rcases List.mem_append.mp hb with h | h
  · exact penaltyBonds_distinct n r b h
  · obtain ⟨xs,hxs,hb⟩ := List.mem_flatten.mp h
    obtain ⟨e,he⟩ := List.mem_ofFn.mp hxs
    subst xs
    exact termBonds_distinct k r (t e) (J e) b hb

theorem fullBonds_valid {n m : ℕ} (k : ℕ) (r : ℚ) (t : Fin m → QMAXZTerm n) (J : Fin m → ℚ)
    (b : Bond) (hb : b ∈ fullBonds (n,(k,r),packed t J)) :
    b.1 < n*4 ∧ b.2.1 < n*4 ∧ b.1 ≠ b.2.1 := by
  rw [fullBonds_packed] at hb
  obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hb
  refine ⟨a.1.isLt,a.2.1.isLt,?_⟩
  exact fun h => family_distinct k r t J a ha (Fin.ext h)

end ContinuumCoulomb.QuantumRawExchange

end

end OAI
