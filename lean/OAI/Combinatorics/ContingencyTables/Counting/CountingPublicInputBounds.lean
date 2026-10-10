import OAI.Combinatorics.ContingencyTables.Counting.CountingTerminalBounds
import OAI.Combinatorics.ContingencyTables.Counting.ComputedCountingParameters
import OAI.Combinatorics.ContingencyTables.AlgorithmStatements

namespace OAI

/-! # Bounding counting parameters by the public binary input -/

namespace ContingencyTables.CountingPublicInputBounds
open MatchingFPRAS Algorithms
open scoped BigOperators
noncomputable section

def size {m n : ℕ} (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (epsilon delta : ℚ) : ℕ :=
  (encodeCountingInput r c b epsilon delta).length+⌈epsilon⁻¹⌉₊+Nat.clog 2 ⌈delta⁻¹⌉₊+1

lemma nat_length (x : ℕ) : (encodeNat x).length=x.size+1 := by
  simp only [encodeNat,List.length_append,List.length_map,List.length_singleton,Nat.size_eq_bits_len]

lemma successor_size (x : ℕ) : (x+1).size ≤ x.size+1 := by
  apply Nat.size_le.mpr
  have h := Nat.lt_size_self x
  have hp : 0 < 2^x.size := by positivity
  rw [pow_succ]
  omega

lemma matrix_length {m n : ℕ} (b : Fin m→Fin n→ℕ) :
    (encodeMatrix b).length=∑ a : Fin m×Fin n,((b a.1 a.2).size+1) := by
  simp [encodeMatrix,List.length_flatten,List.map_ofFn,List.sum_ofFn,nat_length,
    Fintype.sum_prod_type,Function.comp_def]

lemma cells_le_matrix_length {m n : ℕ} (b : Fin m→Fin n→ℕ) :
    m*n ≤ (encodeMatrix b).length := by
  rw [matrix_length]
  calc
    m*n = ∑ _a : Fin m×Fin n,1 := by simp
    _ ≤ _ := Finset.sum_le_sum (fun _ _ => by omega)

lemma matrix_le_input {m n : ℕ} (r : Fin m→ℕ) (c : Fin n→ℕ)
    (b : Fin m→Fin n→ℕ) (epsilon delta : ℚ) :
    (encodeMatrix b).length ≤ (encodeCountingInput r c b epsilon delta).length := by
  simp only [encodeCountingInput,List.length_append]
  omega

lemma dimension_le {m n : ℕ} (r : Fin m→ℕ) (c : Fin n→ℕ)
    (b : Fin m→Fin n→ℕ) (epsilon delta : ℚ) :
    ComputedCountingParameters.dimensionAllowance (m:=m) (n:=n) ≤ size r c b epsilon delta := by
  have hc := (cells_le_matrix_length b).trans (matrix_le_input r c b epsilon delta)
  unfold ComputedCountingParameters.dimensionAllowance size
  omega

lemma capacityBits_le {m n : ℕ} (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (hne : ∃ X,TableTightening.Feasible r c b X) (epsilon delta : ℚ) :
    ComputedCountingParameters.capacityBits r c b ≤ size r c b epsilon delta := by
  have hb : ComputedCountingParameters.capacityBits r c b ≤ (encodeMatrix b).length := by
    rw [ComputedCountingParameters.capacityBits,matrix_length]
    apply Finset.sum_le_sum
    intro a _
    have hu := ComputedTableTightening.upper_le_bound hEK r c b hne a.1 a.2
    have hn : ComputedTableTightening.newBounds r c b a.1 a.2 ≤ b a.1 a.2 := by
      exact (Nat.sub_le _ _).trans hu
    exact (Nat.size_le_size (Nat.add_le_add_right hn 1)).trans (successor_size _)
  have hi := hb.trans (matrix_le_input r c b epsilon delta)
  unfold size
  omega

lemma inverse_le {m n : ℕ} (r : Fin m→ℕ) (c : Fin n→ℕ)
    (b : Fin m→Fin n→ℕ) (epsilon delta : ℚ) :
    1/epsilon ≤ (size r c b epsilon delta:ℚ) := by
  have hc := Nat.le_ceil (epsilon⁻¹)
  have hn : ⌈epsilon⁻¹⌉₊ ≤ size r c b epsilon delta := by unfold size; omega
  have hc' : 1/epsilon ≤ (⌈epsilon⁻¹⌉₊:ℚ) := by simpa only [one_div] using hc
  exact hc'.trans (by exact_mod_cast hn)

lemma repeats_le {m n : ℕ} (r : Fin m→ℕ) (c : Fin n→ℕ)
    (b : Fin m→Fin n→ℕ) (epsilon delta : ℚ) :
    64*(delta.den.bits.length+1) ≤ 64*size r c b epsilon delta := by
  have hd : delta.den.bits.length+1 ≤ (encodeCountingInput r c b epsilon delta).length := by
    simp only [encodeCountingInput,encodeRat,List.length_append,nat_length,Nat.size_eq_bits_len]
    omega
  exact Nat.mul_le_mul_left 64 (hd.trans (by unfold size; omega))

end
end ContingencyTables.CountingPublicInputBounds

end OAI
