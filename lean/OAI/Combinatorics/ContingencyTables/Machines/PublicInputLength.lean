import OAI.Combinatorics.ContingencyTables.AlgorithmStatements
import Mathlib.Data.Nat.Size

namespace OAI

/-! # Binary input lengths for the sampling machine -/

namespace ContingencyTables.Algorithms
open MatchingFPRAS
open scoped BigOperators

lemma encodeNat_length (n : ℕ) : (encodeNat n).length=n.size+1 := by
  simp only [encodeNat,List.length_append,List.length_map,List.length_singleton,Nat.size_eq_bits_len]

lemma encodeNat_length_le (n N : ℕ) (hn : n ≤ N) :
    (encodeNat n).length ≤ Nat.clog 2 (N+1)+1 := by
  rw [encodeNat_length]
  have hs : n.size ≤ Nat.clog 2 (N+1) := Nat.size_le.mpr
    ((Nat.lt_succ_of_le hn).trans_le (Nat.le_pow_clog (by decide) (N+1)))
  omega

private lemma natWords_length (ns : List ℕ) (N : ℕ) (h : ∀ n∈ns,n ≤ N) :
    (ns.flatMap encodeNat).length ≤ ns.length*(Nat.clog 2 (N+1)+1) := by
  induction ns with
  | nil => simp
  | cons n ns ih =>
    have hn := encodeNat_length_le n N (h n (by simp))
    have ht := ih (fun a ha => h a (by simp [ha]))
    simp only [List.flatMap_cons,List.length_append,List.length_cons,Nat.add_mul,Nat.one_mul]
    omega

lemma encodeMargins_length {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
    (htotal : (∑ i,r i)=∑ j,c j) :
    (encodeMargins r c).length ≤ m+n+2+(m+n)*(Nat.clog 2 ((∑ i,r i)+1)+1) := by
  have hm : (encodeNat m).length ≤ m+1 := by
    rw [encodeNat_length]
    exact Nat.add_le_add_right (Nat.size_le.mpr (Nat.lt_two_pow_self)) 1
  have hn : (encodeNat n).length ≤ n+1 := by
    rw [encodeNat_length]
    exact Nat.add_le_add_right (Nat.size_le.mpr (Nat.lt_two_pow_self)) 1
  have hr := natWords_length (List.ofFn r) (∑ i,r i) (by
    intro a ha
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp ha
    exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i))
  have hc := natWords_length (List.ofFn c) (∑ i,r i) (by
    intro a ha
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp ha
    rw [htotal]
    exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j))
  simp only [List.length_ofFn] at hr hc
  simp only [List.flatMap_def,←List.ofFn_comp'] at hr hc
  unfold encodeMargins
  simp only [List.length_append]
  nlinarith

/-- The bit input length is polynomial in the parameters used by the
paper's public sampling statement. -/
theorem encodeSamplingInput_length {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
    (htotal : (∑ i,r i)=∑ j,c j) (k : ℕ) :
    (encodeSamplingInput r c k).length ≤ 5*(samplingSize n r k)^2 := by
  have hM := encodeMargins_length r c htotal
  have hk : (encodeNat k).length ≤ k+1 := by
    rw [encodeNat_length]
    exact Nat.add_le_add_right (Nat.size_le.mpr (Nat.lt_two_pow_self)) 1
  rw [encodeSamplingInput,List.length_append]
  let S := samplingSize n r k
  have hS : 1 ≤ S := by dsimp [S,samplingSize]; omega
  have hmn : m+n ≤ S := by dsimp [S,samplingSize]; omega
  have hl : Nat.clog 2 ((∑ i,r i)+1)+1 ≤ S := by dsimp [S,samplingSize]; omega
  have hkS : k+1 ≤ S := by dsimp [S,samplingSize]; omega
  have hp := Nat.mul_le_mul hmn hl
  change _ ≤ 5*S^2
  nlinarith

end ContingencyTables.Algorithms

end OAI
