import OAI.NumberTheory.JointDickman.Counting.ShortLagSet

namespace OAI

/-! # Exact counting of translated pairs inside integer blocks -/

namespace JointDickman
open Finset

def blockOverlap (M : ℕ) (j : ℤ) : Finset ℤ :=
  (Icc 1 (M : ℤ)).filter (fun i => i+j ∈ Icc 1 (M : ℤ))

theorem card_blockOverlap (M : ℕ) (j : ℤ) (hj : j.natAbs ≤ M) :
    (blockOverlap M j).card = M-j.natAbs := by
  have hab : |j| ≤ (M : ℤ) := by rw [← Int.natCast_natAbs]; exact_mod_cast hj
  by_cases hsign : 0 ≤ j
  · have he : blockOverlap M j = Icc 1 ((M : ℤ)-j) := by
      ext i
      simp only [blockOverlap, mem_filter, mem_Icc]
      omega
    rw [he, Int.card_Icc]
    have ha : (j.natAbs : ℤ) = j := by rw [Int.natCast_natAbs,abs_of_nonneg hsign]
    omega
  · have he : blockOverlap M j = Icc (1-j) (M : ℤ) := by
      ext i
      simp only [blockOverlap, mem_filter, mem_Icc]
      omega
    rw [he, Int.card_Icc]
    have ha : (j.natAbs : ℤ) = -j := by
      rw [Int.natCast_natAbs,abs_of_neg (lt_of_not_ge hsign)]
    omega

def blockOrigins (M V : ℕ) : Finset ℤ := Icc (1-(M : ℤ)) V

theorem sum_block_origins (M V : ℕ) (i : ℤ) (hi : i ∈ Icc 1 (M : ℤ))
    (f : ℤ → ℝ) :
    (∑ s ∈ blockOrigins M V, if s+i ∈ Icc 1 (V : ℤ) then f (s+i) else 0) =
      ∑ n ∈ Icc 1 (V : ℤ), f n := by
  classical
  have he : (blockOrigins M V).filter (fun s => s+i ∈ Icc 1 (V : ℤ)) =
      (Icc 1 (V : ℤ)).image (fun n => n-i) := by
    ext s
    simp only [mem_filter, blockOrigins, mem_Icc, mem_image]
    constructor
    · rintro ⟨hs,hn⟩
      exact ⟨s+i,hn,by omega⟩
    · rintro ⟨n,hn,he⟩
      have h := mem_Icc.mp hi
      constructor <;> omega
  rw [← sum_filter, he, sum_image]
  · simp
  · intro a _ b _ hab
    dsimp at hab
    omega

theorem sum_block_overlap (M V : ℕ) (j : ℤ) (hj : j.natAbs ≤ M)
    (f : ℤ → ℝ) :
    (∑ s ∈ blockOrigins M V, ∑ i ∈ blockOverlap M j,
      if s+i ∈ Icc 1 (V : ℤ) then f (s+i) else 0) =
        ((M-j.natAbs : ℕ) : ℝ)*(∑ n ∈ Icc 1 (V : ℤ), f n) := by
  rw [sum_comm]
  have he (i : ℤ) (hi : i ∈ blockOverlap M j) :=
    sum_block_origins M V i (mem_filter.mp hi).1 f
  simp_rw [sum_congr rfl he]
  simp only [sum_const, nsmul_eq_mul, card_blockOverlap M j hj]

end JointDickman

end OAI
