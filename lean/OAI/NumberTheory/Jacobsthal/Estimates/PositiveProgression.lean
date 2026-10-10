import Mathlib

namespace OAI

namespace Erdos970

section

namespace ErdosInverseHits

def hitLength (Y M b : ℕ) : ℕ := (Y+M-b)/M

theorem lt_hitLength_iff (Y M b j : ℕ) (hM : 0 < M) (hb : b ≤ M) :
    j < hitLength Y M b ↔ b+M*j ≤ Y := by
  unfold hitLength
  rw [Nat.lt_iff_add_one_le,Nat.le_div_iff_mul_le hM,
    Nat.le_sub_iff_add_le (by omega : b ≤ Y+M)]
  constructor <;> intro h <;> nlinarith

theorem exists_positive_coordinate (M b n : ℕ) (_hM : 0 < M)
    (hb1 : 1 ≤ b) (hbM : b ≤ M) (hn : 1 ≤ n) (hres : Nat.ModEq M n b) :
    ∃ j : ℕ,n = b+M*j := by
  have hsub : Nat.ModEq M (n-1) (b-1) := by
    apply Nat.ModEq.add_left_cancel' 1
    simpa only [Nat.add_sub_of_le hn,Nat.add_sub_of_le hb1] using hres
  have hbsmall : b-1 < M := by omega
  have hrem : (n-1)%M = b-1 := by
    change (n-1)%M = (b-1)%M at hsub
    simpa only [Nat.mod_eq_of_lt hbsmall] using hsub
  refine ⟨(n-1)/M,?_⟩
  have heq := Nat.mod_add_div (n-1) M
  rw [hrem] at heq
  omega

noncomputable def positiveHits (Y M b : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc 1 Y).filter (fun n => Nat.ModEq M n b)

theorem positiveHits_eq_image (Y M b : ℕ) (hM : 0 < M) (hb1 : 1 ≤ b) (hbM : b ≤ M) :
    positiveHits Y M b = (Finset.range (hitLength Y M b)).image (fun j => b+M*j) := by
  classical
  ext n
  simp only [positiveHits,Finset.mem_filter,Finset.mem_Icc,Finset.mem_image,Finset.mem_range]
  constructor
  · rintro ⟨⟨hn1,hnY⟩,hres⟩
    obtain ⟨j,rfl⟩ := exists_positive_coordinate M b n hM hb1 hbM hn1 hres
    exact ⟨j,(lt_hitLength_iff Y M b j hM hbM).mpr hnY,rfl⟩
  · rintro ⟨j,hj,rfl⟩
    refine ⟨⟨by omega,(lt_hitLength_iff Y M b j hM hbM).mp hj⟩,?_⟩
    change (b+M*j)%M = b%M
    simp

theorem positiveHits_card (Y M b : ℕ) (hM : 0 < M) (hb1 : 1 ≤ b) (hbM : b ≤ M) :
    (positiveHits Y M b).card = hitLength Y M b := by
  rw [positiveHits_eq_image Y M b hM hb1 hbM,Finset.card_image_of_injective]
  · exact Finset.card_range _
  · intro i j hij
    exact Nat.eq_of_mul_eq_mul_left hM (Nat.add_left_cancel hij)

theorem hitLength_error (Y M b : ℕ) (hM : 0 < M) (hb1 : 1 ≤ b) (hbM : b ≤ M) :
    |(hitLength Y M b : ℝ)-(Y : ℝ)/M| ≤ 1 := by
  have hsub : b ≤ Y+M := by omega
  have hdivision := Nat.mod_add_div (Y+M-b) M
  have hmod := Nat.mod_lt (Y+M-b) hM
  have heq : (((Y+M-b)%M : ℕ) : ℝ)+(M : ℝ)*hitLength Y M b = (Y : ℝ)+M-b := by
    simpa only [hitLength,Nat.cast_add,Nat.cast_mul,Nat.cast_sub hsub] using
      congrArg (fun n : ℕ => (n : ℝ)) hdivision
  have hmR : (0 : ℝ) < M := by exact_mod_cast hM
  have hrR : (((Y+M-b)%M : ℕ) : ℝ) < M := by exact_mod_cast hmod
  have hbR : (b : ℝ) ≤ M := by exact_mod_cast hbM
  have hbR1 : (1 : ℝ) ≤ b := by exact_mod_cast hb1
  have hremR : (0 : ℝ) ≤ ((Y+M-b)%M : ℕ) := Nat.cast_nonneg _
  have hlo : (Y : ℝ)/M ≤ (hitLength Y M b : ℝ)+1 := by
    apply (div_le_iff₀ hmR).mpr
    nlinarith
  have hhi : (hitLength Y M b : ℝ)-1 ≤ (Y : ℝ)/M := by
    apply (le_div_iff₀ hmR).mpr
    nlinarith
  rw [abs_le]
  constructor <;> linarith

end ErdosInverseHits

end

end Erdos970

end OAI
