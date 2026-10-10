import OAI.NumberTheory.Jacobsthal.Partitions.IntervalCuts

namespace OAI

namespace Erdos970

section

namespace ErdosHyperbolaFourier

def progressionPoint (a : ℤ) (T : ℕ) (j : ℤ) : ℤ := a + (T : ℤ)*j

noncomputable def lowerIndex (x : ℝ) (T : ℕ) (a : ℤ) (closed : Bool) : ℤ :=
  lowerCut ((x-a)/T) closed

noncomputable def upperIndex (y : ℝ) (T : ℕ) (a : ℤ) (closed : Bool) : ℤ :=
  upperCut ((y-a)/T) closed

noncomputable def progressionPoints (x y : ℝ) (lc rc : Bool) (T : ℕ) (a : ℤ) : Finset ℤ :=
  (Finset.Ico (lowerIndex x T a lc) (upperIndex y T a rc)).image (progressionPoint a T)

theorem progressionPoint_injective (a : ℤ) (T : ℕ) (hT : 0 < T) :
    Function.Injective (progressionPoint a T) := by
  intro i j hij
  have hT0 : (T : ℤ) ≠ 0 := by exact_mod_cast hT.ne'
  exact mul_left_cancel₀ hT0 (add_left_cancel hij)

theorem progressionPoint_modEq (a : ℤ) (T : ℕ) (j : ℤ) :
    Int.ModEq (T : ℤ) (progressionPoint a T j) a := by
  apply Int.modEq_iff_dvd.mpr
  exact ⟨-j, by dsimp [progressionPoint]; ring⟩

theorem index_mem_iff (x y : ℝ) (lc rc : Bool) (T : ℕ) (a : ℤ) (hT : 0 < T) (j : ℤ) :
    j ∈ Finset.Ico (lowerIndex x T a lc) (upperIndex y T a rc) ↔
      (if lc then x ≤ (progressionPoint a T j : ℝ) else x < (progressionPoint a T j : ℝ)) ∧
      (if rc then (progressionPoint a T j : ℝ) ≤ y else (progressionPoint a T j : ℝ) < y) := by
  have hTR : (0 : ℝ) < T := by exact_mod_cast hT
  simp only [Finset.mem_Ico, lowerIndex, upperIndex, lowerCut_le_iff, lt_upperCut_iff]
  cases lc <;> cases rc <;>
    simp only [Bool.false_eq_true, ite_false, ite_true, div_le_iff₀ hTR, div_lt_iff₀ hTR,
      le_div_iff₀ hTR, lt_div_iff₀ hTR, progressionPoint, Int.cast_add, Int.cast_mul,
      Int.cast_natCast] <;>
    constructor <;> rintro ⟨hlo, hhi⟩ <;> constructor <;> nlinarith

theorem mem_progressionPoints_iff (x y : ℝ) (lc rc : Bool) (T : ℕ) (a z : ℤ) (hT : 0 < T) :
    z ∈ progressionPoints x y lc rc T a ↔
      (if lc then x ≤ (z : ℝ) else x < (z : ℝ)) ∧
      (if rc then (z : ℝ) ≤ y else (z : ℝ) < y) ∧ Int.ModEq (T : ℤ) z a := by
  constructor
  · intro hz
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨hlo, hhi⟩ := (index_mem_iff x y lc rc T a hT j).mp hj
    exact ⟨hlo, hhi, progressionPoint_modEq a T j⟩
  · rintro ⟨hlo, hhi, hmod⟩
    obtain ⟨j, hj⟩ := Int.modEq_iff_dvd.mp hmod.symm
    have he : progressionPoint a T j = z := by dsimp [progressionPoint]; linarith
    apply Finset.mem_image.mpr
    refine ⟨j, ?_, he⟩
    apply (index_mem_iff x y lc rc T a hT j).mpr
    rw [he]
    exact ⟨hlo, hhi⟩

theorem progressionPoints_card (x y : ℝ) (lc rc : Bool) (T : ℕ) (a : ℤ) (hT : 0 < T) :
    (progressionPoints x y lc rc T a).card =
      (upperIndex y T a rc-lowerIndex x T a lc).toNat := by
  unfold progressionPoints
  rw [Finset.card_image_of_injective _ (progressionPoint_injective a T hT), Int.card_Ico]

theorem progressionPoints_count_error (x y : ℝ) (hxy : x ≤ y) (lc rc : Bool)
    (T : ℕ) (a : ℤ) (hT : 0 < T) :
    |((progressionPoints x y lc rc T a).card : ℝ) - (y-x)/(T : ℝ)| ≤ 1 := by
  have hTR : (0 : ℝ) < T := by exact_mod_cast hT
  have hlohi : (x-a)/(T : ℝ) ≤ (y-a)/(T : ℝ) :=
    div_le_div_of_nonneg_right (sub_le_sub_right hxy _) hTR.le
  have h := cut_count_error ((x-a)/(T : ℝ)) ((y-a)/(T : ℝ)) hlohi lc rc
  rw [show (y-a)/(T : ℝ)-(x-a)/(T : ℝ) = (y-x)/(T : ℝ) by ring] at h
  rw [progressionPoints_card x y lc rc T a hT]
  exact h

end ErdosHyperbolaFourier

end

end Erdos970

end OAI
