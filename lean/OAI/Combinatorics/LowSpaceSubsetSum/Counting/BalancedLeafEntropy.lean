import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationLeafDomains

namespace OAI

/-! # Entropy of the actual balanced leaf counts

Both the selected count and its complementary half count are treated with
the same unit rounding error.  This is applied to the four top blocks and
the two local blocks sampled by the representation experiment.
-/

noncomputable section

namespace LowSpaceSubsetSum

def orientedBlockCount (complement : Bool) (l t k : ℕ) (j : Fin l) : ℕ :=
  if complement then t - balancedBlockCounts l k j else balancedBlockCounts l k j

def orientedDensity (complement : Bool) (p : ℝ) : ℝ :=
  if complement then 1 / 2 - p else p

theorem orientedDensity_mem {p : ℝ} (hp : p ∈ Set.Icc (1 / 6) (1 / 4))
    (complement : Bool) : orientedDensity complement p ∈ Set.Icc (1 / 6) (1 / 3) := by
  cases complement <;> simp only [orientedDensity, Bool.false_eq_true, ↓reduceIte]
  · constructor <;> linarith [hp.1, hp.2]
  · constructor <;> linarith [hp.1, hp.2]

theorem orientedBlockCount_error (complement : Bool) (l t k : ℕ)
    (hl : l = 2 ∨ l = 4) (ht : 0 < t) (hk : k ≤ l * t) (j : Fin l) :
    |(orientedBlockCount complement l t k j : ℝ) -
      (2 * t : ℕ) * orientedDensity complement ((k : ℝ) / (l * (2 * t) : ℕ))| ≤ 1 := by
  have hl0 : 0 < l := by rcases hl with rfl | rfl <;> decide
  have hlR : (l : ℝ) ≠ 0 := by positivity
  have htR : (t : ℝ) ≠ 0 := by positivity
  have heq : ((2 * t : ℕ) : ℝ) * ((k : ℝ) / (l * (2 * t) : ℕ)) = (k : ℝ) / l := by
    push_cast
    field_simp [hlR, htR]
  have hcount := balancedBlockCounts_le l t k hl hk j
  have herr := balancedBlockCounts_error l k hl0 j
  cases complement
  · simpa only [orientedBlockCount, orientedDensity, Bool.false_eq_true,
      ↓reduceIte, heq] using herr
  · have hsub : ((t - balancedBlockCounts l k j : ℕ) : ℝ) =
        (t : ℝ) - balancedBlockCounts l k j := Nat.cast_sub hcount
    simp only [orientedBlockCount, orientedDensity, ↓reduceIte, hsub, mul_sub, heq]
    have htwo : ((2 * t : ℕ) : ℝ) * (1 / 2) = t := by push_cast; ring
    rw [htwo]
    rw [show (t : ℝ) - balancedBlockCounts l k j - (t - (k : ℝ) / l) =
      -((balancedBlockCounts l k j : ℝ) - (k : ℝ) / l) by ring, abs_neg]
    exact herr

theorem orientedBlockCount_entropy (complement : Bool) (l t k : ℕ)
    (hl : l = 2 ∨ l = 4) (ht : 24 ≤ 2 * t) (hk : k ≤ l * t)
    (hp : (k : ℝ) / (l * (2 * t) : ℕ) ∈ Set.Icc (1 / 6) (1 / 4)) (j : Fin l) :
    ((2 * t : ℕ) : ℝ) *
        binaryEntropy ((orientedBlockCount complement l t k j : ℝ) / (2 * t : ℕ)) ≤
      ((2 * t : ℕ) : ℝ) *
        binaryEntropy (orientedDensity complement ((k : ℝ) / (l * (2 * t) : ℕ))) + 3 := by
  exact rounded_leaf_component ht (orientedDensity_mem hp complement)
    (orientedBlockCount_error complement l t k hl (by omega) hk j)

namespace RepresentationSetup

variable {n : ℕ} (R : RepresentationSetup n)

theorem guess_density (g : Guesses n) (hm : 0 < mixerSize n) (j : Fin 3) :
    ((g j).val : ℝ) / mixerSize n ∈ Set.Icc (1 / 6) (1 / 4) := by
  have hg := Finset.mem_Icc.mp (g j).property
  have hlo : mixerSize n ≤ 6 * (g j).val := by
    have h := hg.1
    change (mixerSize n + 5) / 6 ≤ (g j).val at h
    omega
  have hhi : 4 * (g j).val ≤ mixerSize n := by
    have h := hg.2
    change (g j).val ≤ mixerSize n / 4 at h
    omega
  have hmR : (0 : ℝ) < mixerSize n := by exact_mod_cast hm
  have hloR : (mixerSize n : ℝ) ≤ 6 * (g j).val := by exact_mod_cast hlo
  have hhiR : (4 : ℝ) * (g j).val ≤ mixerSize n := by exact_mod_cast hhi
  constructor
  · apply (le_div_iff₀ hmR).mpr
    linarith
  · apply (div_le_iff₀ hmR).mpr
    linarith

theorem rawLeaf_top_entropy (z : Layout n) (g : Guesses n) (f : R.Partitions z)
    (B : Fin n → Fin 2 × Fin 4) (hn : 400 ≤ n) (j : Fin 2) (i : Fin 4) :
    ((R.rawLeaf z g f B j i).top.card : ℝ) *
        binaryEntropy ((R.rawLeaf z g f B j i).topCount /
          ((R.rawLeaf z g f B j i).top.card : ℝ)) ≤
      (mixerSize n : ℝ) * binaryEntropy
        (orientedDensity (j != 0) (((g 0).val : ℝ) / mixerSize n)) / 4 + 3 := by
  have ht : 24 ≤ 2 * (3 * n / 100) := by omega
  have hk : (g 0).val ≤ 4 * (3 * n / 100) := by
    have h := (Finset.mem_Icc.mp (g 0).property).2
    change (g 0).val ≤ 8 * (3 * n / 100) / 4 at h
    omega
  have hm : 0 < mixerSize n := by unfold mixerSize; omega
  have hp := guess_density g hm 0
  have heq : 4 * (2 * (3 * n / 100)) = mixerSize n := by unfold mixerSize; omega
  rw [← heq] at hp
  have he := orientedBlockCount_entropy (j != 0) 4 (3 * n / 100) (g 0).val
    (Or.inr rfl) ht hk hp i
  rw [R.rawLeaf_top_card]
  have hcount : (R.rawLeaf z g f B j i).topCount =
      orientedBlockCount (j != 0) 4 (3 * n / 100) (g 0).val i := by
    fin_cases j <;> rfl
  rw [hcount]
  change ((2 * (3 * n / 100) : ℕ) : ℝ) * _ ≤ _
  rw [heq] at he
  have hsize : ((mixerSize n : ℕ) : ℝ) = 4 * ((2 * (3 * n / 100) : ℕ) : ℝ) := by
    rw [← heq]
    push_cast
    ring
  calc
    _ ≤ ((2 * (3 * n / 100) : ℕ) : ℝ) * binaryEntropy
        (orientedDensity (j != 0) (((g 0).val : ℝ) / mixerSize n)) + 3 := he
    _ = _ := by rw [hsize]; ring

theorem rawLeaf_local_entropy (z : Layout n) (g : Guesses n) (f : R.Partitions z)
    (B : Fin n → Fin 2 × Fin 4) (hn : 400 ≤ n) (j : Fin 2) (i : Fin 4) :
    ((R.rawLeaf z g f B j i).mixer.card : ℝ) *
        binaryEntropy ((R.rawLeaf z g f B j i).localCount /
          ((R.rawLeaf z g f B j i).mixer.card : ℝ)) ≤
      (mixerSize n : ℝ) * binaryEntropy
        (orientedDensity (decide (2 ≤ i.val)) (((g j.succ).val : ℝ) / mixerSize n)) / 2 + 3 := by
  have ht : 24 ≤ 2 * (2 * (3 * n / 100)) := by omega
  have hk : (g j.succ).val ≤ 2 * (2 * (3 * n / 100)) := by
    have h := (Finset.mem_Icc.mp (g j.succ).property).2
    change (g j.succ).val ≤ 8 * (3 * n / 100) / 4 at h
    omega
  have hm : 0 < mixerSize n := by unfold mixerSize; omega
  have hp := guess_density g hm j.succ
  have heq : 2 * (2 * (2 * (3 * n / 100))) = mixerSize n := by unfold mixerSize; omega
  rw [← heq] at hp
  have he := orientedBlockCount_entropy (decide (2 ≤ i.val)) 2 (2 * (3 * n / 100))
    (g j.succ).val (Or.inl rfl) ht hk hp ⟨i.val % 2, Nat.mod_lt _ (by decide)⟩
  rw [R.rawLeaf_local_card]
  have hcount : (R.rawLeaf z g f B j i).localCount =
      orientedBlockCount (decide (2 ≤ i.val)) 2 (2 * (3 * n / 100))
        (g j.succ).val ⟨i.val % 2, Nat.mod_lt _ (by decide)⟩ := by
    fin_cases j <;> fin_cases i <;> rfl
  have hhalf : blockHalf n j.succ = 2 * (3 * n / 100) := by fin_cases j <;> rfl
  rw [hcount, hhalf]
  rw [heq] at he
  have hsize : ((mixerSize n : ℕ) : ℝ) = 2 * ((2 * (2 * (3 * n / 100)) : ℕ) : ℝ) := by
    rw [← heq]
    push_cast
    ring
  calc
    _ ≤ ((2 * (2 * (3 * n / 100)) : ℕ) : ℝ) * binaryEntropy
        (orientedDensity (decide (2 ≤ i.val)) (((g j.succ).val : ℝ) / mixerSize n)) + 3 := he
    _ = _ := by rw [hsize]; ring

end RepresentationSetup

end LowSpaceSubsetSum

end

end OAI
