import OAI.Combinatorics.LowSpaceSubsetSum.Counting.BalancedLeafEntropy

namespace OAI

/-! # Feasibility of the executable representation allocation -/

noncomputable section

namespace LowSpaceSubsetSum

open scoped BigOperators
open RepresentationSetup

def representationCount (n : ℕ) (g : Guesses n) (complement : Bool) (j : Fin 3) : ℕ :=
  if complement then mixerSize n / 2 - (g j).val else (g j).val

def representationBits (n : ℕ) (g : Guesses n) (complement : Bool) (j : Fin 3) : ℕ :=
  binomialBits (mixerSize n) (representationCount n g complement j)

def representationBackgroundSize (n : ℕ) : ℕ := n - 3 * mixerSize n

def representationParentSize (n : ℕ) (g : Guesses n) (j : Fin 2) : ℕ :=
  allocateSide (j != 0) (representationBackgroundSize n)
    (representationBits n g false 0) (representationBits n g true 0)

def representationChildSize (n : ℕ) (g : Guesses n) (j : Fin 2) (right : Bool) : ℕ :=
  allocateSide right (representationParentSize n g j)
    (representationBits n g false j.succ) (representationBits n g true j.succ)

def representationLeafCounts (n : ℕ) (g : Guesses n) : Fin 8 → ℕ :=
  computedLeafCounts (representationBackgroundSize n)
    (representationBits n g false 0) (representationBits n g true 0)
    (representationBits n g false 1) (representationBits n g true 1)
    (representationBits n g false 2) (representationBits n g true 2)

def representationEntropy (n : ℕ) (g : Guesses n) (complement : Bool) (j : Fin 3) : ℝ :=
  (mixerSize n : ℝ) * binaryEntropy
    (orientedDensity complement (((g j).val : ℝ) / mixerSize n))

/-- The main-branch input-scale test supplies the small allocation error. -/
theorem representation_log_budget {n : ℕ} {u : ℝ} (hn : 10000 ≤ n)
    (hmu : (mixerSize n : ℝ) + 1 ≤ u) (hlog : Real.logb 2 u ≤ (n : ℝ) / 1000000000) :
    Real.logb 2 ((mixerSize n : ℝ) + 1) + 1 ≤ (n : ℝ) / 1000 := by
  have hmono := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
    (by positivity : (0 : ℝ) < (mixerSize n : ℝ) + 1) hmu
  have hnR : (10000 : ℝ) ≤ n := by exact_mod_cast hn
  linarith

theorem representationCount_le (n : ℕ) (g : Guesses n) (complement : Bool) (j : Fin 3) :
    representationCount n g complement j ≤ mixerSize n := by
  have hg := (Finset.mem_Icc.mp (g j).property).2
  change (g j).val ≤ mixerSize n / 4 at hg
  cases complement <;> simp only [representationCount, Bool.false_eq_true, ↓reduceIte] <;> omega

theorem representationCount_fraction {n : ℕ} (g : Guesses n) (complement : Bool)
    (hm : 0 < mixerSize n) (j : Fin 3) :
    (representationCount n g complement j : ℝ) / mixerSize n =
      orientedDensity complement (((g j).val : ℝ) / mixerSize n) := by
  have hg := (Finset.mem_Icc.mp (g j).property).2
  change (g j).val ≤ mixerSize n / 4 at hg
  have hk : (g j).val ≤ mixerSize n / 2 := by omega
  have he : 2 * (mixerSize n / 2) = mixerSize n := by unfold mixerSize; omega
  have heR : (2 : ℝ) * (mixerSize n / 2 : ℕ) = mixerSize n := by exact_mod_cast he
  have hmR : (mixerSize n : ℝ) ≠ 0 := by positivity
  cases complement
  · rfl
  · simp only [representationCount, orientedDensity, ↓reduceIte, Nat.cast_sub hk]
    rw [sub_div]
    congr 1
    apply (div_eq_iff hmR).mpr
    nlinarith

theorem representationBits_entropy_error {n : ℕ} (g : Guesses n) (complement : Bool)
    (hm : 0 < mixerSize n) (j : Fin 3) :
    |(representationBits n g complement j : ℝ) - representationEntropy n g complement j| <
      Real.logb 2 ((mixerSize n : ℝ) + 1) + 1 := by
  have h := binomialBits_entropy_error (mixerSize n) (representationCount n g complement j)
    (representationCount_le n g complement j)
  rw [representationCount_fraction g complement hm j] at h
  exact h

theorem representationBits_difference {n : ℕ} (g : Guesses n)
    (hm : 0 < mixerSize n) (j : Fin 3) :
    |(representationBits n g true j : ℝ) - representationBits n g false j| <
      (3 / 8 : ℝ) * mixerSize n + 2 * (Real.logb 2 ((mixerSize n : ℝ) + 1) + 1) := by
  apply binomialBits_difference (mixerSize n) (representationCount n g false j)
    (representationCount n g true j)
    (representationCount_le n g false j) (representationCount_le n g true j)
  · rw [representationCount_fraction g false hm]
    exact orientedDensity_mem (guess_density g hm j) false
  · rw [representationCount_fraction g true hm]
    exact orientedDensity_mem (guess_density g hm j) true

theorem allocation_guards_of_error (r a b : ℕ) {d : ℝ}
    (hd : |(b : ℝ) - a| ≤ d) (hdr : d ≤ r) : a ≤ r + b ∧ b ≤ r + a := by
  have h := abs_le.mp hd
  constructor
  · have he : (a : ℝ) ≤ r + b := by linarith
    exact_mod_cast he
  · have he : (b : ℝ) ≤ r + a := by linarith
    exact_mod_cast he

theorem weighted_parent_allocation_bound (side : Bool) (r a b : ℕ)
    (ha : a ≤ r + b) (hb : b ≤ r + a) {A B e : ℝ}
    (hA : |(a : ℝ) - A| ≤ e) (hB : |(b : ℝ) - B| ≤ e) :
    (if side then B else A) + (allocateSide side r a b : ℝ) ≤
      (r : ℝ) / 2 + (A + B) / 2 + e + 1 := by
  have h := (abs_lt.mp (allocateSide_error side r a b ha hb hA hB)).2
  cases side <;> simp only [idealSide, Bool.false_eq_true, ↓reduceIte] at h ⊢ <;> linarith

theorem allocation_three_levels_feasible (r : ℕ) (a b : Fin 3 → ℕ) {d : ℝ}
    (hd0 : 0 ≤ d) (hd : ∀ j, |(b j : ℝ) - a j| ≤ d) (hr : 3 * d + 2 ≤ r) :
    (a 0 ≤ r + b 0 ∧ b 0 ≤ r + a 0) ∧
      ∀ j : Fin 2, a j.succ ≤ allocateSide (j != 0) r (a 0) (b 0) + b j.succ ∧
        b j.succ ≤ allocateSide (j != 0) r (a 0) (b 0) + a j.succ := by
  have hdr : d ≤ r := by linarith
  have hbase := allocation_guards_of_error r (a 0) (b 0) (hd 0) hdr
  have hparents := allocated_sides_lower r (a 0) (b 0) (hd 0) hdr
  refine ⟨hbase, fun j => ?_⟩
  apply allocation_guards_of_error _ _ _ (hd j.succ)
  fin_cases j
  · change d ≤ (allocateLeft r (a 0) (b 0) : ℝ)
    linarith [hparents.1]
  · change d ≤ (allocateRight r (a 0) (b 0) : ℝ)
    linarith [hparents.2]

theorem representationAllocation_feasible {n : ℕ} (g : Guesses n) (hn : 10000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ) + 1) + 1 ≤ (n : ℝ) / 1000) :
    (representationBits n g false 0 ≤ representationBackgroundSize n +
      representationBits n g true 0 ∧
     representationBits n g true 0 ≤ representationBackgroundSize n +
      representationBits n g false 0) ∧
      ∀ j : Fin 2, representationBits n g false j.succ ≤
          representationParentSize n g j + representationBits n g true j.succ ∧
        representationBits n g true j.succ ≤
          representationParentSize n g j + representationBits n g false j.succ := by
  have hm : 0 < mixerSize n := by unfold mixerSize; omega
  have hmbound := (mixerSize_bounds n).2
  have hthreeR : (3 : ℝ) * mixerSize n ≤ n := by linarith
  have hthree : 3 * mixerSize n ≤ n := by exact_mod_cast hthreeR
  have hr : (representationBackgroundSize n : ℝ) = n - 3 * (mixerSize n : ℝ) := by
    simp only [representationBackgroundSize, Nat.cast_sub hthree, Nat.cast_mul, Nat.cast_ofNat]
  let d : ℝ := (3 / 8 : ℝ) * mixerSize n +
    2 * (Real.logb 2 ((mixerSize n : ℝ) + 1) + 1)
  have hd : ∀ j, |(representationBits n g true j : ℝ) - representationBits n g false j| ≤ d :=
    fun j => (representationBits_difference g hm j).le
  have hd0 : 0 ≤ d := (abs_nonneg _).trans (hd 0)
  have hmargin : 3 * d + 2 ≤ (representationBackgroundSize n : ℝ) := by
    have hnR : (10000 : ℝ) ≤ n := by exact_mod_cast hn
    dsimp only [d]
    rw [hr]
    linarith
  exact allocation_three_levels_feasible (representationBackgroundSize n)
    (representationBits n g false) (representationBits n g true) hd0 hd hmargin

theorem representationLeafCounts_sum {n : ℕ} (g : Guesses n) (hn : 10000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ) + 1) + 1 ≤ (n : ℝ) / 1000) :
    ∑ i, representationLeafCounts n g i = representationBackgroundSize n := by
  obtain ⟨h0, hchildren⟩ := representationAllocation_feasible g hn hlog
  exact computedLeafCounts_sum _ _ _ _ _ _ _ h0.1 h0.2
    (hchildren 0).1 (hchildren 0).2 (hchildren 1).1 (hchildren 1).2

end LowSpaceSubsetSum

end

end OAI
