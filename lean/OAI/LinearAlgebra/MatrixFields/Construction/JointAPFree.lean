import Mathlib

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

noncomputable section

namespace MatrixMultiplication.JointAPFree

def natSet (N : ℕ) : Finset ℕ := (rothNumberNat_spec N).choose

theorem natSet_subset (N : ℕ) : natSet N ⊆ Finset.range N :=
  (rothNumberNat_spec N).choose_spec.1

theorem natSet_card (N : ℕ) : (natSet N).card = rothNumberNat N :=
  (rothNumberNat_spec N).choose_spec.2.1

theorem natSet_threeAPFree (N : ℕ) : ThreeAPFree (natSet N : Set ℕ) :=
  (rothNumberNat_spec N).choose_spec.2.2

theorem mem_natSet_lt {N a : ℕ} (ha : a ∈ natSet N) : a < N :=
  Finset.mem_range.mp (natSet_subset N ha)

theorem natCast_injective_below {M a b : ℕ} (ha : a < M) (hb : b < M)
    (hab : (a : ZMod M) = (b : ZMod M)) : a = b := by
  have h := congrArg ZMod.val hab
  simpa only [ZMod.val_natCast_of_lt ha, ZMod.val_natCast_of_lt hb] using h

theorem add_lt_modulus {M a b : ℕ} (ha : a < M / 2) (hb : b < M / 2) :
    a + b < M := by
  have h := Nat.div_mul_le_self M 2
  omega

def modularSet (M : ℕ) : Finset (ZMod M) :=
  (natSet (M / 2)).image (fun a : ℕ => (a : ZMod M))

theorem modularSet_card (M : ℕ) :
    (modularSet M).card = rothNumberNat (M / 2) := by
  rw [modularSet, Finset.card_image_iff.mpr, natSet_card]
  intro a ha b hb hab
  exact natCast_injective_below
    ((mem_natSet_lt ha).trans_le (Nat.div_le_self M 2))
    ((mem_natSet_lt hb).trans_le (Nat.div_le_self M 2)) hab

theorem modularSet_threeAPFree (M : ℕ) :
    ThreeAPFree (modularSet M : Set (ZMod M)) := by
  intro a ha b hb c hc habc
  change a ∈ (natSet (M / 2)).image (fun n : ℕ => (n : ZMod M)) at ha
  change b ∈ (natSet (M / 2)).image (fun n : ℕ => (n : ZMod M)) at hb
  change c ∈ (natSet (M / 2)).image (fun n : ℕ => (n : ZMod M)) at hc
  obtain ⟨a', ha', rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨b', hb', rfl⟩ := Finset.mem_image.mp hb
  obtain ⟨c', hc', rfl⟩ := Finset.mem_image.mp hc
  have hac := add_lt_modulus (mem_natSet_lt ha') (mem_natSet_lt hc')
  have hbb := add_lt_modulus (mem_natSet_lt hb') (mem_natSet_lt hb')
  have hnat : a' + c' = b' + b' := natCast_injective_below hac hbb (by
    simpa only [Nat.cast_add] using habc)
  exact congrArg (fun n : ℕ => (n : ZMod M)) (natSet_threeAPFree (M / 2) ha' hb' hc' hnat)

theorem modularSet_hashAP (M : ℕ) :
    ∀ x ∈ modularSet M, ∀ y ∈ modularSet M, ∀ z ∈ modularSet M,
      x + y = 2 * z → x = z ∧ y = z := by
  intro x hx y hy z hz h
  have h' : x + y = z + z := by simpa only [two_mul] using h
  exact ⟨modularSet_threeAPFree M hx hz hy h',
    ((modularSet_threeAPFree M).eq_right hx hz hy h').symm⟩

theorem modularSet_card_lower (M : ℕ) :
    ((M / 2 : ℕ) : ℝ) * Real.exp (-4 * Real.sqrt (Real.log ((M / 2 : ℕ) : ℝ))) ≤
      ((modularSet M).card : ℝ) := by
  rw [modularSet_card]
  exact Behrend.roth_lower_bound

theorem modularSet_card_le_half (M : ℕ) : (modularSet M).card ≤ M / 2 := by
  rw [modularSet_card]
  exact rothNumberNat_le _

theorem modularSet_card_pos {M : ℕ} (hM : 2 ≤ M) : 0 < (modularSet M).card := by
  have hhalf : 0 < M / 2 := Nat.div_pos hM (by decide)
  have hpos : (0 : ℝ) < ((M / 2 : ℕ) : ℝ) *
      Real.exp (-4 * Real.sqrt (Real.log ((M / 2 : ℕ) : ℝ))) := by
    exact mul_pos (by exact_mod_cast hhalf) (Real.exp_pos _)
  exact_mod_cast hpos.trans_le (modularSet_card_lower M)

theorem modularSet_nonempty {M : ℕ} (hM : 2 ≤ M) : (modularSet M).Nonempty :=
  Finset.card_pos.mp (modularSet_card_pos hM)

theorem modularSet_log_card_lower {M : ℕ} (hM : 2 ≤ M) :
    Real.log ((M / 2 : ℕ) : ℝ) - 4 * Real.sqrt (Real.log ((M / 2 : ℕ) : ℝ)) ≤
      Real.log ((modularSet M).card : ℝ) := by
  have hhalf : (0 : ℝ) < ((M / 2 : ℕ) : ℝ) := by
    exact_mod_cast (Nat.div_pos hM (by decide) : 0 < M / 2)
  have h := Real.log_le_log (mul_pos hhalf (Real.exp_pos _)) (modularSet_card_lower M)
  rw [Real.log_mul hhalf.ne' (Real.exp_pos _).ne', Real.log_exp] at h
  linarith

theorem modularSet_log_card_le_half {M : ℕ} (hM : 2 ≤ M) :
    Real.log ((modularSet M).card : ℝ) ≤ Real.log ((M / 2 : ℕ) : ℝ) := by
  apply Real.log_le_log
  · exact_mod_cast modularSet_card_pos hM
  · exact_mod_cast modularSet_card_le_half M

theorem modularSet_log_card_lower_modulus {M : ℕ} (hM : 2 ≤ M) :
    Real.log (M : ℝ) - Real.log 3 - 4 * Real.sqrt (Real.log (M : ℝ)) ≤
      Real.log ((modularSet M).card : ℝ) := by
  have hMr : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
  have hhalf : (0 : ℝ) < ((M / 2 : ℕ) : ℝ) := by
    exact_mod_cast (Nat.div_pos hM (by decide) : 0 < M / 2)
  have hround : (M : ℝ) / 3 ≤ ((M / 2 : ℕ) : ℝ) := by
    have hn : M ≤ 3 * (M / 2) := by omega
    have hr : (M : ℝ) ≤ 3 * ((M / 2 : ℕ) : ℝ) := by exact_mod_cast hn
    linarith
  have hlog := Real.log_le_log (div_pos hMr (by norm_num)) hround
  rw [Real.log_div hMr.ne' (by norm_num)] at hlog
  have hlogUpper : Real.log ((M / 2 : ℕ) : ℝ) ≤ Real.log (M : ℝ) := by
    apply Real.log_le_log hhalf
    exact_mod_cast Nat.div_le_self M 2
  have hsqrt := Real.sqrt_le_sqrt hlogUpper
  have hcard := modularSet_log_card_lower hM
  linarith

theorem modularSet_log_card_le_modulus {M : ℕ} (hM : 2 ≤ M) :
    Real.log ((modularSet M).card : ℝ) ≤ Real.log (M : ℝ) := by
  apply Real.log_le_log
  · exact_mod_cast modularSet_card_pos hM
  · exact_mod_cast (modularSet_card_le_half M).trans (Nat.div_le_self M 2)

end MatrixMultiplication.JointAPFree

end

end MatrixAllFields

end OAI
