import OAI.Probability.ThorpShuffle.EnergyDecay

namespace OAI

universe uα

noncomputable section

open scoped BigOperators
open Filter

namespace Thorp

namespace Conditional

theorem freeCount_eq_sum {α : Type uα} [Fintype α] (B : α → Bool) :
    freeCount B = ∑ x, (B x).toNat := by
  classical
  calc
    freeCount B = ∑ x, if B x = true then (1 : ℕ) else 0 := (Finset.sum_boole _ _).symm
    _ = _ := Finset.sum_congr rfl (fun x _ => by cases B x <;> rfl)

theorem pairFreeCount_physical (d : ℕ) (B : Position (d + 1) → Bool) :
    pairFreeCount (B ∘ (splitPosition d).symm) = freeCount B := by
  rw [freeCount_eq_sum]
  have he := Equiv.sum_comp (splitPosition d).symm (fun x => (B x).toNat)
  rw [← he, Fintype.sum_prod_type, Fintype.sum_bool]
  simp only [pairFreeCount, Function.comp_apply, Finset.sum_add_distrib]
  exact Nat.add_comm _ _

theorem halfCount_after_step (d : ℕ) (v : RawState (d + 1))
    (c : Coins (d + 1)) (h : Bool) :
    freeCount (halfRaw d (Fin.last d) h (rawNext d v c)).free =
      pairHalfCount (v.free ∘ (splitPosition d).symm) c h := by
  rw [freeCount_eq_sum]
  unfold halfRaw rawNext pairHalfCount
  simp only [insertBit_last]
  apply Finset.sum_congr rfl
  intro x _
  erw [physicalFree_snoc]
  rfl

theorem halfDensity_after_step (d : ℕ) (v : RawState (d + 1))
    (c : Coins (d + 1)) (h : Bool)
    (hm : Fintype.card (Position (d + 1)) ≤ 8 * freeCount v.free)
    (hc : freeCount v.free ≤ 4 * pairHalfCount (v.free ∘ (splitPosition d).symm) c h) :
    (1 / 16 : ℝ) ≤ startHalfDensity d (rawNext d v c) h := by
  unfold startHalfDensity
  rw [halfCount_after_step]
  have hn : Fintype.card (Position (d + 1)) = 2 * Fintype.card (Position d) := by
    simp [Fintype.card_pi, Fintype.card_bool, Fintype.card_fin, pow_succ, Nat.mul_comm]
  rw [hn] at hm
  have hm' : (2 : ℝ) * Fintype.card (Position d) ≤ 8 * (freeCount v.free : ℝ) := by
    exact_mod_cast hm
  have hc' : (freeCount v.free : ℝ) ≤
      4 * (pairHalfCount (v.free ∘ (splitPosition d).symm) c h : ℝ) := by exact_mod_cast hc
  apply (le_div_iff₀ (by exact_mod_cast Fintype.card_pos (α := Position d))).mpr
  nlinarith

theorem partnerEnergy_nonneg (d : ℕ) (v : RawState (d + 1)) (h : Bool) :
    0 ≤ partnerEnergy d v h := by
  unfold partnerEnergy
  exact Finset.sum_nonneg (fun _ _ => mul_nonneg (sq_nonneg _) (by split_ifs <;> norm_num))

theorem oneFreeEnergy_le (d : ℕ) (v : RawState (d + 1)) :
    oneFreeEnergy d v.free v.weight ≤ rawEnergy v := by
  have hid := oneFreeEnergy_partner d v
  linarith [partnerEnergy_nonneg d v false, partnerEnergy_nonneg d v true]

theorem expectedNoise_le_energy (d : ℕ) (v : CenteredState (d + 1)) (t : ℕ) :
    expectedNoise d v t ≤ expectedEnergy d v t := by
  apply mean_le_mean
  intro ω
  exact oneFreeEnergy_le d (iterateState d v t ω).raw

theorem noise_bound_balanced_state (d : ℕ) (v : CenteredState (d + 2))
    (β : ℝ) (hb : ∀ h, β ≤ startHalfDensity (d + 1) v.raw h) :
    expectedNoise (d + 1) v (d + 1) ≤ (1 - β) * expectedEnergy (d + 1) v (d + 1) := by
  have he := noise_bound_balanced_halves d v.raw β hb
  simp_rw [← iterateState_raw] at he
  exact he

def singleHistory (d : ℕ) : Coins d ≃ History d 1 where
  toFun c := fun _ => c
  invFun ω := ω 0
  left_inv _ := rfl
  right_inv ω := by
    funext i
    change ω 0 = ω i
    rw [Subsingleton.elim i 0]

theorem mean_history_one (d : ℕ) (f : History d 1 → ℝ) :
    mean f = mean (fun c : Coins d => f (fun _ => c)) :=
  (mean_equiv (singleHistory d) f).symm

@[simp] theorem iterateState_one (d : ℕ) (v : CenteredState (d + 1)) (c : Coins (d + 1)) :
    iterateState d v 1 (fun _ => c) = nextState d v c := rfl

theorem expectedEnergy_first (d t : ℕ) (v : CenteredState (d + 1)) :
    expectedEnergy d v (t + 1) =
      mean (fun c : Coins (d + 1) => expectedEnergy d (nextState d v c) t) := by
  rw [Nat.add_comm t 1, expectedEnergy_add, mean_history_one]
  rfl

theorem expectedNoise_first (d t : ℕ) (v : CenteredState (d + 1)) :
    expectedNoise d v (t + 1) =
      mean (fun c : Coins (d + 1) => expectedNoise d (nextState d v c) t) := by
  rw [Nat.add_comm t 1, expectedNoise_add, mean_history_one]
  rfl

theorem expectedNoise_dimension (d : ℕ) (v : CenteredState (d + 2))
    (hm : Fintype.card (Position (d + 2)) ≤ 8 * freeCount v.free) :
    expectedNoise (d + 1) v (d + 2) ≤ (15 / 16 : ℝ) * expectedEnergy (d + 1) v (d + 2) +
      2 * (9 / 10 : ℝ) ^ freeCount v.free := by
  let B := v.free ∘ (splitPosition (d + 1)).symm
  let bad (c : Coins (d + 2)) : Prop :=
    4 * pairHalfCount B c false < pairFreeCount B ∨
    4 * pairHalfCount B c true < pairFreeCount B
  have hlocal (c : Coins (d + 2)) :
      expectedNoise (d + 1) (nextState (d + 1) v c) (d + 1) ≤
      (15 / 16 : ℝ) * expectedEnergy (d + 1) (nextState (d + 1) v c) (d + 1) +
        (if bad c then 1 else 0) := by
    by_cases hc : bad c
    · rw [ite_eq_left hc]
      have hle := expectedNoise_le_energy (d + 1) (nextState (d + 1) v c) (d + 1)
      have hone := expectedEnergy_le_one (d + 1) (nextState (d + 1) v c) (d + 1)
      linarith
    · rw [ite_eq_right hc, add_zero]
      have hb (h : Bool) : (1 / 16 : ℝ) ≤
          startHalfDensity (d + 1) (nextState (d + 1) v c).raw h := by
        apply halfDensity_after_step (d + 1) v.raw c h hm
        have hf : ¬ 4 * pairHalfCount B c false < freeCount v.free := by
          simpa only [B, pairFreeCount_physical] using not_or.mp hc |>.1
        have ht : ¬ 4 * pairHalfCount B c true < freeCount v.free := by
          simpa only [B, pairFreeCount_physical] using not_or.mp hc |>.2
        change freeCount v.free ≤ 4 * pairHalfCount B c h
        cases h
        · exact Nat.le_of_not_gt hf
        · exact Nat.le_of_not_gt ht
      convert noise_bound_balanced_state d (nextState (d + 1) v c) (1 / 16) hb using 1; norm_num
  have hmean := mean_le_mean hlocal
  rw [mean_add, mean_const_mul, ← expectedNoise_first, ← expectedEnergy_first] at hmean
  have hbad := pair_both_half_balance B
  have hbad' : mean (fun c : Coins (d + 2) => if bad c then (1 : ℝ) else 0) ≤
      2 * (9 / 10 : ℝ) ^ freeCount v.free := by
    change mean (fun c : Position (d + 1) → Bool => if bad c then (1 : ℝ) else 0) ≤ _
    simpa only [bad, B, pairFreeCount_physical] using hbad
  exact hmean.trans (add_le_add (le_refl _) hbad')

theorem expectedNoise_bound (d : ℕ) (v : CenteredState (d + 2))
    (hm : Fintype.card (Position (d + 2)) ≤ 8 * freeCount v.free)
    (s : ℕ) (hs : d + 2 ≤ s) :
    expectedNoise (d + 1) v s ≤ (15 / 16 : ℝ) * expectedEnergy (d + 1) v s +
      2 * (9 / 10 : ℝ) ^ freeCount v.free := by
  obtain ⟨a, rfl⟩ := Nat.exists_eq_add_of_le hs
  rw [Nat.add_comm (d + 2) a, expectedNoise_add, expectedEnergy_add]
  have he := mean_le_mean (fun ω : History (d + 2) a =>
    expectedNoise_dimension d (iterateState (d + 1) v a ω)
      (by simpa only [iterateState_freeCount] using hm))
  simpa only [iterateState_freeCount, mean_add, mean_const_mul, mean_const] using he

end Conditional

namespace Conditional

theorem expectedEnergy_decay (d : ℕ) (v : CenteredState (d + 2))
    (hm : Fintype.card (Position (d + 2)) ≤ 8 * freeCount v.free) (t : ℕ) :
    expectedEnergy (d + 1) v t ≤
      (31 / 32 : ℝ) ^ t / (31 / 32 : ℝ) ^ (2 * (d + 2)) +
        32 * (9 / 10 : ℝ) ^ freeCount v.free := by
  have he := scalar_decay (d + 2) (expectedEnergy (d + 1) v)
    (expectedNoise (d + 1) v) (1 / 16) (31 / 32)
    (2 * (9 / 10 : ℝ) ^ freeCount v.free)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by positivity) (expectedEnergy_le_one (d + 1) v)
    (expectedEnergy_recurrence (d + 1) v)
    (by intro s hs; convert expectedNoise_bound d v hm s hs using 1; norm_num) t
  convert he using 1; ring

theorem expectedEnergy_200 (d : ℕ) (v : CenteredState (d + 2))
    (hm : Fintype.card (Position (d + 2)) ≤ 8 * freeCount v.free) :
    expectedEnergy (d + 1) v (200 * (d + 2)) ≤
      (1 / 2 : ℝ) ^ (8 * (d + 2)) + 32 * (9 / 10 : ℝ) ^ freeCount v.free := by
  have he := expectedEnergy_decay d v hm (200 * (d + 2))
  have hp : (31 / 32 : ℝ) ^ (200 * (d + 2)) / (31 / 32 : ℝ) ^ (2 * (d + 2)) =
      (31 / 32 : ℝ) ^ (198 * (d + 2)) := by
    have hn : 200 * (d + 2) = 198 * (d + 2) + 2 * (d + 2) := by omega
    rw [hn, pow_add, mul_div_cancel_right₀ _ (by positivity)]
  rw [hp] at he
  have hpow := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (31 / 32) ^ 198)
    eight_block_geometric_choice (d + 2)
  rw [← pow_mul, ← pow_mul] at hpow
  exact he.trans (add_le_add hpow (le_refl _))

theorem centeredPoint_energy_200 (d : ℕ) (B : Position (d + 2) → Bool)
    (tag : Position (d + 2)) (ht : B tag = true)
    (hm : Fintype.card (Position (d + 2)) ≤ 8 * freeCount B) :
    expectedEnergy (d + 1) (initialState (d + 2) B tag ht) (200 * (d + 2)) ≤
      (1 / 2 : ℝ) ^ (8 * (d + 2)) + 32 * (9 / 10 : ℝ) ^ freeCount B :=
  expectedEnergy_200 d _ hm

end Conditional

end Thorp

end

end OAI
