import OAI.Probability.ThorpShuffle.Main

namespace OAI


noncomputable section
open scoped BigOperators
open Filter
namespace Thorp
namespace Conditional

theorem halfDensity_after_step_sixteen (d : ℕ) (v : RawState (d + 1))
    (c : Coins (d + 1)) (h : Bool)
    (hm : Fintype.card (Position (d + 1)) ≤ 16 * freeCount v.free)
    (hc : freeCount v.free ≤ 4 * pairHalfCount (v.free ∘ (splitPosition d).symm) c h) :
    (1 / 32 : ℝ) ≤ startHalfDensity d (rawNext d v c) h := by
  unfold startHalfDensity
  rw [halfCount_after_step]
  have hn : Fintype.card (Position (d + 1)) = 2 * Fintype.card (Position d) := by
    simp [Fintype.card_pi, Fintype.card_bool, Fintype.card_fin, pow_succ, Nat.mul_comm]
  rw [hn] at hm
  have hm' : (2 : ℝ) * Fintype.card (Position d) ≤ 16 * (freeCount v.free : ℝ) := by
    exact_mod_cast hm
  have hc' : (freeCount v.free : ℝ) ≤
      4 * (pairHalfCount (v.free ∘ (splitPosition d).symm) c h : ℝ) := by exact_mod_cast hc
  apply (le_div_iff₀ (by exact_mod_cast Fintype.card_pos (α := Position d))).mpr
  nlinarith

theorem expectedNoise_dimension_sixteen (d : ℕ) (v : CenteredState (d + 2))
    (hm : Fintype.card (Position (d + 2)) ≤ 16 * freeCount v.free) :
    expectedNoise (d + 1) v (d + 2) ≤ (31 / 32 : ℝ) * expectedEnergy (d + 1) v (d + 2) +
      2 * (9 / 10 : ℝ) ^ freeCount v.free := by
  let B := v.free ∘ (splitPosition (d + 1)).symm
  let bad (c : Coins (d + 2)) : Prop :=
    4 * pairHalfCount B c false < pairFreeCount B ∨
    4 * pairHalfCount B c true < pairFreeCount B
  have hlocal (c : Coins (d + 2)) :
      expectedNoise (d + 1) (nextState (d + 1) v c) (d + 1) ≤
      (31 / 32 : ℝ) * expectedEnergy (d + 1) (nextState (d + 1) v c) (d + 1) +
        (if bad c then 1 else 0) := by
    by_cases hc : bad c
    · rw [ite_eq_left hc]
      have hle := expectedNoise_le_energy (d + 1) (nextState (d + 1) v c) (d + 1)
      have hone := expectedEnergy_le_one (d + 1) (nextState (d + 1) v c) (d + 1)
      linarith
    · rw [ite_eq_right hc, add_zero]
      have hb (h : Bool) : (1 / 32 : ℝ) ≤
          startHalfDensity (d + 1) (nextState (d + 1) v c).raw h := by
        apply halfDensity_after_step_sixteen (d + 1) v.raw c h hm
        have hf : ¬ 4 * pairHalfCount B c false < freeCount v.free := by
          simpa only [B, pairFreeCount_physical] using not_or.mp hc |>.1
        have ht : ¬ 4 * pairHalfCount B c true < freeCount v.free := by
          simpa only [B, pairFreeCount_physical] using not_or.mp hc |>.2
        change freeCount v.free ≤ 4 * pairHalfCount B c h
        cases h
        · exact Nat.le_of_not_gt hf
        · exact Nat.le_of_not_gt ht
      convert noise_bound_balanced_state d (nextState (d + 1) v c) (1 / 32) hb using 1; norm_num
  have hmean := mean_le_mean hlocal
  rw [mean_add, mean_const_mul, ← expectedNoise_first, ← expectedEnergy_first] at hmean
  have hbad := pair_both_half_balance B
  have hbad' : mean (fun c : Coins (d + 2) => if bad c then (1 : ℝ) else 0) ≤
      2 * (9 / 10 : ℝ) ^ freeCount v.free := by
    change mean (fun c : Position (d + 1) → Bool => if bad c then (1 : ℝ) else 0) ≤ _
    simpa only [bad, B, pairFreeCount_physical] using hbad
  exact hmean.trans (add_le_add (le_refl _) hbad')

theorem expectedNoise_bound_sixteen (d : ℕ) (v : CenteredState (d + 2))
    (hm : Fintype.card (Position (d + 2)) ≤ 16 * freeCount v.free)
    (s : ℕ) (hs : d + 2 ≤ s) :
    expectedNoise (d + 1) v s ≤ (31 / 32 : ℝ) * expectedEnergy (d + 1) v s +
      2 * (9 / 10 : ℝ) ^ freeCount v.free := by
  obtain ⟨a, rfl⟩ := Nat.exists_eq_add_of_le hs
  rw [Nat.add_comm (d + 2) a, expectedNoise_add, expectedEnergy_add]
  have he := mean_le_mean (fun ω : History (d + 2) a =>
    expectedNoise_dimension_sixteen d (iterateState (d + 1) v a ω)
      (by simpa only [iterateState_freeCount] using hm))
  simpa only [iterateState_freeCount, mean_add, mean_const_mul, mean_const] using he

theorem expectedEnergy_decay_sixteen (d : ℕ) (v : CenteredState (d + 2))
    (hm : Fintype.card (Position (d + 2)) ≤ 16 * freeCount v.free) (t : ℕ) :
    expectedEnergy (d + 1) v t ≤
      (63 / 64 : ℝ) ^ t / (63 / 64 : ℝ) ^ (2 * (d + 2)) +
        64 * (9 / 10 : ℝ) ^ freeCount v.free := by
  have he := scalar_decay (d + 2) (expectedEnergy (d + 1) v)
    (expectedNoise (d + 1) v) (1 / 32) (63 / 64)
    (2 * (9 / 10 : ℝ) ^ freeCount v.free)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by positivity) (expectedEnergy_le_one (d + 1) v)
    (expectedEnergy_recurrence (d + 1) v)
    (by intro s hs; convert expectedNoise_bound_sixteen d v hm s hs using 1; norm_num) t
  convert he using 1; ring

theorem expectedEnergy_long (d C : ℕ) (v : CenteredState (d + 2))
    (hm : Fintype.card (Position (d + 2)) ≤ 16 * freeCount v.free) :
    expectedEnergy (d + 1) v ((C + 2) * (d + 2)) ≤
      (63 / 64 : ℝ) ^ (C * (d + 2)) + 64 * (9 / 10 : ℝ) ^ freeCount v.free := by
  have he := expectedEnergy_decay_sixteen d v hm ((C + 2) * (d + 2))
  rw [Nat.add_mul, pow_add, mul_div_cancel_right₀ _ (by positivity)] at he
  simpa only [Nat.add_mul] using he

theorem prefix_test_bound_sixteen (d C m : ℕ)
    (hm : Fintype.card (Position (d + 2)) ≤ 16 * m)
    (k : ℕ) (hk : k + m ≤ Fintype.card (Position (d + 2)))
    (e : Fin k → Position (d + 2)) (he : Function.Injective e)
    (f : (Fin k → Position (d + 2)) → ℝ) (hf : ∀ z, |f z| ≤ 1) :
    |mean (fun ω : History (d + 2) ((C + 2) * (d + 2)) =>
        f ((run (d + 2) ((C + 2) * (d + 2)) ω) ∘ e)) -
      mean (fun g : State (d + 2) => f (g ∘ e))| ≤
    (k : ℝ) * Real.sqrt ((Fintype.card (Position (d + 2)) : ℝ) *
      ((63 / 64 : ℝ) ^ (C * (d + 2)) + 64 * (9 / 10 : ℝ) ^ m)) := by
  induction k with
  | zero =>
    have hz (g : State (d + 2)) : g ∘ e = e := by funext i; exact Fin.elim0 i
    simp only [hz, mean_const, sub_self, abs_zero, Nat.cast_zero, zero_mul, le_refl]
  | succ k ih =>
    have he0 : Function.Injective (Fin.init e) := by
      intro i j hij
      exact Fin.castSucc_inj.mp (he hij)
    have ht : freeOf (Fin.init e) (e (Fin.last k)) = true := by
      apply (freeOf_true _ _).mpr
      intro i hi
      exact Fin.castSucc_ne_last i (he hi)
    have hcount : m ≤ freeCount (freeOf (Fin.init e)) := by
      rw [freeCount_freeOf _ he0]
      omega
    have henergy := expectedEnergy_long d C
      (initialState (d + 2) (freeOf (Fin.init e)) (e (Fin.last k)) ht) (by
        change Fintype.card (Position (d + 2)) ≤ 16 * freeCount (freeOf (Fin.init e))
        omega)
    have hpower : (9 / 10 : ℝ) ^ freeCount (freeOf (Fin.init e)) ≤ (9 / 10 : ℝ) ^ m :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) hcount
    have hz := prefix_one_step_bound (d + 1) ((C + 2) * (d + 2)) k e he f hf
    have hestimate :
        Real.sqrt ((Fintype.card (Position (d + 2)) : ℝ) *
          expectedEnergy (d + 1) (initialState (d + 2) (freeOf (Fin.init e)) (e (Fin.last k)) ht)
            ((C + 2) * (d + 2))) ≤
        Real.sqrt ((Fintype.card (Position (d + 2)) : ℝ) *
          ((63 / 64 : ℝ) ^ (C * (d + 2)) + 64 * (9 / 10 : ℝ) ^ m)) := by
      apply Real.sqrt_le_sqrt
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      exact henergy.trans (add_le_add (le_refl _) (mul_le_mul_of_nonneg_left hpower (by norm_num : (0 : ℝ) ≤ 64)))
    have hnext := ih (by omega) (Fin.init e) he0 (completeTest f) (completeTest_bound f hf)
    rw [uniform_prefix_step k e he f]
    have htri := abs_sub_le
      (mean (fun ω : History (d + 2) ((C + 2) * (d + 2)) =>
        f ((run (d + 2) ((C + 2) * (d + 2)) ω) ∘ e)))
      (mean (fun ω : History (d + 2) ((C + 2) * (d + 2)) =>
        completeTest f ((run (d + 2) ((C + 2) * (d + 2)) ω) ∘ Fin.init e)))
      (mean (fun g : State (d + 2) => completeTest f (g ∘ Fin.init e)))
    have hz' := hz.trans hestimate
    push_cast
    nlinarith

end Conditional
end Thorp

end

end OAI
