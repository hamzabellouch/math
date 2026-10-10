import OAI.Analysis.LipschitzHilbert.Estimates.VariationSum

namespace OAI

/-! The variation of packet partial sums is bounded by the sum of packet
norms. This is used for the long-scale spatial oscillation and error terms. -/

noncomputable section
open scoped BigOperators

namespace LipschitzHilbert

def packetPartialSum {E : Type*} [AddCommMonoid E] {N : ℕ}
    (f : Fin N → E) (n : ℕ) : E := ∑ j, if j.val < n then f j else 0

theorem monotone_partition_crossing_unique {N j : ℕ}
    (p : Fin (N + 1) → Fin (N + 1)) (hp : Monotone p)
    {i k : Fin N} (hi : (p i.castSucc).val ≤ j ∧ j < (p i.succ).val)
    (hk : (p k.castSucc).val ≤ j ∧ j < (p k.succ).val) : i = k := by
  rcases lt_trichotomy i k with hik | hik | hik
  · have h := hp (show i.succ ≤ k.castSucc by
      simpa only [Fin.le_def, Fin.val_succ, Fin.val_castSucc] using
        (Nat.succ_le_of_lt (show i.val < k.val from hik)))
    have h' : (p i.succ).val ≤ (p k.castSucc).val := h
    omega
  · exact hik
  · have h := hp (show k.succ ≤ i.castSucc by
      simpa only [Fin.le_def, Fin.val_succ, Fin.val_castSucc] using
        (Nat.succ_le_of_lt (show k.val < i.val from hik)))
    have h' : (p k.succ).val ≤ (p i.castSucc).val := h
    omega

theorem partition_single_step_cube_le {E : Type*} [NormedAddCommGroup E]
    (v : E) (j N : ℕ) (p : Fin (N + 1) → Fin (N + 1)) (hp : Monotone p) :
    (∑ i : Fin N, ‖(if j < (p i.succ).val then v else 0) -
      (if j < (p i.castSucc).val then v else 0)‖ ^ 3) ≤ ‖v‖ ^ 3 := by
  classical
  have hterm (i : Fin N) : ‖(if j < (p i.succ).val then v else 0) -
      (if j < (p i.castSucc).val then v else 0)‖ ^ 3 =
      if (p i.castSucc).val ≤ j ∧ j < (p i.succ).val then ‖v‖ ^ 3 else 0 := by
    have hle : (p i.castSucc).val ≤ (p i.succ).val := hp (Fin.castSucc_le_succ i)
    by_cases hlow : j < (p i.castSucc).val
    · have hhigh : j < (p i.succ).val := hlow.trans_le hle
      simp [hlow, hhigh, Nat.not_le.mpr hlow]
    · by_cases hhigh : j < (p i.succ).val
      · simp [hlow, hhigh, Nat.le_of_not_gt hlow]
      · simp [hlow, hhigh]
  simp_rw [hterm]
  by_cases hex : ∃ i : Fin N, (p i.castSucc).val ≤ j ∧ j < (p i.succ).val
  · obtain ⟨k,hk⟩ := hex
    rw [Finset.sum_eq_single k]
    · simp [hk]
    · intro i _ hik
      have hi : ¬ ((p i.castSucc).val ≤ j ∧ j < (p i.succ).val) :=
        fun hi => hik (monotone_partition_crossing_unique p hp hi hk)
      simp [hi]
    · simp
  · have hz (i : Fin N) : ¬ ((p i.castSucc).val ≤ j ∧ j < (p i.succ).val) :=
      fun hi => hex ⟨i,hi⟩
    simp only [hz, ite_false, Finset.sum_const_zero]
    positivity

theorem cubicVariation_single_step_le {E : Type*} [NormedAddCommGroup E]
    (v : E) (j N : ℕ) : cubicVariation (fun n => if j < n then v else 0) N ≤ ‖v‖ := by
  classical
  have hcube : finiteCubicVariation (fun n => if j < n then v else 0) N ≤ ‖v‖ ^ 3 := by
    apply Finset.sup'_le
    intro p _
    split_ifs with hp
    · exact partition_single_step_cube_le v j N p hp
    · positivity
  have h := Real.rpow_le_rpow (finiteCubicVariation_nonneg _ _) hcube (by norm_num : (0 : ℝ) ≤ 1 / 3)
  have hpow : (‖v‖ ^ 3) ^ (1 / 3 : ℝ) = ‖v‖ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg v)]
    norm_num
  simpa only [cubicVariation, hpow] using h

theorem cubicVariation_packetPartialSum_le {E : Type*} [NormedAddCommGroup E]
    {N : ℕ} (f : Fin N → E) : cubicVariation (packetPartialSum f) N ≤ ∑ j, ‖f j‖ := by
  change cubicVariation (fun n => ∑ j : Fin N, if j.val < n then f j else 0) N ≤ _
  exact (cubicVariation_finset_sum (fun (j : Fin N) (n : ℕ) => if j.val < n then f j else 0) Finset.univ N).trans
    (Finset.sum_le_sum (fun j _ => cubicVariation_single_step_le (f j) j.val N))

end LipschitzHilbert

end

end OAI
