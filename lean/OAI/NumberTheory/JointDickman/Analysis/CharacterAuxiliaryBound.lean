import OAI.NumberTheory.JointDickman.Analysis.MovingCharacterBound

namespace OAI

/-! # Uniform character cancellation on the manuscript's scale -/

namespace JointDickman

open Finset Filter
open scoped Topology

theorem auxiliary_modulus_bound : ∀ᶠ B : ℕ in atTop,
    ∀ L : ℝ, (B : ℝ) ^ (89 / 100 : ℝ) ≤ L →
      (B : ℝ) ^ (100 : ℝ) ≤ (L / 2) ^ (200 : ℝ) := by
  have hlarge : ∀ᶠ B : ℕ in atTop, (2 : ℝ) ≤ (B : ℝ) ^ (39 / 100 : ℝ) :=
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 39 / 100)).comp
      tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop 2)
  filter_upwards [hlarge, eventually_gt_atTop 0] with B hlargeB hB
  intro L hL
  have hB0 : (0 : ℝ) < B := by exact_mod_cast hB
  have hpow : (B : ℝ) ^ (1 / 2 : ℝ) ≤ L / 2 := by
    have heq : (B : ℝ) ^ (89 / 100 : ℝ) =
        (B : ℝ) ^ (1 / 2 : ℝ) * (B : ℝ) ^ (39 / 100 : ℝ) := by
      rw [← Real.rpow_add hB0]
      norm_num
    rw [heq] at hL
    nlinarith [Real.rpow_pos_of_pos hB0 (1 / 2 : ℝ)]
  calc
    _ = ((B : ℝ) ^ (1 / 2 : ℝ)) ^ (200 : ℝ) := by
      rw [← Real.rpow_mul hB0.le]
      norm_num
    _ ≤ _ := Real.rpow_le_rpow (Real.rpow_nonneg hB0.le _) hpow (by norm_num)

/-- Cancellation after moving small-prime removal holds for all
nonprincipal characters of modulus at most `B^100`. -/
theorem moving_rough_character_bound
    (hSW : PublishedInputs.SquarefreeCharacterEstimateInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) {z D : ℝ}
    (hz : z = 1 / 4 ∨ z = 1 / 2) (hD : 0 ≤ D) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ B : ℕ in atTop, ∀ Y : ℝ,
      (B : ℝ) ^ (89 / 100 : ℝ) ≤ Real.log Y → 9 ≤ Y →
      ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ (B : ℝ) ^ (100 : ℝ) →
      ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
      ‖roughCharacterSum χ (Nat.primesLE (auxiliaryCutoff B)) z Y‖ ≤
        K * Y * (B : ℝ) ^ (-D) := by
  let E : ℝ := 2 * (D + 1)
  have hE : 0 ≤ E := by dsimp [E]; linarith
  obtain ⟨K, hK, hbound⟩ := roughCharacterSum_exponential hSW hM hz hE
  refine ⟨K, hK, ?_⟩
  have hgap : D + (89 / 100 : ℝ) * ((2 - E) - 2 - (0 : ℕ)) < 0 := by
    dsimp [E]
    norm_num
    linarith
  have hlim := (roughErrorEnvelope_tendsto hgap).comp tendsto_natCast_atTop_atTop
  have hsmall : ∀ᶠ B : ℕ in atTop,
      (B : ℝ) ^ D * roughErrorEnvelope (2 - E) 0 B ≤ 1 :=
    hlim.eventually (eventually_le_nhds (by norm_num : (0 : ℝ) < 1))
  have hlarge : ∀ᶠ B : ℕ in atTop, (16 : ℝ) ≤ (B : ℝ) ^ (89 / 100 : ℝ) :=
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 89 / 100)).comp
      tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop 16)
  have hP : ∀ᶠ B : ℕ in atTop, 2 ≤ auxiliaryCutoff B :=
    auxiliaryCutoff_tendsto.eventually (eventually_ge_atTop 2)
  have hlog : ∀ᶠ B : ℕ in atTop, 1 ≤ Real.log (auxiliaryCutoff B) :=
    (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp auxiliaryCutoff_tendsto)).eventually
      (eventually_ge_atTop 1)
  filter_upwards [hsmall, hlarge, hP, hlog, auxiliary_modulus_bound,
    eventually_gt_atTop 1] with B hs hl hp hlogP hmod hB
  intro Y hY hY9 q _ hq χ hχ
  have hB0 : (0 : ℝ) < B := by exact_mod_cast (lt_trans Nat.zero_lt_one hB)
  have henv : roughErrorEnvelope (2 - E) 0 B ≤ (B : ℝ) ^ (-D) := by
    rw [Real.rpow_neg hB0.le, ← one_div]
    exact (le_div_iff₀ (Real.rpow_pos_of_pos hB0 D)).mpr (by simpa [mul_comm] using hs)
  have hpoint : (Real.log Y) ^ (-E) *
      (Real.log (auxiliaryCutoff B)) ^ (Real.exp 1 + 1) +
      (Real.log (auxiliaryCutoff B)) ^ (Real.exp 1) *
        Real.exp (-(Real.log Y / (8 * Real.log (auxiliaryCutoff B)))) ≤
      roughErrorEnvelope (2 - E) 0 B := by
    have h := rough_error_at_auxiliaryCutoff (H := 0) (z := 2 - E) hB
      (by dsimp [E]; linarith) hY
    simp only [Nat.cast_zero, sub_zero, Nat.reduceAdd, Nat.cast_one, add_zero] at h
    rw [show 2 - E - 2 = -E by ring] at h
    exact h
  calc
    _ ≤ Y * K * ((Real.log Y) ^ (-E) *
        (Real.log (auxiliaryCutoff B)) ^ (Real.exp 1 + 1) +
        (Real.log (auxiliaryCutoff B)) ^ (Real.exp 1) *
          Real.exp (-(Real.log Y / (8 * Real.log (auxiliaryCutoff B))))) :=
      hbound (auxiliaryCutoff B) Y hp hlogP hY9 (hl.trans hY) q
        (hq.trans (hmod (Real.log Y) hY)) χ hχ
    _ ≤ Y * K * roughErrorEnvelope (2 - E) 0 B :=
      mul_le_mul_of_nonneg_left hpoint (by positivity)
    _ ≤ Y * K * (B : ℝ) ^ (-D) := mul_le_mul_of_nonneg_left henv (by positivity)
    _ = _ := by ring

end JointDickman

end OAI
