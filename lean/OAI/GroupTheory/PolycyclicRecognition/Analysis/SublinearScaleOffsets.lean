import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Tactic

namespace OAI

/-! # Vanishing offsets from the local comparison of adjacent scales -/

namespace PolycyclicRecognition

open Filter
open scoped Topology

/-- The scale-comparison estimate in the height argument forces its offsets
to be uniformly sublinear. Only finitely many contractions are needed for
each prescribed error, so no regularity of the offset as a function of scale
is required. -/
theorem uniform_sublinear_of_contractive_increments
    {P W : Type*} [NormedAddCommGroup W]
    (s : P → ℝ → W) {q C : ℝ} (hq : 0 < q) (hq1 : q < 1)
    (hbound : ∀ p r, 1 ≤ r → ‖s p r‖ ≤ C * r)
    (hincrement : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 1 ≤ R ∧
      ∀ p r, R ≤ r → ‖s p r - s p (q * r)‖ ≤ ε * r) :
    ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 1 ≤ R ∧
      ∀ p r, R ≤ r → ‖s p r‖ ≤ ε * r := by
  intro ε hε
  let e := ε * (1 - q) / 2
  have he : 0 < e := div_pos (mul_pos hε (sub_pos.mpr hq1)) (by norm_num)
  obtain ⟨R, hR1, hinc⟩ := hincrement e he
  have hiter : ∀ k : ℕ, ∀ p r, R ≤ q ^ k * r →
      ‖s p r‖ ≤ (C * q ^ k + e / (1 - q)) * r := by
    intro k
    induction k with
    | zero =>
      intro p r hr
      have hr' : R ≤ r := by simpa using hr
      have hh := hbound p r (hR1.trans hr')
      have he' : 0 ≤ e / (1 - q) := div_nonneg he.le (sub_pos.mpr hq1).le
      simp only [pow_zero, mul_one]
      nlinarith [mul_nonneg he' (show 0 ≤ r by linarith)]
    | succ k ih =>
      intro p r hr
      have hrpos : 0 < r := pos_of_mul_pos_right
        (lt_of_lt_of_le (lt_of_lt_of_le zero_lt_one hR1) hr) (pow_nonneg hq.le _)
      have hpow : q ^ (k + 1) ≤ 1 := pow_le_one₀ hq.le hq1.le
      have hRr : R ≤ r := hr.trans ((mul_le_mul_of_nonneg_right hpow hrpos.le).trans_eq (one_mul r))
      have hsub : R ≤ q ^ k * (q * r) := by simpa only [pow_succ, mul_assoc] using hr
      calc
        ‖s p r‖ = ‖(s p r - s p (q * r)) + s p (q * r)‖ := by rw [sub_add_cancel]
        _ ≤ ‖s p r - s p (q * r)‖ + ‖s p (q * r)‖ := norm_add_le _ _
        _ ≤ e * r + (C * q ^ k + e / (1 - q)) * (q * r) :=
          add_le_add (hinc p r hRr) (ih p (q * r) hsub)
        _ = (C * q ^ (k + 1) + e / (1 - q)) * r := by
          rw [pow_succ]
          field_simp [(sub_pos.mpr hq1).ne']; ring
  have hlim : Tendsto (fun k : ℕ => C * q ^ k) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hq.le hq1).const_mul C
  obtain ⟨k, hk⟩ := (hlim.eventually (gt_mem_nhds (half_pos hε))).exists
  refine ⟨max 1 (R / q ^ k), le_max_left _ _, ?_⟩
  intro p r hr
  have hr0 : 0 ≤ r := zero_le_one.trans ((le_max_left _ _).trans hr)
  have hkr : R ≤ q ^ k * r := by
    have hh := (div_le_iff₀ (pow_pos hq k)).mp ((le_max_right _ _).trans hr)
    simpa only [mul_comm] using hh
  have heq : e / (1 - q) = ε / 2 := by
    dsimp only [e]
    field_simp [(sub_pos.mpr hq1).ne']
  apply (hiter k p r hkr).trans
  rw [heq]
  exact mul_le_mul_of_nonneg_right (by linarith) hr0

end PolycyclicRecognition

end OAI
