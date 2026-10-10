import OAI.MathematicalPhysics.AlternatingFlow.Machines

namespace OAI

open scoped BigOperators ENNReal NNReal Topology ContDiff
open MeasureTheory
namespace AlternatingNS
namespace Profiles

noncomputable def selector (b a : ℕ) (v : ℝ) : ℝ :=
  letI := twoAtLeastTwo
  letI := eightAtLeastTwo
  Real.smoothTransition (8 * ((b : ℝ) * v - 2 * a) + 2) *
    Real.smoothTransition (8 * (2 * a + 1 - (b : ℝ) * v) + 2)

lemma selector_smooth (b a : ℕ) : ContDiff ℝ ∞ (selector b a) := by
  unfold selector
  fun_prop

lemma selector_nonneg (b a : ℕ) (v : ℝ) : 0 ≤ selector b a v :=
  mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)

lemma selector_le_one (b a : ℕ) (v : ℝ) : selector b a v ≤ 1 := by
  exact (mul_le_of_le_one_left (Real.smoothTransition.nonneg _)
    (Real.smoothTransition.le_one _)).trans (Real.smoothTransition.le_one _)

lemma selector_one (b a : ℕ) (v : ℝ)
    (h₀ : 2 * (a : ℝ) - 1 / 8 ≤ b * v) (h₁ : (b : ℝ) * v ≤ 2 * a + 9 / 8) :
    selector b a v = 1 := by
  rw [selector, Real.smoothTransition.one_of_one_le (by linarith),
    Real.smoothTransition.one_of_one_le (by linarith)]
  norm_num

lemma selector_zero_left (b a : ℕ) (v : ℝ) (h : (b : ℝ) * v ≤ 2 * a - 1 / 4) :
    selector b a v = 0 := by
  rw [selector, Real.smoothTransition.zero_of_nonpos (by linarith), zero_mul]

lemma selector_zero_right (b a : ℕ) (v : ℝ) (h : 2 * (a : ℝ) + 5 / 4 ≤ b * v) :
    selector b a v = 0 := by
  rw [selector, Real.smoothTransition.zero_of_nonpos (by linarith :
    8 * (2 * (a : ℝ) + 1 - b * v) + 2 ≤ 0), mul_zero]

lemma selector_support_bound (b a : ℕ) (v : ℝ) (h : selector b a v ≠ 0) :
    2 * (a : ℝ) - 1 / 4 < b * v ∧ (b : ℝ) * v < 2 * a + 5 / 4 := by
  constructor
  · by_contra hn
    exact h (selector_zero_left b a v (le_of_not_gt hn))
  · by_contra hn
    exact h (selector_zero_right b a v (le_of_not_gt hn))

lemma selector_support_disjoint (b a q : ℕ) (haq : a ≠ q) :
    Disjoint (Function.support (selector b a)) (Function.support (selector b q)) := by
  rw [Set.disjoint_left]
  intro v ha hq
  obtain ⟨ha₀, ha₁⟩ := selector_support_bound b a v ha
  obtain ⟨hq₀, hq₁⟩ := selector_support_bound b q v hq
  rcases lt_or_gt_of_ne haq with h | h
  · have h' : (a : ℝ) + 1 ≤ q := by exact_mod_cast h
    linarith
  · have h' : (q : ℝ) + 1 ≤ a := by exact_mod_cast h
    linarith

lemma selector_on_cell (b a q : ℕ) (v : ℝ)
    (h₀ : 2 * (q : ℝ) ≤ b * v) (h₁ : (b : ℝ) * v ≤ 2 * q + 1) :
    selector b a v = if a = q then 1 else 0 := by
  split_ifs with h
  · subst a
    apply selector_one <;> linarith
  · rcases lt_or_gt_of_ne h with ha | ha
    · have h' : (a : ℝ) + 1 ≤ q := by exact_mod_cast ha
      apply selector_zero_right
      linarith
    · have h' : (q : ℝ) + 1 ≤ a := by exact_mod_cast ha
      apply selector_zero_left
      linarith

lemma selector_code (b a q : ℕ) (hb : 2 ≤ b) (L : List ℕ)
    (hL : ∀ d ∈ L, d + 2 ≤ b) :
    selector b a (Encoding.code b (2 * q :: L)) = if a = q then 1 else 0 := by
  have hb' : (0 : ℝ) < b := by exact_mod_cast (show 0 < b by omega)
  have h := Encoding.digit_interval b (2 * q) hb L hL
  have h₀ := (div_le_iff₀ hb').1 h.1
  have h₁ := (le_div_iff₀ hb').1 h.2
  push_cast at h₀ h₁
  apply selector_on_cell <;> nlinarith

lemma selector_streamCode (b a q K : ℕ) (hb : 2 ≤ b) (hK : 0 < K) (f : ℕ → ℕ)
    (hf : ∀ j, f j + 2 ≤ b) (h₀ : f 0 = 2 * q) :
    selector b a (Encoding.streamCode b K f) = if a = q then 1 else 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hK)
  rw [Encoding.streamCode, Encoding.digits_succ, h₀]
  apply selector_code b a q hb
  intro d hd
  obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hd
  exact hf _

end Profiles

namespace Machine

lemma selector_recordedBlock (M : Machine) (hM : M.WellFormed) (w : List ℕ)
    (hw : M.ValidInput w) (n q : ℕ) :
    Profiles.selector M.base q (M.recordedBlock w n) =
      if q = (M.run w n).state then 1 else 0 := by
  apply Profiles.selector_code _ _ _ (by have := base_ge_four M; omega)
  intro d hd
  exact recordedDigits_bound M hM w hw n d (List.mem_cons_of_mem _ hd)

lemma selector_leftCode (M : Machine) (c : Configuration) (hc : M.Admissible c) (N n a : ℕ) :
    Profiles.selector M.base a (leftCode M.base N n c) =
      if a = c.tape (c.head - 1) then 1 else 0 := by
  apply Profiles.selector_streamCode _ _ _ _ (by have := base_ge_four M; omega)
    (by dsimp [Scales.K]; omega)
  · intro j
    exact symbol_digit_bound M _ (hc.2 _)
  · simp [leftDigits]

lemma selector_rightCode (M : Machine) (c : Configuration) (hc : M.Admissible c) (N n a : ℕ) :
    Profiles.selector M.base a (rightCode M.base N n c) =
      if a = c.tape c.head then 1 else 0 := by
  apply Profiles.selector_streamCode _ _ _ _ (by have := base_ge_four M; omega)
    (by dsimp [Scales.K]; omega)
  · intro j
    exact symbol_digit_bound M _ (hc.2 _)
  · simp [rightDigits]

end Machine
end AlternatingNS

end OAI
