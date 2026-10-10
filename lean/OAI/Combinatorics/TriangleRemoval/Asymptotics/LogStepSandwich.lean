import Mathlib

namespace OAI

section
noncomputable section
open scoped BigOperators

namespace SharpTerminalLeave

lemma log_step_sandwich {p q h : ℝ} (hp : 0 < p) (hq : 0 < q) (hs : p = q+h) :
    h/p ≤ Real.log p-Real.log q ∧ Real.log p-Real.log q ≤ h/q := by
  have hl := Real.log_le_sub_one_of_pos (div_pos hq hp)
  have hu := Real.log_le_sub_one_of_pos (div_pos hp hq)
  rw [Real.log_div (ne_of_gt hq) (ne_of_gt hp)] at hl
  rw [Real.log_div (ne_of_gt hp) (ne_of_gt hq)] at hu
  have he₁ : q/p-1 = -(h/p) := by field_simp; linarith only [hs]
  have he₂ : p/q-1 = h/q := by field_simp; linarith only [hs]
  rw [he₁] at hl
  rw [he₂] at hu
  exact ⟨by linarith only [hl],hu⟩

theorem density_log_sum_bounds (p : ℕ → ℝ) (h : ℝ) (T : ℕ)
    (hp : ∀ i ≤ T, 0 < p i) (hs : ∀ i < T, p i = p (i+1)+h) :
    (∑ i ∈ Finset.range T, h/p i) ≤ Real.log (p 0)-Real.log (p T) ∧
    Real.log (p 0)-Real.log (p T) ≤
      (∑ i ∈ Finset.range T, h/p i)+(h/p T-h/p 0) := by
  induction T with
  | zero => simp
  | succ T ih =>
    obtain ⟨hl,hu⟩ := ih (fun i hi => hp i (by omega)) (fun i hi => hs i (by omega))
    obtain ⟨sl,su⟩ := log_step_sandwich (hp T (by omega)) (hp (T+1) le_rfl) (hs T (by omega))
    rw [Finset.sum_range_succ]
    constructor <;> linarith only [hl,hu,sl,su]

lemma inverse_square_grid_step {a p q h : ℝ} (ha : 0 < a) (hp : 0 < p) (hq : 0 < q)
    (hh : 0 ≤ h) (hs : p = q+h) :
    2*h/(a*p^3) ≤ 1/(a*q^2)-1/(a*p^2) := by
  have hpq : q ≤ p := by linarith only [hs,hh]
  have hc : 2*q^2 ≤ p*(p+q) := by nlinarith [mul_nonneg (sub_nonneg.mpr hpq) (by linarith : 0 ≤ p+2*q)]
  have hm := mul_le_mul_of_nonneg_left hc hh
  have he : p^2-q^2 = h*(p+q) := by rw [hs]; ring
  apply (div_le_iff₀ (mul_pos ha (pow_pos hp 3))).mpr
  have hd : (1/(a*q^2)-1/(a*p^2))*(a*p^3) = (p^2-q^2)*p/q^2 := by
    field_simp
  rw [hd,he]
  apply (le_div_iff₀ (pow_pos hq 2)).mpr
  nlinarith only [hm]

theorem inverse_square_grid_sum (p : ℕ → ℝ) (a h : ℝ) (T : ℕ)
    (ha : 0 < a) (hh : 0 ≤ h) (hp : ∀ i ≤ T, 0 < p i)
    (hs : ∀ i < T, p i = p (i+1)+h) :
    (∑ i ∈ Finset.range T, 2*h/(a*p i^3)) ≤ 1/(a*p T^2)-1/(a*p 0^2) := by
  induction T with
  | zero => simp
  | succ T ih =>
    have hi := ih (fun i hi => hp i (by omega)) (fun i hi => hs i (by omega))
    have hstep := inverse_square_grid_step ha (hp T (by omega)) (hp (T+1) le_rfl) hh (hs T (by omega))
    rw [Finset.sum_range_succ]
    linarith only [hi,hstep]

theorem density_survival_exponent_bound (p : ℕ → ℝ) (a h b η : ℝ) (T : ℕ)
    (ha : 0 < a) (hh : 0 ≤ h) (hb : 0 ≤ b) (hη : 0 ≤ η)
    (hp : ∀ i ≤ T, 0 < p i) (hs : ∀ i < T, p i = p (i+1)+h)
    (hp0 : p 0 ≤ 1) :
    (∑ i ∈ Finset.range T, (-b*(h/p i)+2*b*η*(h/p i)+b^2*(2*h/(a*p i^3)))) ≤
      b*Real.log (p T)+b*(1-p 0)/p 0+b*h/p T+
        2*b*η*(-Real.log (p T))+b^2/(a*p T^2) := by
  obtain ⟨hloglo,hloghi⟩ := density_log_sum_bounds p h T hp hs
  have hinv := inverse_square_grid_sum p a h T ha hh hp hs
  have hln0 : Real.log (p 0) ≤ 0 := Real.log_nonpos (hp 0 (Nat.zero_le _)).le hp0
  have hlninit : -Real.log (p 0) ≤ (1-p 0)/p 0 := by
    have hi := Real.log_le_sub_one_of_pos (inv_pos.mpr (hp 0 (Nat.zero_le _)))
    rw [Real.log_inv] at hi
    have he : (p 0)⁻¹-1 = (1-p 0)/p 0 := by
      field_simp [ne_of_gt (hp 0 (Nat.zero_le _))]
    rwa [he] at hi
  have h₁ := mul_le_mul_of_nonneg_left hloghi hb
  have h₂ := mul_le_mul_of_nonneg_left hloglo (show 0 ≤ 2*b*η by positivity)
  have h₃ := mul_le_mul_of_nonneg_left hinv (sq_nonneg b)
  have h₄ := mul_le_mul_of_nonneg_left hlninit hb
  have h₅ := mul_nonpos_of_nonneg_of_nonpos (show 0 ≤ 2*b*η by positivity) hln0
  have hpzero := hp 0 (Nat.zero_le _)
  have h₆ : 0 ≤ b*h/p 0 := by positivity
  have h₇ : 0 ≤ b^2/(a*p 0^2) := by positivity
  have he : (∑ i ∈ Finset.range T, (-b*(h/p i)+2*b*η*(h/p i)+b^2*(2*h/(a*p i^3)))) =
      -b*(∑ i ∈ Finset.range T, h/p i)+2*b*η*(∑ i ∈ Finset.range T, h/p i)+
        b^2*(∑ i ∈ Finset.range T, 2*h/(a*p i^3)) := by
    simp only [Finset.sum_add_distrib,← Finset.mul_sum]
  rw [he]
  simp only [mul_sub,mul_add] at h₁ h₂ h₃
  simp only [div_eq_mul_inv] at h₁ h₂ h₃ h₄ h₆ h₇ ⊢
  nlinarith only [h₁,h₂,h₃,h₄,h₅,h₆,h₇]

end SharpTerminalLeave
end
end

end OAI
