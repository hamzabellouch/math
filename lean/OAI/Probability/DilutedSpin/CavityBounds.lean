import OAI.Probability.DilutedSpin.HierarchyBasic

namespace OAI

section
open _root_.MeasureTheory _root_.OAI.MeasureTheory Filter Set TopologicalSpace
open scoped Topology NNReal ENNReal BigOperators

namespace DilutedSpinGlass
@[simp] theorem q_pos (x : ℝ) (s : Spin) : 0 < q x s := by
  unfold q
  exact div_pos (Real.exp_pos _) (mul_pos (by norm_num) (Real.cosh_pos _))

@[simp] theorem q_sum (x : ℝ) : ∑ s : Spin, q x s = 1 := by
  rw [Fintype.sum_bool]
  simp only [q, spin, Bool.false_eq_true, ↓reduceIte, mul_one, mul_neg_one]
  rw [← add_div]
  rw [Real.cosh_eq]
  field_simp

/-- Product message probabilities have total mass exactly one. -/
theorem product_q_sum {p : ℕ} (x : Fin p → ℝ) :
    (∑ s : Fin p → Spin, ∏ l, q (x l) (s l)) = 1 := by
  rw [← Fintype.prod_sum]
  simp only [q_sum, Finset.prod_const_one]


/-- Uniform bounds on a finite probability-weighted exponential sum. -/
theorem weighted_exp_bounds {ι : Type*} [Fintype ι] (w f : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hs : ∑ i, w i = 1) {B : ℝ}
    (hf : ∀ i, |f i| ≤ B) :
    Real.exp (-B) ≤ ∑ i, w i * Real.exp (f i) ∧
      (∑ i, w i * Real.exp (f i)) ≤ Real.exp B := by
  have hlo : ∀ i, Real.exp (-B) ≤ Real.exp (f i) :=
    fun i => Real.exp_le_exp.mpr (abs_le.mp (hf i)).1
  have hhi : ∀ i, Real.exp (f i) ≤ Real.exp B :=
    fun i => Real.exp_le_exp.mpr (abs_le.mp (hf i)).2
  constructor
  · calc
      Real.exp (-B) = ∑ i, w i * Real.exp (-B) := by rw [← Finset.sum_mul, hs, one_mul]
      _ ≤ _ := Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hlo i) (hw i))
  · calc
      _ ≤ ∑ i, w i * Real.exp B :=
        Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hhi i) (hw i))
      _ = Real.exp B := by rw [← Finset.sum_mul, hs, one_mul]

theorem weighted_log_exp_bound {ι : Type*} [Fintype ι] (w f : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hs : ∑ i, w i = 1) {B : ℝ}
    (hf : ∀ i, |f i| ≤ B) :
    |Real.log (∑ i, w i * Real.exp (f i))| ≤ B := by
  obtain ⟨hlo, hhi⟩ := weighted_exp_bounds w f hw hs hf
  have hp := (Real.exp_pos _).trans_le hlo
  exact abs_le.mpr ⟨(Real.le_log_iff_exp_le hp).mpr hlo,
    (Real.log_le_iff_le_exp hp).mpr hhi⟩

theorem edge_pos {p : ℕ} (theta : Interaction p) (x : Fin p → ℝ) :
    0 < edge theta x := by
  have hb := (weighted_exp_bounds (B := ‖theta‖) (fun s : Fin p → Spin => ∏ l, q (x l) (s l)) theta
    (fun _ => (Finset.prod_pos (fun l _ => q_pos _ _)).le)
    (product_q_sum x) (fun s => norm_le_pi_norm theta s)).1
  simpa only [edge, mul_comm] using (Real.exp_pos _).trans_le hb

/-- The message-free uniform edge bound, with only the physical interaction norm. -/
theorem log_edge_bound {p : ℕ} (theta : Interaction p) (x : Fin p → ℝ) :
    |Real.log (edge theta x)| ≤ ‖theta‖ := by
  simpa only [edge, mul_comm] using
    weighted_log_exp_bound (B := ‖theta‖) (fun s : Fin p → Spin => ∏ l, q (x l) (s l)) theta
      (fun _ => (Finset.prod_pos (fun l _ => q_pos _ _)).le)
      (product_q_sum x) (fun s => norm_le_pi_norm theta s)

/-- The uniform cavity-message bound; no message moments occur. -/
theorem message_bound {p : ℕ} (theta : Interaction p)
    (x : Fin (p - 1) → ℝ) (ε : Spin) : |message theta x ε| ≤ ‖theta‖ := by
  simpa only [message, mul_comm] using
    weighted_log_exp_bound (B := ‖theta‖) (fun s : Fin (p-1) → Spin => ∏ l, q (x l) (s l))
      (fun s => theta (appendSpin s ε))
      (fun _ => (Finset.prod_pos (fun l _ => q_pos _ _)).le)
      (product_q_sum x) (fun s => norm_le_pi_norm theta (appendSpin s ε))

 
theorem siteLog_bound {p k : ℕ} (theta : Fin k → InteractionSample p)
    (h : ℝ) (x : (Fin k × Fin (p-1)) → ℝ) :
    |siteLog theta h x| ≤ |h| + ∑ j, ‖(theta j).1‖ := by
  have hf : ∀ ε : Spin,
      |h * spin ε + ∑ j, message (theta j).1 (fun l => x (j,l)) ε| ≤
        |h| + ∑ j, ‖(theta j).1‖ := by
    intro ε
    apply (abs_add_le _ _).trans
    apply add_le_add
    · simp only [abs_mul, abs_spin, mul_one, le_refl]
    · exact (Finset.abs_sum_le_sum_abs _ _).trans
        (Finset.sum_le_sum (fun j _ => message_bound _ _ _))
  have hw : (∑ _ε : Spin, (1/2 : ℝ)) = 1 := by norm_num [Fintype.sum_bool]
  have hb := weighted_log_exp_bound (fun _ε : Spin => (1/2 : ℝ))
    (fun ε => h * spin ε + ∑ j, message (theta j).1 (fun l => x (j,l)) ε)
    (fun _ => by norm_num) hw hf
  simpa only [siteLog, ← Finset.mul_sum, one_div, div_eq_mul_inv, one_mul, mul_comm] using hb

end DilutedSpinGlass

end

end OAI
