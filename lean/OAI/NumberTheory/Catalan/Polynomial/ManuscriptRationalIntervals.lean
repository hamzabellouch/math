import OAI.NumberTheory.Catalan.Energy.BarrierLogRatConstants

namespace OAI

namespace InternalCatalan

def manuscriptIntervalAdd (a b : ℚ × ℚ) : ℚ × ℚ :=
  (a.1 + b.1, a.2 + b.2)

def manuscriptIntervalScale (c : ℚ) (a : ℚ × ℚ) : ℚ × ℚ :=
  if 0 ≤ c then (c * a.1, c * a.2) else (c * a.2, c * a.1)

theorem manuscript_interval_add {a b : ℚ × ℚ} {x y : ℝ}
    (hx : x ∈ Set.Icc (a.1 : ℝ) (a.2 : ℝ))
    (hy : y ∈ Set.Icc (b.1 : ℝ) (b.2 : ℝ)) :
    x + y ∈ Set.Icc ((manuscriptIntervalAdd a b).1 : ℝ)
      ((manuscriptIntervalAdd a b).2 : ℝ) := by
  change ((a.1 + b.1 : ℚ) : ℝ) ≤ x + y ∧ x + y ≤ ((a.2 + b.2 : ℚ) : ℝ)
  push_cast
  exact ⟨add_le_add hx.1 hy.1, add_le_add hx.2 hy.2⟩

theorem manuscript_interval_scale (c : ℚ) {a : ℚ × ℚ} {x : ℝ}
    (hx : x ∈ Set.Icc (a.1 : ℝ) (a.2 : ℝ)) :
    (c : ℝ) * x ∈ Set.Icc ((manuscriptIntervalScale c a).1 : ℝ)
      ((manuscriptIntervalScale c a).2 : ℝ) := by
  by_cases hc : 0 ≤ c
  · rw [manuscriptIntervalScale, ite_eq_left hc]
    change ((c * a.1 : ℚ) : ℝ) ≤ (c : ℝ) * x ∧
      (c : ℝ) * x ≤ ((c * a.2 : ℚ) : ℝ)
    push_cast
    have hc' : (0 : ℝ) ≤ (c : ℝ) := by exact_mod_cast hc
    exact ⟨mul_le_mul_of_nonneg_left hx.1 hc', mul_le_mul_of_nonneg_left hx.2 hc'⟩
  · rw [manuscriptIntervalScale, ite_eq_right hc]
    change ((c * a.2 : ℚ) : ℝ) ≤ (c : ℝ) * x ∧
      (c : ℝ) * x ≤ ((c * a.1 : ℚ) : ℝ)
    push_cast
    have hc' : (c : ℝ) ≤ 0 := by exact_mod_cast (le_of_lt (lt_of_not_ge hc))
    exact ⟨mul_le_mul_of_nonpos_left hx.2 hc', mul_le_mul_of_nonpos_left hx.1 hc'⟩

def manuscriptIntervalSum (xs : List (ℚ × ℚ)) : ℚ × ℚ :=
  ((xs.map Prod.fst).sum, (xs.map Prod.snd).sum)

theorem manuscript_interval_sum {ι : Type*} (xs : List ι)
    (iv : ι → ℚ × ℚ) (f : ι → ℝ)
    (h : ∀ a ∈ xs, f a ∈ Set.Icc ((iv a).1 : ℝ) ((iv a).2 : ℝ)) :
    (xs.map f).sum ∈ Set.Icc ((manuscriptIntervalSum (xs.map iv)).1 : ℝ)
      ((manuscriptIntervalSum (xs.map iv)).2 : ℝ) := by
  induction xs with
  | nil => simp [manuscriptIntervalSum]
  | cons a xs ih =>
    have ha := h a (by simp)
    have ht := ih (fun b hb => h b (by simp [hb]))
    simpa [manuscriptIntervalAdd, manuscriptIntervalSum] using manuscript_interval_add ha ht

end InternalCatalan

end OAI
