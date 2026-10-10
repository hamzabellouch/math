import OAI.NumberTheory.Ostmann.Preliminaries.Counting

namespace OAI

namespace Ostmann.Preliminaries
open Filter
attribute [local instance] Classical.propDecidable

theorem countUpTo_eq_natCount (A : Set ℕ) (X : ℕ) :
    countUpTo A X = Nat.count (fun n => n ∈ A) (X + 1) := by
  classical
  rw [Nat.count_eq_card_filter_range]
  rfl

theorem countUpTo_mono (A : Set ℕ) : Monotone (countUpTo A) := by
  intro X Y hXY
  apply Finset.card_le_card
  intro n hn
  obtain ⟨hA, hnX⟩ := mem_elementsUpTo.mp hn
  exact mem_elementsUpTo.mpr ⟨hA, hnX.trans hXY⟩

noncomputable def nthElement (A : Set ℕ) (n : ℕ) : ℕ := Nat.nth (fun a => a ∈ A) n

theorem nthElement_mem (A : Set ℕ) (hA : A.Infinite) (n : ℕ) : nthElement A n ∈ A :=
  Nat.nth_mem_of_infinite hA n

theorem countUpTo_nthElement (A : Set ℕ) (hA : A.Infinite) (n : ℕ) :
    countUpTo A (nthElement A n) = n + 1 := by
  classical
  rw [countUpTo_eq_natCount]
  exact Nat.count_nth_succ_of_infinite (p := fun n => n ∈ A) hA n

theorem nthElement_ge (A : Set ℕ) (hA : A.Infinite) (n : ℕ) : n ≤ nthElement A n :=
  Nat.le_nth (fun hfinite => (hA hfinite).elim)

theorem nthElement_tendsto (A : Set ℕ) (hA : A.Infinite) :
    Tendsto (nthElement A) atTop atTop :=
  tendsto_atTop_mono (nthElement_ge A hA) tendsto_id

theorem countUpTo_tendsto (A : Set ℕ) (hA : A.Infinite) :
    Tendsto (countUpTo A) atTop atTop := by
  apply tendsto_atTop.2
  intro n
  filter_upwards [eventually_ge_atTop (nthElement A n)] with X hX
  have h := countUpTo_mono A hX
  rw [countUpTo_nthElement A hA n] at h
  omega

theorem eventual_polylog_lower_of_upper (d : Decomposition) (j : ℕ) {C : ℝ}
    (hC : 0 < C)
    (hupper : ∀ᶠ X : ℕ in atTop,
      (countUpTo d.B X : ℝ) ≤ C * X / Real.log (X : ℝ) ^ (j + 1)) :
    ∀ᶠ X : ℕ in atTop,
      (Real.log 2 / (2 * C)) * Real.log (X : ℝ) ^ j ≤ countUpTo d.A X := by
  filter_upwards [eventually_count_product_lower d, hupper, eventually_ge_atTop 2] with X hprod hupper hX
  have hxr : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  have hl : 0 < Real.log (X : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < X by omega))
  have hA : (0 : ℝ) ≤ countUpTo d.A X := by positivity
  have hcombined := hprod.trans (mul_le_mul_of_nonneg_left hupper hA)
  have hpow : 0 < Real.log (X : ℝ) ^ (j + 1) := pow_pos hl _
  have hcombined' : (Real.log 2 / 2) * (X : ℝ) / Real.log (X : ℝ) ≤
      ((countUpTo d.A X : ℝ) * C * X) / Real.log (X : ℝ) ^ (j + 1) := by
    simpa only [mul_div_assoc, mul_assoc] using hcombined
  have hcross := (div_le_div_iff₀ hl hpow).mp hcombined'
  rw [pow_succ] at hcross
  have hc : (Real.log 2 / 2) * (X : ℝ) * Real.log (X : ℝ) ^ j ≤
      (countUpTo d.A X : ℝ) * C * X := by
    apply (mul_le_mul_iff_right₀ hl).mp
    nlinarith [hcross]
  have hc' : (Real.log 2 / 2) * Real.log (X : ℝ) ^ j ≤
      (countUpTo d.A X : ℝ) * C := by
    apply (mul_le_mul_iff_right₀ hxr).mp
    nlinarith [hc]
  have hid : (Real.log 2 / (2 * C)) * Real.log (X : ℝ) ^ j =
      ((Real.log 2 / 2) * Real.log (X : ℝ) ^ j) / C := by ring
  rw [hid]
  exact (div_le_iff₀ hC).mpr hc'

end Ostmann.Preliminaries

end OAI
