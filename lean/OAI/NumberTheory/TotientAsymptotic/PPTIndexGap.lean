import OAI.NumberTheory.TotientAsymptotic.PPTCoordinateAlignment
import OAI.NumberTheory.TotientAsymptotic.Phase

namespace OAI

/-!
The local normality error is smaller than every fixed fraction of the
two-thirds-power cutoff height.  This gives both the right-index
existence gap and the separation needed for the right-tail smoothness
argument, with no normality transfer between different cutoffs.
-/

noncomputable section
open scoped Topology
open Filter

namespace TotientAsymptotic

theorem ppt_local_normality_interval_budget {A η : ℝ} (_hA : 0 < A) (hη : 0 < η) :
    ∀ᶠ t : ℝ in atTop, ∀ (H J : ℕ) (s X : ℝ),
      1 ≤ H → J ≤ H → (H : ℝ) ≤ A*Real.log t →
      0 ≤ s → s ≤ (H : ℝ)^4 → 0 ≤ X → X ≤ t →
      (2*(J : ℝ)+1)*Real.sqrt (s*X)+s < η*t^(2/3 : ℝ) := by
  have h₃ : Tendsto (fun t : ℝ => (Real.log t)^3/t^(1/6 : ℝ)) atTop (𝓝 0) := by
    simpa only [Real.rpow_natCast] using
      (isLittleO_log_rpow_rpow_atTop (3 : ℕ)
        (by norm_num : (0 : ℝ) < 1/6)).tendsto_div_nhds_zero
  have h₄ : Tendsto (fun t : ℝ => (Real.log t)^4/t^(2/3 : ℝ)) atTop (𝓝 0) := by
    simpa only [Real.rpow_natCast] using
      (isLittleO_log_rpow_rpow_atTop (4 : ℕ)
        (by norm_num : (0 : ℝ) < 2/3)).tendsto_div_nhds_zero
  have hsum : Tendsto (fun t : ℝ =>
      3*A^3*((Real.log t)^3/t^(1/6 : ℝ))+A^4*((Real.log t)^4/t^(2/3 : ℝ)))
      atTop (𝓝 0) := by
    simpa only [mul_zero, zero_add] using (h₃.const_mul (3*A^3)).add (h₄.const_mul (A^4))
  filter_upwards [hsum.eventually (eventually_lt_nhds hη),
    eventually_gt_atTop (0 : ℝ)] with t hbudget ht
  intro H J s X hH hJ hdim hs0 hs hX0 hX
  have hH0 : (0 : ℝ) ≤ H := Nat.cast_nonneg H
  have hHr : (1 : ℝ) ≤ H := by exact_mod_cast hH
  have hJr : (J : ℝ) ≤ H := by exact_mod_cast hJ
  have ht23 : 0 < t^(2/3 : ℝ) := Real.rpow_pos_of_pos ht _
  have hsqrt : 0 ≤ Real.sqrt t := Real.sqrt_nonneg t
  have hroot : Real.sqrt (s*X) ≤ (H : ℝ)^2*Real.sqrt t := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    calc
      s*X ≤ (H : ℝ)^4*t := mul_le_mul hs hX hX0 (by positivity)
      _ = ((H : ℝ)^2*Real.sqrt t)^2 := by
        rw [mul_pow, Real.sq_sqrt ht.le]
        ring
  have hleft : (2*(J : ℝ)+1)*Real.sqrt (s*X) ≤ 3*(H : ℝ)^3*Real.sqrt t := by
    calc
      _ ≤ (2*(J : ℝ)+1)*((H : ℝ)^2*Real.sqrt t) :=
        mul_le_mul_of_nonneg_left hroot (by positivity)
      _ ≤ (3*(H : ℝ))*((H : ℝ)^2*Real.sqrt t) :=
        mul_le_mul_of_nonneg_right (by linarith only [hJr, hHr]) (by positivity)
      _ = _ := by ring
  have hH3 := pow_le_pow_left₀ hH0 hdim 3
  have hH4 := pow_le_pow_left₀ hH0 hdim 4
  have hscale : 3*(H : ℝ)^3*Real.sqrt t+(H : ℝ)^4 ≤
      3*(A*Real.log t)^3*Real.sqrt t+(A*Real.log t)^4 := by
    exact add_le_add (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hH3 (by norm_num)) hsqrt) hH4
  have hratio : Real.sqrt t/t^(2/3 : ℝ) = 1/t^(1/6 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_sub ht,
      show (1/2 : ℝ)-(2/3 : ℝ) = -(1/6 : ℝ) by norm_num,
      Real.rpow_neg ht.le]
    simp only [one_div]
  have he : (3*(A*Real.log t)^3*Real.sqrt t+(A*Real.log t)^4)/t^(2/3 : ℝ) =
      3*A^3*((Real.log t)^3/t^(1/6 : ℝ))+A^4*((Real.log t)^4/t^(2/3 : ℝ)) := by
    rw [add_div, mul_div_assoc, hratio]
    ring
  have htop : 3*(A*Real.log t)^3*Real.sqrt t+(A*Real.log t)^4 < η*t^(2/3 : ℝ) := by
    apply (div_lt_iff₀ ht23).mp
    rwa [he]
  linarith only [hleft, hs, hscale, htop]

/-- This is the strict gap required by `ppt_ordered_right_index` when a
retained left coordinate has height at least `t^(2/3)`. -/
theorem ppt_local_right_index_gap {A : ℝ} (hA : 0 < A) :
    ∀ᶠ z : ℝ in atTop, ∀ (H J : ℕ) (S T : ℝ),
      1 ≤ H → J ≤ H → (H : ℝ) ≤ A*Real.log (B z) →
      0 ≤ B S → B S ≤ (H : ℝ)^4 →
      (B z)^(2/3 : ℝ) ≤ B T → B T ≤ B z →
      (2*(J : ℝ)+1)*Real.sqrt (B S*B T) < B T-B S := by
  filter_upwards [B_tendsto.eventually
    (ppt_local_normality_interval_budget hA (by norm_num : (0 : ℝ) < 1)),
    B_tendsto.eventually (eventually_gt_atTop (0 : ℝ))] with z hbudget hB
  intro H J S T hH hJ hdim hBS0 hBS hTlow hTup
  have hT0 : 0 ≤ B T := (Real.rpow_pos_of_pos hB (2/3 : ℝ)).le.trans hTlow
  have hh := hbudget H J (B S) (B T) hH hJ hdim hBS0 hBS hT0 hTup
  linarith only [hh, hTlow]

/-- A fixed positive gap between two terminal cutoff heights dominates
the same normality error used in the right-tail smoothing argument. -/
theorem ppt_local_right_tail_gap {A η : ℝ} (hA : 0 < A) (hη : 0 < η) :
    ∀ᶠ z : ℝ in atTop, ∀ (H J : ℕ) (S U V : ℝ),
      1 ≤ H → J ≤ H → (H : ℝ) ≤ A*Real.log (B z) →
      0 ≤ B S → B S ≤ (H : ℝ)^4 →
      η*(B z)^(2/3 : ℝ) ≤ B V-B U →
      (2*(J : ℝ)+1)*Real.sqrt (B S*B z) < B V-B U := by
  filter_upwards [B_tendsto.eventually (ppt_local_normality_interval_budget hA hη),
    B_tendsto.eventually (eventually_gt_atTop (0 : ℝ))] with z hbudget hB
  intro H J S U V hH hJ hdim hBS0 hBS hgap
  have hh := hbudget H J (B S) (B z) hH hJ hdim hBS0 hBS hB.le le_rfl
  linarith only [hh, hgap, hBS0]

end TotientAsymptotic

end

end OAI
