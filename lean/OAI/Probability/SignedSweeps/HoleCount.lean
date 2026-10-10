import OAI.Probability.SignedSweeps.FallingFactorials

namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module

def holeBudget {s m l : ℕ} (τ : ℝ) (z : Fin l → Fin s × Fin m) : ℝ :=
  (∑ j : Fin m, clippedBudget τ s (occupancy (fun i => (z i).2) j).val) +
    ∑ j : Fin s, clippedBudget τ m (occupancy (fun i => (z i).1) j).val

def holeClippingError (κ : ℝ) (s m : ℕ) : ℝ :=
  (m : ℝ) * (s : ℝ) ^ (1 - κ) * Real.log s +
    (s : ℝ) * (m : ℝ) ^ (1 - κ) * Real.log m

def holeTraceSum (τ : ℝ) (s m l : ℕ) : ℝ :=
  ∑ z : HolePlacement s m l, holePrefactor z * Real.exp (holeBudget τ z.1)

lemma holeTraceSum_nonneg (τ : ℝ) (s m l : ℕ) : 0 ≤ holeTraceSum τ s m l := by
  apply Finset.sum_nonneg
  intro z hz
  unfold holePrefactor
  positivity

lemma holeTraceSum_bound {κ τ : ℝ} (hκ : 0 ≤ κ) (hκτ : κ ≤ τ)
    {s m l : ℕ} (hs : 0 < s) (hm : 0 < m) :
    holeTraceSum τ s m l ≤ Real.exp
      (τ * l * Real.log ((s * m : ℕ) : ℝ) -
        2 * (l : ℝ) * Real.log (((s * m : ℕ) : ℝ) / l) + 4 * l +
        holeClippingError κ s m + (s + m : ℝ) * Real.log (l + 1)) := by
  classical
  let A := 4 * (l : ℝ) + τ * l * Real.log ((s * m : ℕ) : ℝ) + holeClippingError κ s m
  have hz (z : HolePlacement s m l) :
      holePrefactor z * Real.exp (holeBudget τ z.1) ≤
        Real.exp A * ((((s * m : ℕ) : ℝ) ^ l)⁻¹ * Real.exp (-holeLineEntropy z.1)) := by
    have hb : holeBudget τ z.1 ≤
        τ * l * Real.log ((s * m : ℕ) : ℝ) - holeLineEntropy z.1 + holeClippingError κ s m := by
      simpa only [holeBudget, holeClippingError, add_assoc] using line_budgets_le hκ hκτ hs hm z.1
    calc
      _ ≤ ((((s * m : ℕ) : ℝ) ^ l)⁻¹ * Real.exp (4 * (l : ℝ))) *
          Real.exp (τ * l * Real.log ((s * m : ℕ) : ℝ) - holeLineEntropy z.1 +
            holeClippingError κ s m) :=
        mul_le_mul (holePrefactor_bound hs hm z) (Real.exp_le_exp.mpr hb)
          (Real.exp_pos _).le (by positivity)
      _ = _ := by
        simp only [A, Real.exp_add, Real.exp_sub, Real.exp_neg]
        ring
  calc
    _ ≤ ∑ z : HolePlacement s m l,
        Real.exp A * ((((s * m : ℕ) : ℝ) ^ l)⁻¹ * Real.exp (-holeLineEntropy z.1)) :=
      Finset.sum_le_sum (fun z _ => hz z)
    _ = Real.exp A * ((((s * m : ℕ) : ℝ) ^ l)⁻¹ *
        ∑ z : HolePlacement s m l, Real.exp (-holeLineEntropy z.1)) := by
      rw [← Finset.mul_sum, ← Finset.mul_sum]
    _ ≤ Real.exp A * Real.exp (-2 * (l : ℝ) * Real.log (((s * m : ℕ) : ℝ) / l) +
        (s + m : ℝ) * Real.log (l + 1)) :=
      mul_le_mul_of_nonneg_left (hole_assignment_entropy_bound_exp hs hm) (Real.exp_pos _).le
    _ = _ := by
      rw [← Real.exp_add]
      congr 1
      dsimp [A]
      ring

lemma choose_exp_bound {n l : ℕ} (hn : 0 < n) :
    (n.choose l : ℝ) ≤ Real.exp ((l : ℝ) * (Real.log ((n : ℝ) / l) + 1)) := by
  by_cases hl : l = 0
  · subst l; simp
  have hlp : (0 : ℝ) < l := by exact_mod_cast Nat.pos_of_ne_zero hl
  have hnp : (0 : ℝ) < n := by exact_mod_cast hn
  have h₁ : (l : ℝ) ^ l / (l.factorial : ℝ) ≤ Real.exp l :=
    Real.pow_div_factorial_le_exp (l : ℝ) hlp.le l
  calc
    _ ≤ (n : ℝ) ^ l / (l.factorial : ℝ) := Nat.choose_le_pow_div l n
    _ = ((n : ℝ) / l) ^ l * ((l : ℝ) ^ l / (l.factorial : ℝ)) := by
      rw [div_pow]
      field_simp
    _ ≤ ((n : ℝ) / l) ^ l * Real.exp l :=
      mul_le_mul_of_nonneg_left h₁ (by positivity)
    _ = _ := by
      rw [show (l : ℝ) * (Real.log ((n : ℝ) / l) + 1) =
        (l : ℝ) * Real.log ((n : ℝ) / l) + l by ring,
        Real.exp_add, Real.exp_nat_mul, Real.exp_log (div_pos hnp hlp)]

lemma holeTraceSum_choose_bound {κ τ : ℝ} (hκ : 0 ≤ κ) (hκτ : κ ≤ τ)
    {s m l : ℕ} (hs : 0 < s) (hm : 0 < m) :
    ((s * m).choose l : ℝ) * holeTraceSum τ s m l ≤ Real.exp
      (τ * l * Real.log ((s * m : ℕ) : ℝ) -
        (l : ℝ) * Real.log (((s * m : ℕ) : ℝ) / l) + 5 * l +
        holeClippingError κ s m + (s + m : ℝ) * Real.log (l + 1)) := by
  refine (mul_le_mul (choose_exp_bound (Nat.mul_pos hs hm))
    (holeTraceSum_bound hκ hκτ hs hm) (holeTraceSum_nonneg τ s m l) (Real.exp_pos _).le).trans_eq ?_
  rw [← Real.exp_add]
  congr 1
  ring

end SignedSweeps
end

end OAI
