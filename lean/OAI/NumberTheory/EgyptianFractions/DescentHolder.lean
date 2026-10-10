import Mathlib

namespace OAI
open scoped BigOperators

namespace Problem337

/-- Finite Hölder with one factor equal to one, in the normalization used
for the exceptional set in the descent. -/
theorem sum_le_card_rpow_mul_moment
    {ι : Type*} (H : Finset ι) (f : ι → ℝ) (r : ℝ)
    (hr : 1 < r) (hf : ∀ i ∈ H, 0 ≤ f i) :
    (∑ i ∈ H, f i) ≤
      (H.card : ℝ) ^ (1 - 1 / r) * (∑ i ∈ H, f i ^ r) ^ (1 / r) := by
  have hpq := Real.HolderConjugate.conjExponent hr
  have hq : 1 / Real.conjExponent r = 1 - 1 / r := by
    have h := hpq.inv_add_inv_eq_one
    simp only [one_div] at *
    linarith
  have h := Real.inner_le_Lp_mul_Lq_of_nonneg H hpq.symm
    (f := fun _ => (1 : ℝ)) (g := f) (by intro i hi; norm_num) hf
  simpa only [one_mul, Real.one_rpow, Finset.sum_const, nsmul_eq_mul,
    mul_one, hq] using h

/-- Algebraic normalization of the Hölder moment bound. -/
theorem normalized_moment_factor
    (x Y E r : ℝ) (hx : 0 ≤ x) (hY : 0 < Y) :
    x ^ (1 - 1 / r) * (Y * Real.exp E) ^ (1 / r) =
      Y * Real.exp (E / r) * (x / Y) ^ (1 - 1 / r) := by
  rw [Real.mul_rpow hY.le (Real.exp_pos E).le, ← Real.exp_mul]
  rw [Real.div_rpow hx hY.le]
  have hpow : Y ^ (1 / r) = Y / Y ^ (1 - 1 / r) := by
    have he : 1 / r = 1 - (1 - 1 / r) := by ring
    conv_lhs => rw [he]
    rw [Real.rpow_sub hY, Real.rpow_one]
  rw [hpow]
  rw [div_eq_mul_inv E r]
  ring_nf

/-- A moment estimate on an ambient finite set controls its restriction to
an exceptional set, including the empty exceptional set. -/
theorem descent_holder_bound
    {ι : Type*} (I H : Finset ι) (f : ι → ℝ) (Y E r : ℝ)
    (hHI : H ⊆ I) (hf : ∀ i ∈ I, 0 ≤ f i) (hY : 0 < Y) (hr : 1 < r)
    (hmoment : (∑ i ∈ I, f i ^ r) ≤ Y * Real.exp E) :
    (∑ i ∈ H, f i) ≤
      Y * Real.exp (E / r) * ((H.card : ℝ) / Y) ^ (1 - 1 / r) := by
  have hfH : ∀ i ∈ H, 0 ≤ f i := fun i hi => hf i (hHI hi)
  have hsum0 : 0 ≤ ∑ i ∈ H, f i ^ r :=
    Finset.sum_nonneg (fun i hi => Real.rpow_nonneg (hfH i hi) r)
  have hsum : (∑ i ∈ H, f i ^ r) ≤ Y * Real.exp E := by
    apply le_trans _ hmoment
    exact Finset.sum_le_sum_of_subset_of_nonneg hHI
      (fun i hi _ => Real.rpow_nonneg (hf i hi) r)
  calc
    (∑ i ∈ H, f i) ≤
        (H.card : ℝ) ^ (1 - 1 / r) * (∑ i ∈ H, f i ^ r) ^ (1 / r) :=
      sum_le_card_rpow_mul_moment H f r hr hfH
    _ ≤ (H.card : ℝ) ^ (1 - 1 / r) * (Y * Real.exp E) ^ (1 / r) := by
      apply mul_le_mul_of_nonneg_left
      · exact Real.rpow_le_rpow hsum0 hsum (by positivity)
      · exact Real.rpow_nonneg (by positivity) _
    _ = Y * Real.exp (E / r) * ((H.card : ℝ) / Y) ^ (1 - 1 / r) :=
      normalized_moment_factor _ Y E r (by positivity) hY

/-- Summing the uniform restricted moment estimate over a finite indexed
family does not require that distinct indices have distinct values. -/
theorem indexed_descent_holder_bound
    {ι κ : Type*} (J : Finset ι) (I H : Finset κ) (f : ι → κ → ℝ)
    (Y E r : ℝ) (hHI : H ⊆ I) (hY : 0 < Y) (hr : 1 < r)
    (hf : ∀ j ∈ J, ∀ i ∈ I, 0 ≤ f j i)
    (hmoment : ∀ j ∈ J, (∑ i ∈ I, f j i ^ r) ≤ Y * Real.exp E) :
    (∑ j ∈ J, ∑ i ∈ H, f j i) ≤
      (J.card : ℝ) * (Y * Real.exp (E / r) *
        ((H.card : ℝ) / Y) ^ (1 - 1 / r)) := by
  calc
    (∑ j ∈ J, ∑ i ∈ H, f j i) ≤
        ∑ _j ∈ J, Y * Real.exp (E / r) * ((H.card : ℝ) / Y) ^ (1 - 1 / r) := by
      apply Finset.sum_le_sum
      intro j hj
      exact descent_holder_bound I H (f j) Y E r hHI (hf j hj) hY hr (hmoment j hj)
    _ = _ := by simp

/-- Normalization of the indexed predecessor count.  The factor `1 / ρ`
cancels because the next interval has length `Y = ρ X`. -/
theorem normalized_predecessor_bound
    (a B T X Y ρ ε E r J : ℝ) (hX : 0 < X) (hρ : 0 < ρ) (hJ : 0 < J)
    (hY : Y = ρ * X)
    (hpair : a ≤ X * ε + B + (2 / (ρ * J)) * T)
    (hsum : T ≤ J * (Y * Real.exp (E / r) * (B / Y) ^ (1 - 1 / r))) :
    a / X ≤ ε + ρ * (B / Y) + 2 * Real.exp (E / r) * (B / Y) ^ (1 - 1 / r) := by
  have hρJ : 0 ≤ 2 / (ρ * J) := by positivity
  have hbound : a ≤ X * ε + B + (2 / (ρ * J)) *
      (J * (Y * Real.exp (E / r) * (B / Y) ^ (1 - 1 / r))) := by
    apply hpair.trans
    exact add_le_add_right (mul_le_mul_of_nonneg_left hsum hρJ) (X * ε + B)
  apply (div_le_iff₀ hX).mpr
  apply le_trans hbound
  subst Y
  have hX0 := ne_of_gt hX
  have hρ0 := ne_of_gt hρ
  have hJ0 := ne_of_gt hJ
  apply le_of_eq
  field_simp

/-- The inherited exceptional proportion can be absorbed into the same
fractional power as the new predecessors. -/
theorem absorb_inherited_proportion
    (δ ε ρ E r : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hρ1 : ρ ≤ 1) (hr : 1 < r) :
    ε + ρ * δ + 2 * Real.exp (E / r) * δ ^ (1 - 1 / r) ≤
      ε + (1 + 2 * Real.exp (E / r)) * δ ^ (1 - 1 / r) := by
  have hβ : 0 ≤ 1 / r := by positivity
  have hδ : δ ≤ δ ^ (1 - 1 / r) :=
    Real.self_le_rpow_of_le_one hδ0 hδ1 (by linarith)
  have hρδ : ρ * δ ≤ δ := by nlinarith
  nlinarith

/-- A convenient exponential envelope for the coefficient in the normalized
recurrence, once the moment parameter is at least two. -/
theorem descent_coefficient_bound
    (E r : ℝ) (hE : 2 ≤ E) (hr : 1 ≤ r) :
    1 + 2 * Real.exp (E / r) ≤ Real.exp (2 * E) := by
  have hE0 : 0 ≤ E := by linarith
  have hsmall : Real.exp (E / r) ≤ Real.exp E :=
    Real.exp_le_exp.mpr (div_le_self hE0 hr)
  have hlarge : 3 ≤ Real.exp E := by
    have h := Real.add_one_le_exp E
    linarith
  have hproduct : 0 ≤ (Real.exp E - 3) * (Real.exp E + 1) :=
    mul_nonneg (by linarith) (by positivity)
  rw [show 2 * E = E + E by ring, Real.exp_add]
  nlinarith

/-- The exact one-step recurrence used by the exceptional-density
iteration. All moment and pair-count hypotheses remain explicit. -/
theorem descent_recurrence_of_pair_and_moment
    (a B T X Y ρ ε E r J : ℝ) (hX : 0 < X) (hρ : 0 < ρ)
    (hρ1 : ρ ≤ 1) (hJ : 0 < J) (hY : Y = ρ * X)
    (hB0 : 0 ≤ B) (hBY : B ≤ Y) (hE : 2 ≤ E) (hr : 1 < r)
    (hpair : a ≤ X * ε + B + (2 / (ρ * J)) * T)
    (hsum : T ≤ J * (Y * Real.exp (E / r) * (B / Y) ^ (1 - 1 / r))) :
    a / X ≤ ε + Real.exp (2 * E) * (B / Y) ^ (1 - 1 / r) := by
  have hY0 : 0 < Y := by rw [hY]; positivity
  have hδ0 : 0 ≤ B / Y := div_nonneg hB0 hY0.le
  have hδ1 : B / Y ≤ 1 := (div_le_one hY0).mpr hBY
  calc
    a / X ≤ ε + ρ * (B / Y) +
        2 * Real.exp (E / r) * (B / Y) ^ (1 - 1 / r) :=
      normalized_predecessor_bound a B T X Y ρ ε E r J hX hρ hJ hY hpair hsum
    _ ≤ ε + (1 + 2 * Real.exp (E / r)) * (B / Y) ^ (1 - 1 / r) :=
      absorb_inherited_proportion (B / Y) ε ρ E r hδ0 hδ1 hρ1 hr
    _ ≤ ε + Real.exp (2 * E) * (B / Y) ^ (1 - 1 / r) := by
      gcongr
      exact descent_coefficient_bound E r hE hr.le

end Problem337

end OAI
