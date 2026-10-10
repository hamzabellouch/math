import OAI.Analysis.CircleDomains.Topology.ComponentControl

namespace OAI

/-!
# The regularized metric energy in finite transfer

For the two eigenvalues of the positive semidefinite tensor formed by the
coordinate differentials, this is the energy density for the regularized
metric `A + τ g₀`. These estimates are the scalar analytic step in
the finite-transfer construction. In particular, rank-one fillings have
vanishing limiting energy.
-/

open Filter
open scoped Topology

namespace CircleDomainRigidity.FiniteTransfer

noncomputable section

/-- Sum of the two coordinate energy contributions in an eigenframe. -/
def metricEnergy (a b τ : ℝ) : ℝ :=
  a * Real.sqrt (b + τ) / Real.sqrt (a + τ) +
    b * Real.sqrt (a + τ) / Real.sqrt (b + τ)

/-- This is the density formula written in the manuscript. -/
theorem metricEnergy_eq_density {a b τ : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hτ : 0 < τ) :
    metricEnergy a b τ =
      (2 * a * b + τ * (a + b)) / Real.sqrt ((a + τ) * (b + τ)) := by
  have haτ : 0 < a + τ := add_pos_of_nonneg_of_pos ha hτ
  have hbτ : 0 < b + τ := add_pos_of_nonneg_of_pos hb hτ
  have hsa : Real.sqrt (a + τ) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 haτ)
  have hsb : Real.sqrt (b + τ) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hbτ)
  have hsa2 := Real.sq_sqrt haτ.le
  have hsb2 := Real.sq_sqrt hbτ.le
  rw [Real.sqrt_mul haτ.le]
  unfold metricEnergy
  field_simp
  nlinarith

/-- The regularized density has the original trace as a uniform bound.
This bound is independent of the positive regularization parameter. -/
theorem metricEnergy_le_trace {a b τ : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hτ : 0 < τ) :
    metricEnergy a b τ ≤ a + b := by
  rw [metricEnergy_eq_density ha hb hτ]
  have hp : 0 < (a + τ) * (b + τ) :=
    mul_pos (add_pos_of_nonneg_of_pos ha hτ) (add_pos_of_nonneg_of_pos hb hτ)
  have hd : 0 < Real.sqrt ((a + τ) * (b + τ)) := Real.sqrt_pos.2 hp
  apply (div_le_iff₀ hd).2
  have hn : 0 ≤ 2 * a * b + τ * (a + b) := by positivity
  apply (sq_le_sq₀ hn (mul_nonneg (add_nonneg ha hb) hd.le)).mp
  rw [mul_pow, Real.sq_sqrt hp.le]
  have hgap : 0 ≤ (a - b) ^ 2 * (a * b + τ * (a + b)) := by positivity
  nlinarith

private theorem tendsto_energy_term {a b : ℝ} (ha : 0 ≤ a) :
    Tendsto (fun τ : ℝ => a * Real.sqrt (b + τ) / Real.sqrt (a + τ)) (𝓝 0)
      (𝓝 (Real.sqrt a * Real.sqrt b)) := by
  by_cases ha0 : a = 0
  · subst a
    simp
  have hsa : Real.sqrt a ≠ 0 := Real.sqrt_ne_zero'.mpr (lt_of_le_of_ne ha (Ne.symm ha0))
  have hsqrt (c : ℝ) : Tendsto (fun τ : ℝ => Real.sqrt (c + τ)) (𝓝 0)
      (𝓝 (Real.sqrt c)) := by
    have hadd : Tendsto (fun τ : ℝ => c + τ) (𝓝 0) (𝓝 (c + 0)) :=
      tendsto_const_nhds.add tendsto_id
    simpa only [Function.comp_def, add_zero] using
      (Real.continuous_sqrt.tendsto (c + 0)).comp hadd
  have h : Tendsto (fun τ : ℝ => a * Real.sqrt (b + τ) / Real.sqrt (a + τ)) (𝓝 0)
      (𝓝 (a * Real.sqrt b / Real.sqrt a)) :=
    (tendsto_const_nhds.mul (hsqrt b)).div (hsqrt a) hsa
  have heq : a * Real.sqrt b / Real.sqrt a = Real.sqrt a * Real.sqrt b := by
    apply (div_eq_iff hsa).2
    have hsq := Real.sq_sqrt ha
    calc
      a * Real.sqrt b = Real.sqrt a ^ 2 * Real.sqrt b := by rw [hsq]
      _ = Real.sqrt a * Real.sqrt b * Real.sqrt a := by ring
  rwa [heq] at h

/-- The limiting energy is twice the square root of the determinant. -/
theorem tendsto_metricEnergy {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Tendsto (metricEnergy a b) (𝓝[>] 0) (𝓝 (2 * Real.sqrt (a * b))) := by
  have h := (tendsto_energy_term (b := b) ha).add (tendsto_energy_term (b := a) hb)
  have heq : Real.sqrt a * Real.sqrt b + Real.sqrt b * Real.sqrt a =
      2 * Real.sqrt (a * b) := by rw [Real.sqrt_mul ha]; ring
  rw [heq] at h
  exact h.mono_left nhdsWithin_le_nhds

/-- Rank-one tensors contribute zero in the regularized limit. -/
theorem tendsto_metricEnergy_rank_one {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hrank : a * b = 0) :
    Tendsto (metricEnergy a b) (𝓝[>] 0) (𝓝 0) := by
  simpa [hrank] using tendsto_metricEnergy ha hb

end

end CircleDomainRigidity.FiniteTransfer

end OAI
