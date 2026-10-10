import OAI.NumberTheory.Ostmann.Preliminaries.LocalUniformity

namespace OAI

open Erdos970

namespace Ostmann.Preliminaries
open scoped BigOperators

variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

noncomputable def collisionConstant (k : ℕ) : ℝ :=
  4 * (k + 1 : ℕ) + 4 * Real.log 2 + 6 * Real.log 4 + 16

theorem collisionConstant_pos (k : ℕ) : 0 < collisionConstant k := by
  have h2 := Real.log_nonneg (show (1 : ℝ) ≤ 2 by norm_num)
  have h4 := Real.log_nonneg (show (1 : ℝ) ≤ 4 by norm_num)
  unfold collisionConstant
  positivity

theorem collisionScale_le_sqrt (k X : ℕ) (hlog : 1 ≤ Real.log (X : ℝ)) :
    (collisionScale k X : ℝ) ≤ Real.sqrt X := by
  have hpow : 1 ≤ Real.log (X : ℝ) ^ (k + 1) := one_le_pow₀ hlog
  have hnonneg : 0 ≤ Real.sqrt X / Real.log (X : ℝ) ^ (k + 1) := by positivity
  exact (Nat.floor_le hnonneg).trans (div_le_self (Real.sqrt_nonneg _) hpow)

theorem collisionStability_le_loglog (d : Decomposition) (k X : ℕ)
    (hX : 0 < X) (hlog : 1 ≤ Real.log (X : ℝ))
    (hloglog : 1 ≤ Real.log (Real.log (X : ℝ)))
    (hscale : 2 ≤ Real.sqrt X / Real.log (X : ℝ) ^ (k + 1))
    (a : α → ℕ) (μ : α → ℝ) (b : β → ℕ) (ν : β → ℝ)
    (hai : Function.Injective a) (hbi : Function.Injective b)
    (haX : ∀ i, a i ≤ X) (hbX : ∀ i, b i ≤ X)
    (hμ0 : ∀ i, 0 ≤ μ i) (hν0 : ∀ i, 0 ≤ ν i)
    (hμ : ∑ i, μ i = 1) (hν : ∑ i, ν i = 1)
    (hA : ∀ i, μ i ≠ 0 → a i ∈ d.A) (hB : ∀ i, ν i ≠ 0 → b i ∈ d.B)
    (ha : ∀ i, μ i ≠ 0 → Real.sqrt X + d.cutoff < a i)
    (hb : ∀ i, ν i ≠ 0 → Real.sqrt X + d.cutoff < b i)
    (hμcap : ∀ i, μ i ≤ collisionMassCap k X)
    (hνcap : ∀ i, ν i ≤ collisionMassCap k X) :
    collisionStability d (collisionScale k X) a μ b ν ≤
      collisionConstant k * Real.log (Real.log (X : ℝ)) := by
  have hscale1 := (collisionScale_estimates k X hX hlog hscale).1
  have hQs := collisionScale_le_sqrt k X hlog
  have hAcut : ∀ i, μ i ≠ 0 → collisionScale k X + d.cutoff < a i := by
    intro i hi
    have hreal : (collisionScale k X : ℝ) + d.cutoff < a i := by linarith [ha i hi]
    exact_mod_cast hreal
  have hBcut : ∀ i, ν i ≠ 0 → collisionScale k X + d.cutoff < b i := by
    intro i hi
    have hreal : (collisionScale k X : ℝ) + d.cutoff < b i := by linarith [hb i hi]
    exact_mod_cast hreal
  have hbound := collisionStability_le d (collisionScale k X) X hscale1 hX
    a μ b ν hai hbi haX hbX hμ0 hν0 hμ hν hA hB hAcut hBcut hμcap hνcap
  have hscaleBound := collisionScale_error_le k X hX hlog hscale
  have hc : 0 ≤ 4 * Real.log 2 + 6 * Real.log 4 + 16 := by
    have h2 := Real.log_nonneg (show (1 : ℝ) ≤ 2 by norm_num)
    have h4 := Real.log_nonneg (show (1 : ℝ) ≤ 4 by norm_num)
    positivity
  apply (hbound.trans hscaleBound).trans
  unfold collisionConstant
  nlinarith [mul_le_mul_of_nonneg_left hloglog hc]

theorem eventually_collision_bound_conditions (k : ℕ) :
    ∀ᶠ X : ℕ in Filter.atTop, 0 < X ∧ 1 ≤ Real.log (X : ℝ) ∧
      1 ≤ Real.log (Real.log (X : ℝ)) ∧
      2 ≤ Real.sqrt X / Real.log (X : ℝ) ^ (k + 1) := by
  have ht := Real.tendsto_log_atTop.comp
    (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ)))
  filter_upwards [eventually_collisionScale_conditions k, ht.eventually_ge_atTop 1] with X h hll
  exact ⟨h.1, h.2.1, hll, h.2.2⟩

end Ostmann.Preliminaries

end OAI
