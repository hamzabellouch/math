import OAI.NumberTheory.PiExponent.Polynomials.SimplexRational

namespace OAI

open Filter Topology
open scoped BigOperators

namespace PiExponent

theorem tendsto_log_div_of_normalized_pow {f : ℝ → ℝ} {d : ℕ} {L : ℝ}
    (hf : Tendsto (fun H : ℝ => f H / H ^ d) atTop (𝓝 L)) (hL : 0 < L) :
    Tendsto (fun H : ℝ => Real.log (f H) / H) atTop (𝓝 0) := by
  have hlog : Tendsto (fun H : ℝ => Real.log (f H / H ^ d)) atTop (𝓝 (Real.log L)) :=
    (Real.continuousAt_log hL.ne').tendsto.comp hf
  have hslow : Tendsto (fun H : ℝ => Real.log H / H) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have h := (hlog.div_atTop tendsto_id).add (hslow.const_mul (d : ℝ))
  simp only [mul_zero, add_zero] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ),
    hf.eventually (eventually_ne_nhds hL.ne')] with H hH hn
  have hfne : f H ≠ 0 := by
    intro hz
    apply hn
    simp [hz]
  rw [Real.log_div hfne (pow_ne_zero _ hH.ne'), Real.log_pow]
  simp only [id_eq]
  ring

theorem tendsto_log_add_div_of_normalized_pow {f : ℝ → ℝ} {d : ℕ} {L : ℝ}
    (hf : Tendsto (fun H : ℝ => f H / H ^ d) atTop (𝓝 L)) (hL : 0 < L) (C : ℝ) :
    Tendsto (fun H : ℝ => (Real.log (f H) + C) / H) atTop (𝓝 0) := by
  have h := (tendsto_log_div_of_normalized_pow hf hL).add
    (tendsto_id.const_div_atTop C)
  simpa only [add_zero, add_div, id_eq] using h

theorem tendsto_log_card_realWeightedSimplex_div_rational {d : ℕ}
    (ρ : Fin d → ℚ) (hρ : ∀ i, 0 < ρ i) :
    Tendsto (fun H : ℝ =>
      Real.log ((realWeightedSimplex (fun i => (ρ i : ℝ)) H).card : ℝ) / H)
      atTop (𝓝 0) := by
  apply tendsto_log_div_of_normalized_pow (tendsto_card_realWeightedSimplex_rational ρ hρ)
  apply div_pos zero_lt_one
  apply mul_pos (by exact_mod_cast Nat.factorial_pos d)
  exact Finset.prod_pos (fun i _ => by exact_mod_cast hρ i)

theorem tendsto_log_card_strictWeightedSimplex_div_rational {d : ℕ}
    (ρ : Fin d → ℚ) (hρ : ∀ i, 0 < ρ i) :
    Tendsto (fun H : ℝ =>
      Real.log ((strictWeightedSimplex (fun i => (ρ i : ℝ)) H).card : ℝ) / H)
      atTop (𝓝 0) := by
  apply tendsto_log_div_of_normalized_pow (tendsto_card_strictWeightedSimplex_rational ρ hρ)
  apply div_pos zero_lt_one
  apply mul_pos (by exact_mod_cast Nat.factorial_pos d)
  exact Finset.prod_pos (fun i _ => by exact_mod_cast hρ i)

end PiExponent

end OAI
