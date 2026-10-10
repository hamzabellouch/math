import OAI.GroupTheory.PolycyclicRecognition.Geometry.NilpotentFlow
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

namespace OAI

/-! # Exponential slack survives polynomial nilpotent conjugation

Choosing the chart margin larger than the nilpotence degree times the
expanded-box exponent allows an operator-norm argument for interior slack.
-/

noncomputable section

namespace PolycyclicRecognition

open Filter
open scoped Topology

/-- A uniformly nilpotent operator can grow exponentially more slowly than
its input contracts. Its exponential still sends that input to zero. -/
theorem nilpotent_exp_apply_tendsto_zero_of_exponent_gap
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V] [Nontrivial V]
    (N : ℝ → V →L[ℝ] V) (v : ℝ → V) {m : ℕ}
    (hnil : ∀ r, (N r) ^ (m + 1) = 0)
    {A B α β : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hα : 0 ≤ α)
    (hgap : (m : ℝ) * α < β)
    (hN : ∀ᶠ r : ℝ in atTop, ‖N r‖ ≤ A * Real.exp (α * r))
    (hv : ∀ᶠ r : ℝ in atTop, ‖v r‖ ≤ B * Real.exp (-β * r)) :
    Tendsto (fun r => NormedSpace.exp (N r) (v r)) atTop (𝓝 0) := by
  let C := ((m : ℝ) + 1) * (1 + A) ^ m * 2 ^ m * B
  have hC : 0 ≤ C := by positivity
  have hbound (r : ℝ) (hr : 0 ≤ r)
      (hNr : ‖N r‖ ≤ A * Real.exp (α * r))
      (hvr : ‖v r‖ ≤ B * Real.exp (-β * r)) :
      ‖NormedSpace.exp (N r) (v r)‖ ≤ C * Real.exp (((m : ℝ) * α - β) * r) := by
    have hexp : 1 ≤ Real.exp (α * r) := Real.one_le_exp (mul_nonneg hα hr)
    have hbase : 1 + ‖N r‖ ≤ (1 + A) * Real.exp (α * r) := by
      nlinarith [hNr]
    have he := norm_exp_smul_nilpotent_le (N r) (hnil r) (t := 1) zero_le_one
    simp only [one_smul, one_add_one_eq_two] at he
    calc
      _ ≤ ‖NormedSpace.exp (N r)‖ * ‖v r‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ (((m : ℝ) + 1) * (1 + ‖N r‖) ^ m * 2 ^ m) *
          (B * Real.exp (-β * r)) := mul_le_mul he hvr (norm_nonneg _) (by positivity)
      _ ≤ (((m : ℝ) + 1) * ((1 + A) * Real.exp (α * r)) ^ m * 2 ^ m) *
          (B * Real.exp (-β * r)) := by gcongr
      _ = _ := by
        rw [mul_pow, ← Real.exp_nat_mul]
        calc
          _ = C * (Real.exp ((m : ℝ) * (α * r)) * Real.exp (-β * r)) := by dsimp [C]; ring
          _ = _ := by rw [← Real.exp_add]; congr 2; ring
  have hlim : Tendsto (fun r : ℝ => C * Real.exp (((m : ℝ) * α - β) * r)) atTop (𝓝 0) := by
    have ht : Tendsto (fun r : ℝ => ((m : ℝ) * α - β) * r) atTop atBot :=
      (tendsto_const_mul_atBot_of_neg (sub_neg.mpr hgap)).mpr tendsto_id
    simpa using tendsto_const_nhds.mul (Real.tendsto_exp_atBot.comp ht)
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (Filter.Eventually.of_forall (fun _ => norm_nonneg _)) _ hlim
  filter_upwards [eventually_ge_atTop (0 : ℝ), hN, hv] with r hr hNr hvr
  exact hbound r hr hNr hvr

/-- The same exponential gap absorbs a common subexponential envelope in
both the conjugating operator and the translated vector. -/
theorem nilpotent_exp_apply_tendsto_zero_of_subexponential_bounds
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V] [Nontrivial V]
    (N : ℝ → V →L[ℝ] V) (v : ℝ → V) {m : ℕ}
    (hnil : ∀ r, (N r) ^ (m + 1) = 0)
    {A B α β : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hα : 0 ≤ α)
    (hgap : (m : ℝ) * α < β)
    (ε : ℝ → ℝ) (hε : Tendsto ε atTop (𝓝 0))
    (hN : ∀ᶠ r : ℝ in atTop, ‖N r‖ ≤ A * Real.exp ((α + ε r) * r))
    (hv : ∀ᶠ r : ℝ in atTop, ‖v r‖ ≤ B * Real.exp ((-β + ε r) * r)) :
    Tendsto (fun r => NormedSpace.exp (N r) (v r)) atTop (𝓝 0) := by
  let δ := (β - (m : ℝ) * α) / (2 * ((m : ℝ) + 1))
  have hδ : 0 < δ := div_pos (sub_pos.mpr hgap) (by positivity)
  have hδε : ∀ᶠ r : ℝ in atTop, ε r < δ := hε.eventually (eventually_lt_nhds hδ)
  have hδeq : δ * (2 * ((m : ℝ) + 1)) = β - (m : ℝ) * α := by
    dsimp [δ]
    field_simp
  have hgap' : (m : ℝ) * (α + δ) < β - δ := by nlinarith
  apply nilpotent_exp_apply_tendsto_zero_of_exponent_gap N v hnil hA hB
    (by positivity : 0 ≤ α + δ) hgap'
  · filter_upwards [hN, hδε, eventually_ge_atTop (0 : ℝ)] with r hr he hr0
    exact hr.trans (mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (by nlinarith)) hA)
  · filter_upwards [hv, hδε, eventually_ge_atTop (0 : ℝ)] with r hr he hr0
    exact hr.trans (mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (by nlinarith)) hB)

end PolycyclicRecognition

end

end OAI
