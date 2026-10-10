import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

namespace OAI

/-!
# Replacing divisibility counts by reciprocal products

Replacing `floor(N/d)/N` by `1/d` over admissible prime tuples has an
explicit finite error. This error tends to zero when the number of tuples
is `o(N)`.
-/

namespace JointDickman

open Filter
open scoped Topology

theorem normalized_division_error {N d : ℕ} (hN : 0 < N) (hd : 0 < d) :
    |((N / d : ℕ) : ℝ) / N - 1 / (d : ℝ)| ≤ 1 / (N : ℝ) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hmod : ((N % d : ℕ) : ℝ) + (d : ℝ) * (N / d : ℕ) = N := by
    exact_mod_cast Nat.mod_add_div N d
  have hsmall : ((N % d : ℕ) : ℝ) ≤ d := by exact_mod_cast (Nat.mod_lt N hd).le
  have heq : ((N / d : ℕ) : ℝ) / N - 1 / (d : ℝ) =
      -((N % d : ℕ) : ℝ) / ((N : ℝ) * d) := by
    field_simp
    nlinarith
  rw [heq, abs_div, abs_neg, abs_of_nonneg (Nat.cast_nonneg _),
    abs_of_pos (mul_pos hN' hd')]
  apply (div_le_div_iff₀ (mul_pos hN' hd') hN').mpr
  nlinarith

theorem finite_divisibility_error {ι : Type*} (s : Finset ι) (d : ι → ℕ)
    {N : ℕ} (hN : 0 < N) (hd : ∀ i ∈ s, 0 < d i) :
    |(∑ i ∈ s, ((N / d i : ℕ) : ℝ)) / N - ∑ i ∈ s, 1 / (d i : ℝ)| ≤
      (s.card : ℝ) / N := by
  rw [Finset.sum_div, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i ∈ s, |((N / d i : ℕ) : ℝ) / N - 1 / (d i : ℝ)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ s, 1 / (N : ℝ) :=
      Finset.sum_le_sum fun i hi => normalized_division_error hN (hd i hi)
    _ = _ := by simp [div_eq_mul_inv]

/-- A sublinear number of terms makes the complete floor replacement error
vanish. The tuple family is allowed to vary with the counting scale. -/
theorem divisibility_error_tendsto_zero {ι : Type*}
    (s : ℕ → Finset ι) (d : ℕ → ι → ℕ)
    (hd : ∀ N i, i ∈ s N → 0 < d N i)
    (hsmall : Tendsto (fun N => ((s N).card : ℝ) / N) atTop (𝓝 0)) :
    Tendsto (fun N =>
      (∑ i ∈ s N, ((N / d N i : ℕ) : ℝ)) / N -
        ∑ i ∈ s N, 1 / (d N i : ℝ)) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  simp only [Real.norm_eq_abs]
  apply squeeze_zero' (Filter.Eventually.of_forall fun _ => abs_nonneg _)
    (Filter.eventually_atTop.mpr ⟨1, fun N hN =>
      finite_divisibility_error (s N) (d N) (by omega) (hd N)⟩)
  exact hsmall

end JointDickman

end OAI
