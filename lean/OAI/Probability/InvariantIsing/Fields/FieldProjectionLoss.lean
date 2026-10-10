import OAI.Probability.InvariantIsing.Fields.SpinProjectionTrial
import OAI.Probability.InvariantIsing.Fields.FieldSpinProjectionEnergy
import OAI.Probability.InvariantIsing.Magnetic.RestrictedFieldTerminal

namespace OAI

/-! A depth-free terminal loss estimate for the actual constrained
partition function. It separates the field second moment from the
expected number of flips, before any Gaussian-path averaging. -/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace InvariantIsing

def fieldProjectionDistance {N : ℕ} (f : Spin N → Spin N) (z : Fin N → ℝ) : ℝ :=
  ∑ σ, finiteCanonicalWeights (fieldEnergy z) σ * (hammingDist σ (f σ) : ℝ)

lemma fieldProjectionDistance_nonneg {N : ℕ} (f : Spin N → Spin N) (z : Fin N → ℝ) :
    0 ≤ fieldProjectionDistance f z :=
  Finset.sum_nonneg (fun σ _ => mul_nonneg (finiteCanonicalWeights_pos _ σ).le
    (Nat.cast_nonneg _))

lemma two_sqrt_mul_le_add_div {M D ε : ℝ} (hM : 0 ≤ M) (hD : 0 ≤ D) (hε : 0 < ε) :
    2 * Real.sqrt (M * D) ≤ ε * M + D / ε := by
  have he : (ε * M) * (D / ε) = M * D := by field_simp
  apply (sq_le_sq₀ (by positivity) (by positivity)).mp
  rw [mul_pow, Real.sq_sqrt (mul_nonneg hM hD)]
  nlinarith [sq_nonneg (ε * M - D / ε)]

theorem field_projection_terminal_loss {N : ℕ} (S : Finset (Spin N)) (hS : S.Nonempty)
    (f : Spin N → Spin N) (hf : ∀ σ, f σ ∈ S) (z : Fin N → ℝ) (t : ℝ) :
    (∑ i, Real.log (Real.cosh (z i))) - restrictedFieldTerminal S z ≤
      2 * Real.sqrt ((∑ i, z i ^ 2) * fieldProjectionDistance f z) +
        t * fieldProjectionDistance f z + N * Real.log (1 + Real.exp (-t)) := by
  have ht := restrictedSpinLog_projection_bound S hS f hf (fieldEnergy z) t
  have he := fieldEnergy_projection_mean_le z f (finiteCanonicalWeights (fieldEnergy z))
    (fun σ => (finiteCanonicalWeights_pos _ σ).le) (finiteCanonicalWeights_sum _)
  rw [logPartition_fieldEnergy] at ht
  exact ht.trans (add_le_add (add_le_add
    ((le_abs_self _).trans he) le_rfl) le_rfl)

theorem field_projection_terminal_loss_linear {N : ℕ} (S : Finset (Spin N))
    (hS : S.Nonempty) (f : Spin N → Spin N) (hf : ∀ σ, f σ ∈ S)
    (z : Fin N → ℝ) (t : ℝ) {ε : ℝ} (hε : 0 < ε) :
    (∑ i, Real.log (Real.cosh (z i))) - restrictedFieldTerminal S z ≤
      ε * (∑ i, z i ^ 2) + (ε⁻¹ + t) * fieldProjectionDistance f z +
        N * Real.log (1 + Real.exp (-t)) := by
  have he := two_sqrt_mul_le_add_div
    (Finset.sum_nonneg (s := Finset.univ) (fun i _ => sq_nonneg (z i)))
    (fieldProjectionDistance_nonneg f z) hε
  have ht := field_projection_terminal_loss S hS f hf z t
  rw [div_eq_mul_inv] at he
  nlinarith

end InvariantIsing

end

end OAI
