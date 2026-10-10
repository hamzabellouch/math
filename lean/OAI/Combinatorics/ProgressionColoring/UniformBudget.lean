import OAI.Combinatorics.ProgressionColoring.PerturbationScales
import OAI.Combinatorics.ProgressionColoring.LocalTail

namespace OAI

/-!
# One absolute threshold for the numerical budgets

The constants in the finite counting bounds are fixed arguments here.  The
threshold is uniform in the prime-power base, the label counts, and the eventual
number of colors.  The finite geometric and counting constructions supply the
displayed numerical bounds; none is hidden inside the threshold assertion.
-/

noncomputable section

open Filter Topology

namespace QuantitativeVanDerWaerden.Parameters

theorem integer_affine_risk_le_max {k : ℕ} (hk : 2 ≤ k) {C T : ℝ}
    (hentropy : Real.log (max 1 T) ≤ C * (k : ℝ) ^ (9 / 10 : ℝ) * Real.log k) :
    2 * T * (1 - flipProbability k) ^ ((k + 3) / 4) ≤ affineEnvelope C k := by
  have hp := flipProbability_le_one (by omega : 1 ≤ k)
  have hmax : 0 < max (1 : ℝ) T := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  calc
    _ ≤ 2 * max 1 T * (1 - flipProbability k) ^ ((k + 3) / 4) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (le_max_right _ _) (by norm_num))
        (pow_nonneg (by linarith) _)
    _ ≤ affineEnvelope C k := integer_affine_risk_le hk hmax hentropy

/-- Uniform budget for the exact integer exponents in finite sparse
perturbation.  The base enters only through its proved logarithmic bound. -/
theorem eventually_sparse_budget {C : ℝ} (hC : 0 ≤ C) :
    ∀ᶠ k : ℕ in atTop, ∀ q : ℕ, 0 < q → ∀ T : ℝ,
      (dimension k : ℝ) * Real.log q ≤
        c * k * Real.log k + (dimension k : ℝ) * Real.log (2 * (k : ℝ) ^ 2) →
      Real.log (max 1 T) ≤ C * (k : ℝ) ^ (9 / 10 : ℝ) * Real.log k →
      2 * (((q ^ dimension k : ℕ) : ℝ)) ^ 2 *
          flipProbability k ^ ((k + 399) / 400) +
        2 * T * (1 - flipProbability k) ^ ((k + 3) / 4) < 1 := by
  filter_upwards [eventually_ge_atTop 2, eventually_perturbation_budget hC]
    with k hk hbudget q hq T hlogq hentropy
  have heq : (((q ^ dimension k : ℕ) : ℝ)) ^ 2 =
      (q : ℝ) ^ (2 * dimension k) := by
    rw [Nat.cast_pow, ← pow_mul, Nat.mul_comm]
  rw [heq]
  exact lt_of_le_of_lt
    (add_le_add (integer_rich_risk_le hk hq hlogq)
      (integer_affine_risk_le_max hk hentropy)) hbudget

/-- The row and anchored local weights together eventually obey the incident
weight bound of the asymmetric local lemma.  Any fixed polynomial exponent is
allowed; in particular this includes the proved `14D` pattern bound. -/
theorem eventually_incident_envelope {G C a : ℝ}
    (hG : 0 ≤ G) (hC : 1 ≤ C) (ha : 0 ≤ a) :
    ∀ᶠ k : ℕ in atTop, rowEnvelope G k + localTail C a k < 1 / 500 := by
  have ht := (rowEnvelope_tendsto hG).add (tendsto_localTail_zero hC ha)
  exact ht.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) + 0 < 1 / 500))

theorem eventually_incident_budget {G C a : ℝ}
    (hG : 0 ≤ G) (hC : 1 ≤ C) (ha : 0 ≤ a) :
    ∀ᶠ k : ℕ in atTop, ∀ T : ℝ, 0 < T →
      Real.log T ≤ G * (k : ℝ) ^ (3 / 10 : ℝ) * Real.log k →
      (k : ℝ) * T * Real.exp (-((cutoff k : ℝ) / 10 - 1) / 32) +
        localTail C a k < 1 / 500 := by
  filter_upwards [eventually_incident_envelope hG hC ha, eventually_row_risk_le G]
    with k hbudget hrow T hT hentropy
  exact lt_of_le_of_lt (add_le_add_left (hrow T hT hentropy) _) hbudget

/-- One absolute integer threshold satisfies the geometric scales and both
probability budgets simultaneously. No color-count parameter occurs here. -/
theorem exists_uniform_threshold {G A C a : ℝ}
    (hG : 0 ≤ G) (hA : 0 ≤ A) (hC : 1 ≤ C) (ha : 0 ≤ a) :
    ∃ K : ℕ, ∀ k ≥ K,
      32 ≤ k ∧ BasicScales k ∧ GeometryScales k ∧
      rowEnvelope G k + localTail C a k < 1 / 500 ∧
      richEnvelope k + affineEnvelope A k < 1 := by
  apply eventually_atTop.1
  filter_upwards [eventually_ge_atTop 32, eventually_basicScales,
    eventually_geometryScales, eventually_incident_envelope hG hC ha,
    eventually_perturbation_budget hA] with k hk hb hg hi hp
  exact ⟨hk, hb, hg, hi, hp⟩

end QuantitativeVanDerWaerden.Parameters

end

end OAI
