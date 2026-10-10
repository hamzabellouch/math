import OAI.LinearAlgebra.MatrixMultiplication.ComplexBounds.CW75ReorderedBalanced
import OAI.LinearAlgebra.MatrixMultiplication.ComplexBounds.CW75ReorderedFiniteRates
import OAI.LinearAlgebra.MatrixMultiplication.Entropy.ConditionalRateBridge
import OAI.LinearAlgebra.MatrixMultiplication.Rectangular.Witness

namespace OAI

/-! Explicit complex square and rectangular matrix multiplication bounds. -/

noncomputable section

namespace MatrixMultiplication.CW75ReorderedBalancedRates

open MatrixMultiplication.Foundation Filter CW75LabelHierarchy
open ConditionalLabels ComplexWitness CW75ReorderedBalanced
open scoped BigOperators Topology Classical

variable (counts : Scalar → ℕ) (hD : 0 < ∑ a, counts a)
  (p : FiniteLaw Scalar)
  (mass : ∀ a, p.mass a = (counts a : ℝ) / (∑ b, counts b : ℕ))

include hD mass

theorem tendsto_log_rows :
    Tendsto (fun t => Real.log (CW75ReorderedFinite.rows counts t : ℝ) /
      ((t : ℝ) * (∑ a, counts a : ℕ))) atTop
      (𝓝 (lawPairingRate p curveLabels 5 curveReaderPair .xz)) := by
  have h := tendsto_log_stagePairingSize_law counts hD p mass
    curveLabels 5 curveReaderPair .xz
  apply h.congr
  intro t
  rw [(CW75ReorderedFinite.dimensions_eq_pairingSize counts t).1]

theorem tendsto_log_inner :
    Tendsto (fun t => Real.log (CW75ReorderedFinite.inner counts t : ℝ) /
      ((t : ℝ) * (∑ a, counts a : ℕ))) atTop
      (𝓝 (lawPairingRate p curveLabels 5 curveReaderPair .xy)) := by
  have h := tendsto_log_stagePairingSize_law counts hD p mass
    curveLabels 5 curveReaderPair .xy
  apply h.congr
  intro t
  rw [(CW75ReorderedFinite.dimensions_eq_pairingSize counts t).2.1]

theorem tendsto_log_columns :
    Tendsto (fun t => Real.log (CW75ReorderedFinite.columns counts t : ℝ) /
      ((t : ℝ) * (∑ a, counts a : ℕ))) atTop
      (𝓝 (lawPairingRate p curveLabels 5 curveReaderPair .yz)) := by
  have h := tendsto_log_stagePairingSize_law counts hD p mass
    curveLabels 5 curveReaderPair .yz
  apply h.congr
  intro t
  rw [(CW75ReorderedFinite.dimensions_eq_pairingSize counts t).2.2]

theorem tendsto_log_witness_outer :
    Tendsto (fun t => Real.log ((witness counts t).outer : ℝ) /
      ((t : ℝ) * (∑ a, counts a : ℕ))) atTop
      (𝓝 (lawPairingRate p curveLabels 5 curveReaderPair .xy +
        lawPairingRate p curveLabels 5 curveReaderPair .xz)) := by
  have h := (tendsto_log_rows counts hD p mass).add
    (tendsto_log_inner counts hD p mass)
  rw [add_comm (lawPairingRate p curveLabels 5 curveReaderPair .xz)] at h
  apply h.congr
  intro t
  rw [witness_outer, Nat.cast_mul, Real.log_mul
    (Nat.cast_ne_zero.mpr (Nat.ne_of_gt (CW75ReorderedFinite.rows_pos counts t)))
    (Nat.cast_ne_zero.mpr (Nat.ne_of_gt (CW75ReorderedFinite.inner_pos counts t))), add_div]

theorem tendsto_log_witness_inner :
    Tendsto (fun t => Real.log ((witness counts t).inner : ℝ) /
      ((t : ℝ) * (∑ a, counts a : ℕ))) atTop
      (𝓝 (2 * lawPairingRate p curveLabels 5 curveReaderPair .yz)) := by
  simpa only [witness_inner, Nat.cast_pow, Real.log_pow, Nat.cast_ofNat,
    mul_div_assoc] using (tendsto_log_columns counts hD p mass).const_mul 2

theorem tendsto_log_witness_multiplicity :
    Tendsto (fun t => Real.log ((witness counts t).multiplicity : ℝ) /
      ((t : ℝ) * (∑ a, counts a : ℕ))) atTop
      (𝓝 (2 * finiteEntropy p.mass)) := by
  simpa only [witness_multiplicity, Nat.cast_pow, Real.log_pow, Nat.cast_ofNat,
    mul_div_assoc] using
      (CW75ReorderedFiniteRates.tendsto_log_copies counts hD p mass).const_mul 2

theorem tendsto_log_witness_rank :
    Tendsto (fun t => Real.log ((witness counts t).rank : ℝ) /
      ((t : ℝ) * (∑ a, counts a : ℕ))) atTop
      (𝓝 (6 * Real.log 3 + 2 * finiteEntropy p.mass)) := by
  have h := (CW75ReorderedFiniteRates.tendsto_log_rankBudget counts hD p mass).const_mul 2
  have hcost : 2 * (3 * Real.log 3 + finiteEntropy p.mass) =
      6 * Real.log 3 + 2 * finiteEntropy p.mass := by ring
  simpa only [witness_rank, Nat.cast_pow, Real.log_pow, Nat.cast_ofNat,
    mul_div_assoc, hcost] using h

omit mass

theorem scale_eventually_pos :
    ∀ᶠ t : ℕ in atTop, 0 < (t : ℝ) * (∑ a, counts a : ℕ) := by
  filter_upwards [eventually_ge_atTop 1] with t ht
  exact mul_pos (Nat.cast_pos.mpr (by omega)) (Nat.cast_pos.mpr hD)

include mass

theorem omega_lt_of_fixed_count_law (k target : ℝ)
    (k_nonneg : 0 ≤ k)
    (incident_positive : 0 < lawPairingRate p curveLabels 5 curveReaderPair .xy +
      lawPairingRate p curveLabels 5 curveReaderPair .xz)
    (aspect_gap : k * (lawPairingRate p curveLabels 5 curveReaderPair .xy +
      lawPairingRate p curveLabels 5 curveReaderPair .xz) <
      2 * lawPairingRate p curveLabels 5 curveReaderPair .yz)
    (cost_gap : 6 * Real.log 3 < target *
      (lawPairingRate p curveLabels 5 curveReaderPair .xy +
        lawPairingRate p curveLabels 5 curveReaderPair .xz)) :
    Arithmetic.rectangularOmega ℂ k < target :=
  RectangularWitness.omega_lt_of_balanced_family (witness counts)
    (fun t => (t : ℝ) * (∑ a, counts a : ℕ)) k target
    (lawPairingRate p curveLabels 5 curveReaderPair .yz)
    (lawPairingRate p curveLabels 5 curveReaderPair .xy +
      lawPairingRate p curveLabels 5 curveReaderPair .xz)
    (finiteEntropy p.mass) k_nonneg incident_positive aspect_gap cost_gap
    (scale_eventually_pos counts hD)
    (tendsto_log_witness_outer counts hD p mass)
    (tendsto_log_witness_inner counts hD p mass)
    (tendsto_log_witness_multiplicity counts hD p mass)
    (tendsto_log_witness_rank counts hD p mass)

end MatrixMultiplication.CW75ReorderedBalancedRates

end

end OAI
