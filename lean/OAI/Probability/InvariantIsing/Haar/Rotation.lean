import OAI.Probability.InvariantIsing.Core.Model

namespace OAI

/-!
# Ising pressure on an orthogonal spectral orbit

The interaction is defined using a real linear isometry, so orthogonality
is part of its type. The bounds hold pointwise in the rotation; no Haar
or independence assumption is needed for these finite-volume estimates.
-/

noncomputable section

open scoped BigOperators Topology
open Filter

namespace InvariantIsing

abbrev Rotation (N : ℕ) :=
  EuclideanSpace ℝ (Fin N) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin N)

def spinVector {N : ℕ} (σ : Spin N) : EuclideanSpace ℝ (Fin N) :=
  WithLp.toLp 2 (fun i => spinValue (σ i))

@[simp] lemma spinVector_apply {N : ℕ} (σ : Spin N) (i : Fin N) :
    spinVector σ i = spinValue (σ i) := rfl

lemma spinVector_norm_sq {N : ℕ} (σ : Spin N) : ‖spinVector σ‖ ^ 2 = N := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp only [spinVector_apply, spinValue_sq, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one]

lemma rotated_spin_sq_sum {N : ℕ} (U : Rotation N) (σ : Spin N) :
    (∑ i, (U (spinVector σ) i) ^ 2) = N := by
  rw [← EuclideanSpace.real_norm_sq_eq, U.norm_map, spinVector_norm_sq]

/-- The quadratic energy in spectral coordinates, equal to
`σᵀ Uᵀ diag(eig) U σ / 2`. -/
def rotatedEnergy {N : ℕ} (eig : Fin N → ℝ) (U : Rotation N) (σ : Spin N) : ℝ :=
  (1 / 2 : ℝ) * ∑ i, eig i * (U (spinVector σ) i) ^ 2

/-- Equation (1.1), with an optional deterministic magnetic field. -/
def rotatedPressure {N : ℕ} (eig : Fin N → ℝ) (U : Rotation N)
    (c : Fin N → ℝ) : ℝ :=
  (N : ℝ)⁻¹ * logPartition (fun σ => rotatedEnergy eig U σ + fieldEnergy c σ)

lemma rotatedEnergy_constant {N : ℕ} (a : ℝ) (U : Rotation N) (σ : Spin N) :
    rotatedEnergy (fun _ => a) U σ = a * N / 2 := by
  rw [rotatedEnergy, ← Finset.mul_sum, rotated_spin_sq_sum]
  ring

@[simp] lemma logPartition_zero {X : Type*} [Fintype X] [Nonempty X] :
    logPartition (fun _ : X => (0 : ℝ)) = 0 := by
  rw [logPartition_eq]
  simp

lemma rotatedPressure_constant {N : ℕ} (hN : 0 < N) (a : ℝ) (U : Rotation N) :
    rotatedPressure (fun _ => a) U (fun _ => 0) = a / 2 := by
  have he : (fun σ => rotatedEnergy (fun _ : Fin N => a) U σ +
      fieldEnergy (fun _ => 0) σ) = (fun _ : Spin N => 0 + a * N / 2) := by
    funext σ
    simp [rotatedEnergy_constant, fieldEnergy]
  rw [rotatedPressure, he, logPartition_add_const, logPartition_zero, zero_add]
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
  field_simp

/-- Pointwise operator comparison in spectral coordinates. -/
lemma abs_rotatedEnergy_sub_le {N : ℕ} (eig κ : Fin N → ℝ) (U : Rotation N)
    (δ : ℝ) (hδ : ∀ i, |eig i - κ i| ≤ δ) (σ : Spin N) :
    |rotatedEnergy eig U σ - rotatedEnergy κ U σ| ≤ δ * N / 2 := by
  have he : rotatedEnergy eig U σ - rotatedEnergy κ U σ =
      (1 / 2 : ℝ) * ∑ i, (eig i - κ i) * (U (spinVector σ) i) ^ 2 := by
    simp only [rotatedEnergy, sub_mul, Finset.sum_sub_distrib]
    ring
  rw [he, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  calc
    _ ≤ (1 / 2 : ℝ) * ∑ i, |(eig i - κ i) * (U (spinVector σ) i) ^ 2| :=
      mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by norm_num)
    _ = (1 / 2 : ℝ) * ∑ i, |eig i - κ i| * (U (spinVector σ) i) ^ 2 := by
      simp only [abs_mul, abs_sq]
    _ ≤ (1 / 2 : ℝ) * ∑ i, δ * (U (spinVector σ) i) ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hδ i) (sq_nonneg _)
    _ = δ * N / 2 := by rw [← Finset.mul_sum, rotated_spin_sq_sum]; ring

/-- Equation (6.6), pointwise in the rotation and independent of the field. -/
lemma abs_rotatedPressure_sub_le {N : ℕ} (hN : 0 < N)
    (eig κ : Fin N → ℝ) (U : Rotation N) (c : Fin N → ℝ)
    (δ : ℝ) (hδ : ∀ i, |eig i - κ i| ≤ δ) :
    |rotatedPressure eig U c - rotatedPressure κ U c| ≤ δ / 2 := by
  have h := abs_logPartition_sub_le
    (fun σ => rotatedEnergy eig U σ + fieldEnergy c σ)
    (fun σ => rotatedEnergy κ U σ + fieldEnergy c σ)
    (δ * N / 2) (fun σ => by
      simpa only [add_sub_add_right_eq_sub] using abs_rotatedEnergy_sub_le eig κ U δ hδ σ)
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
  calc
    _ = (N : ℝ)⁻¹ * |logPartition (fun σ => rotatedEnergy eig U σ + fieldEnergy c σ) -
        logPartition (fun σ => rotatedEnergy κ U σ + fieldEnergy c σ)| := by
      rw [rotatedPressure, rotatedPressure, ← mul_sub, abs_mul,
        abs_of_nonneg (show (0 : ℝ) ≤ (N : ℝ)⁻¹ by positivity)]
    _ ≤ (N : ℝ)⁻¹ * (δ * N / 2) :=
      mul_le_mul_of_nonneg_left h (by positivity)
    _ = δ / 2 := by field_simp

/-- The point-mass spectral specialization: spectra uniformly approaching a scalar
have limiting pressure `a/2` for every choice of rotations. -/
lemma tendsto_pressure_scalar_spectrum
    (eig : (N : ℕ) → Fin (N + 1) → ℝ) (U : (N : ℕ) → Rotation (N + 1))
    (a : ℝ) (δ : ℕ → ℝ) (hδ : Tendsto δ atTop (nhds 0))
    (heig : ∀ N i, |eig N i - a| ≤ δ N) :
    Tendsto (fun N => rotatedPressure (eig N) (U N) (fun _ => 0)) atTop (nhds (a / 2)) := by
  have hb : ∀ N, |rotatedPressure (eig N) (U N) (fun _ => 0) - a / 2| ≤ δ N / 2 := by
    intro N
    have h := abs_rotatedPressure_sub_le (Nat.zero_lt_succ N) (eig N) (fun _ => a)
      (U N) (fun _ => 0) (δ N) (heig N)
    rwa [rotatedPressure_constant (Nat.zero_lt_succ N)] at h
  have hz : Tendsto (fun N => |rotatedPressure (eig N) (U N) (fun _ => 0) - a / 2|)
      atTop (nhds 0) :=
    squeeze_zero (fun _ => abs_nonneg _) hb (by simpa using hδ.div_const 2)
  exact tendsto_iff_norm_sub_tendsto_zero.mpr (by simpa only [Real.norm_eq_abs] using hz)

end InvariantIsing

end

end OAI
