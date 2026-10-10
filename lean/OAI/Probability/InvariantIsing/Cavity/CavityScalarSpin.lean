import OAI.Probability.InvariantIsing.Cavity.CavityGaussianAffine
import OAI.Probability.InvariantIsing.Arrays.NSpinFactorization

namespace OAI

/-! The ordinary terminal residual in the cavity spin factor. Its
variance contributes a constant because every Ising spin has norm squared
equal to the number of cavity sites. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

namespace InvariantIsing

private lemma cavity_spin_linear_gaussian_integrable {n : ℕ}
    (v : ℝ≥0) (ε : Spin n) :
    Integrable (fun w : Fin n → ℝ => Real.exp (fieldEnergy w ε))
      (vectorGaussianLaw n v : Measure (Fin n → ℝ)) := by
  have h := cavity_diagonal_gaussian_affine_integrable (fun _ : Fin n => v)
    (fun _ => 0) (fun i => spinValue (ε i)) (fun _ => by simp)
  convert! h using 1
  · funext w
    simp only [fieldEnergy, zero_div, zero_mul, zero_add]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    ring

private lemma cavity_spin_linear_gaussian_integral {n : ℕ}
    (v : ℝ≥0) (ε : Spin n) :
    (∫ w : Fin n → ℝ, Real.exp (fieldEnergy w ε)
      ∂(vectorGaussianLaw n v : Measure (Fin n → ℝ))) = Real.exp ((n : ℝ) * v / 2) := by
  have h := cavity_diagonal_gaussian_affine_integral (fun _ : Fin n => v)
    (fun _ => 0) (fun i => spinValue (ε i)) (fun _ => by simp)
  have he : (fun w : Fin n → ℝ => Real.exp (fieldEnergy w ε)) =
      (fun w : Fin n → ℝ => Real.exp (∑ i, (0 / 2 * w i ^ 2 + spinValue (ε i) * w i))) := by
    funext w
    simp only [fieldEnergy, zero_div, zero_mul, zero_add]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he]
  change (∫ w : Fin n → ℝ, Real.exp (∑ i, (0 / 2 * w i ^ 2 + spinValue (ε i) * w i))
    ∂Measure.pi (fun _ : Fin n => gaussianReal 0 v)) = _
  rw [h]
  simp only [mul_zero, sub_zero, Real.sqrt_one, inv_one, Finset.prod_const_one,
    one_mul, spinValue_sq, mul_one, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  congr 1
  ring

lemma cavity_residual_spin_integrable {n : ℕ} (v : ℝ≥0) (c : ℝ)
    (z : Fin n → ℝ) (ε : Spin n) :
    Integrable (fun w : Fin n → ℝ =>
      Real.exp (fieldEnergy (z + w) ε + (n : ℝ) * c / 2))
      (vectorGaussianLaw n v : Measure (Fin n → ℝ)) := by
  have he : (fun w : Fin n → ℝ => Real.exp (fieldEnergy (z + w) ε + (n : ℝ) * c / 2)) =
      (fun w => Real.exp (fieldEnergy z ε + (n : ℝ) * c / 2) * Real.exp (fieldEnergy w ε)) := by
    funext w
    rw [← Real.exp_add]
    congr 1
    simp only [fieldEnergy, Pi.add_apply, add_mul, Finset.sum_add_distrib]
    ring
  rw [he]
  exact (cavity_spin_linear_gaussian_integrable v ε).const_mul _

/-- The ordinary Gaussian residual supplies `n*v/2` to the logarithm,
independently of the chosen cavity spin. -/
theorem cavity_residual_spin_integral {n : ℕ} (v : ℝ≥0) (c : ℝ)
    (z : Fin n → ℝ) (ε : Spin n) :
    (∫ w : Fin n → ℝ, Real.exp (fieldEnergy (z + w) ε + (n : ℝ) * c / 2)
      ∂(vectorGaussianLaw n v : Measure (Fin n → ℝ))) =
        Real.exp (fieldEnergy z ε + (n : ℝ) * (c + v) / 2) := by
  have he : (fun w : Fin n → ℝ => Real.exp (fieldEnergy (z + w) ε + (n : ℝ) * c / 2)) =
      (fun w => Real.exp (fieldEnergy z ε + (n : ℝ) * c / 2) * Real.exp (fieldEnergy w ε)) := by
    funext w
    rw [← Real.exp_add]
    congr 1
    simp only [fieldEnergy, Pi.add_apply, add_mul, Finset.sum_add_distrib]
    ring
  rw [he, integral_const_mul, cavity_spin_linear_gaussian_integral, ← Real.exp_add]
  congr 1
  ring

def cavityResidualSpinLog (n : ℕ) (v : ℝ≥0) (c : ℝ) (z : Fin n → ℝ) : ℝ :=
  Real.log ((Fintype.card (Spin n) : ℝ)⁻¹ * ∑ ε : Spin n,
    ∫ w : Fin n → ℝ, Real.exp (fieldEnergy (z + w) ε + (n : ℝ) * c / 2)
      ∂(vectorGaussianLaw n v : Measure (Fin n → ℝ)))

/-- The residual-integrated cavity terminal is a sum of one-site
`log cosh` terminals plus the deterministic scalar contribution. -/
theorem cavityResidualSpinLog_eq (n : ℕ) (v : ℝ≥0) (c : ℝ) (z : Fin n → ℝ) :
    cavityResidualSpinLog n v c z =
      (n : ℝ) * (c + v) / 2 + ∑ i, Real.log (Real.cosh (z i)) := by
  unfold cavityResidualSpinLog
  simp_rw [cavity_residual_spin_integral]
  change logPartition (fun ε : Spin n => fieldEnergy z ε + (n : ℝ) * (c + v) / 2) = _
  rw [logPartition_add_const, logPartition_fieldEnergy]
  ring

lemma measurable_cavityResidualSpinLog (n : ℕ) (v : ℝ≥0) (c : ℝ) :
    Measurable (cavityResidualSpinLog n v c) := by
  have he : cavityResidualSpinLog n v c =
      (fun z => (n : ℝ) * (c + v) / 2 + ∑ i, Real.log (Real.cosh (z i))) :=
    funext (cavityResidualSpinLog_eq n v c)
  rw [he]
  fun_prop

end InvariantIsing

end

end OAI
