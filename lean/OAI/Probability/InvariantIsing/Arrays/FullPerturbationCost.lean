import OAI.Probability.InvariantIsing.Arrays.TensorPerturbationCost
import OAI.Probability.InvariantIsing.Spectral.SpectralDiagonalPerturbation

namespace OAI

/-! Uniform vanishing cost of both terms of the manuscript perturbation. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators NNReal

namespace InvariantIsing

private lemma rotatedEnergy_mul {N : ℕ} (eig : Fin N → ℝ) (U : Rotation N) (t : ℝ) (σ : Spin N) :
    rotatedEnergy (fun i => t * eig i) U σ = t * rotatedEnergy eig U σ := by
  simp only [rotatedEnergy, mul_assoc, ← Finset.mul_sum]
  ring

lemma abs_tensorPathPressure_sub_base_le {N m k : ℕ} (hN : 0 < N)
    (eig eig' c : Fin N → ℝ) (U : Rotation N)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (a : Fin k → ℝ)
    (n : ℕ) (r : Fin k → ℕ) (b : ℕ → ℝ) (hb : CascadeExponents n b)
    (h : ℕ → ℝ) (hh : Monotone h) (h0 : 0 ≤ h 0) (C : ℝ)
    (hE : ∀ σ, |rotatedEnergy eig U σ - rotatedEnergy eig' U σ| ≤ C) :
    let v := tensorPathProfile I degree n r h
    |tensorEnrichedPressure eig U c I degree a n b (fun i => v (i + 1)) (v 0) -
      tensorEnrichedPressure eig' U c I degree a n b (fun i => v (i + 1)) (v 0)| ≤
      (N : ℝ)⁻¹ * C := by
  intro v
  have hA := tensorFlatLog_integrable eig U c I degree a n b v
  have hB := tensorFlatLog_integrable eig' U c I degree a n b v
  have hpoint (T : LabeledTree n) :
      |(∫ g, tensorFlatLog eig U c I degree a n v (T, g) ∂gaussianCoordinates) -
        ∫ g, tensorFlatLog eig' U c I degree a n v (T, g) ∂gaussianCoordinates| ≤ C := by
    let ν := labeledSpinReference n (uniformSpinPrior N : Measure (Spin N)) T
    have he := countable_cylinder_log_mean_base_compare ν
      (fun x => rotatedEnergy eig U x.1 + fieldEnergy c x.1)
      (fun x => rotatedEnergy eig' U x.1 + fieldEnergy c x.1)
      (finite_spin_base_exp_integrable ν (fun σ => rotatedEnergy eig U σ + fieldEnergy c σ))
      (finite_spin_base_exp_integrable ν (fun σ => rotatedEnergy eig' U σ + fieldEnergy c σ))
      (tensorLeafCoefficients U I degree a n (fun i => v i))
      (tensorPathProfile_variance_cap U I degree a n r h hh h0)
      (fun x => by simpa only [add_sub_add_right_eq_sub] using hE x.1)
    exact he
  have hi := norm_integral_le_of_norm_le_const
    (μ := (labeledCascadeLaw n b : Measure (LabeledTree n)))
    (f := fun T => (∫ g, tensorFlatLog eig U c I degree a n v (T, g) ∂gaussianCoordinates) -
      ∫ g, tensorFlatLog eig' U c I degree a n v (T, g) ∂gaussianCoordinates)
    (C := C) (ae_of_all _ fun T => by simpa only [Real.norm_eq_abs] using hpoint T)
  rw [tensorEnrichedPressure_eq_flat_mean hN eig U c I degree a n b v hb,
    tensorEnrichedPressure_eq_flat_mean hN eig' U c I degree a n b v hb,
    ← mul_sub, ← integral_sub hA.integral_prod_left hB.integral_prod_left, abs_mul,
    abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg N))]
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Nat.cast_nonneg N))
  simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using hi

/-- The actual diagonal and Gaussian perturbations together cost at most
`2 m e_N + 8 e_N²`, uniformly in the other deterministic parameters. -/
theorem fullPerturbationPressure_cost {N m : ℕ} (hN : 0 < N)
    (eig c : Fin N → ℝ) (U : Rotation N) (I : Fin m → Finset (Fin N))
    (degree : Fin N → Fin m → ℕ) (u : Fin N → ℝ) (hu : ∀ j, |u j| ≤ 2)
    (z : Fin m → ℝ) (hz : ∀ a, |z a| ≤ 2) (t : ℝ)
    (n : ℕ) (r : Fin N → ℕ) (b : ℕ → ℝ) (hb : CascadeExponents n b)
    (h : ℕ → ℝ) (hh : Monotone h) (h0 : 0 ≤ h 0) :
    let v := tensorPathProfile I degree n r h
    |tensorEnrichedPressure (diagonalPerturbedEigenvalues eig I z t) U c I degree
        (tensorPerturbationAmplitude N u) n b (fun i => v (i + 1)) (v 0) -
      tensorEnrichedPressure (fun i => t * eig i) U c I degree 0 n b
        (fun i => v (i + 1)) (v 0)| ≤
      2 * m * perturbationScale N + 8 * perturbationScale N ^ 2 := by
  intro v
  have hg := tensorPerturbationPressure_cost hN (diagonalPerturbedEigenvalues eig I z t) c U I
    degree u hu n r b hb h hh h0
  have hd := abs_tensorPathPressure_sub_base_le hN (diagonalPerturbedEigenvalues eig I z t)
    (fun i => t * eig i) c U I degree 0 n r b hb h hh h0
    (2 * m * N * perturbationScale N) (fun σ => by
      rw [rotatedEnergy_mul]
      exact abs_rotatedEnergy_diagonalPerturbation_le hN eig U I z hz t σ)
  have hn : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have he : (N : ℝ)⁻¹ * (2 * m * N * perturbationScale N) = 2 * m * perturbationScale N := by
    field_simp
  rw [he] at hd
  exact (abs_sub_le _ _ _).trans ((add_le_add hg hd).trans_eq (by ring))

lemma fullPerturbationCost_tendsto (m : ℕ) :
    Filter.Tendsto (fun N => 2 * m * perturbationScale N + 8 * perturbationScale N ^ 2)
      Filter.atTop (nhds (0 : ℝ)) := by
  simpa only [mul_zero, zero_pow (by norm_num : 2 ≠ 0), add_zero] using
    (perturbationScale_tendsto.const_mul (2 * (m : ℝ))).add
      ((perturbationScale_tendsto.pow 2).const_mul 8)

end InvariantIsing

end

end OAI
