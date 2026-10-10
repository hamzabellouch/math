import OAI.Geometry.EinsteinFour.AngularRotation

namespace OAI

/-! The pointwise and averaged normal Jacobi curvature form. -/

namespace PositiveEinsteinFour.Angular

open Matrix MeasureTheory

noncomputable section

abbrev Mat3 := Geometry.Mat3

def squareNorm (T : Mat3) : ℝ := ∑ i, ∑ j, T i j ^ 2

def pairing (T U : Mat3) : ℝ := ∑ i, ∑ j, T i j * U i j

def rotated (U : Mat3) (q : Directions) : Mat3 :=
  mixingMatrix q * U * (mixingMatrix q)ᵀ

/-- The curvature deviation in the normal basis `I_s q`. -/
def normalDeviation (T U : Mat3) (q : Directions) : Mat3 :=
  (1 / 2 : ℝ) • (T + rotated U q)

theorem squareNorm_eq_trace (T : Mat3) : squareNorm T = (Tᵀ * T).trace := by
  simp only [squareNorm, Matrix.trace, Matrix.diag, Matrix.mul_apply,
    Matrix.transpose_apply]
  rw [Finset.sum_comm]
  simp only [pow_two]

theorem squareNorm_conjugate (O U : Mat3) (hO : O * Oᵀ = 1) :
    squareNorm (O * U * Oᵀ) = squareNorm U := by
  have hOT : Oᵀ * O = 1 := mul_eq_one_comm.mp hO
  rw [squareNorm_eq_trace, squareNorm_eq_trace]
  have hp : (O * U * Oᵀ)ᵀ * (O * U * Oᵀ) = O * (Uᵀ * U) * Oᵀ := by
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose]
    calc
      (O * (Uᵀ * Oᵀ)) * (O * U * Oᵀ) = O * Uᵀ * (Oᵀ * O) * U * Oᵀ := by
        noncomm_ring
      _ = _ := by rw [hOT, mul_one]; noncomm_ring
  rw [hp, Matrix.trace_mul_cycle, hOT, one_mul]

theorem squareNorm_rotated (U : Mat3) (q : Directions) :
    squareNorm (rotated U q) = squareNorm U :=
  squareNorm_conjugate _ _ (mixing_orthogonal q)

private theorem norm_add_half (T U : Fin 3 → Fin 3 → ℝ) :
    (∑ i, ∑ j, ((1 / 2 : ℝ) * (T i j + U i j)) ^ 2) =
      ((∑ i, ∑ j, T i j ^ 2) + (∑ i, ∑ j, U i j ^ 2) +
        2 * (∑ i, ∑ j, T i j * U i j)) / 4 := by
  have hp (i j : Fin 3) : ((1 / 2 : ℝ) * (T i j + U i j)) ^ 2 =
      (T i j ^ 2 + U i j ^ 2 + 2 * (T i j * U i j)) / 4 := by ring
  simp_rw [hp, ← Finset.sum_div, Finset.sum_add_distrib, ← Finset.mul_sum]

theorem squareNorm_normalDeviation (T U : Mat3) (q : Directions) :
    squareNorm (normalDeviation T U q) =
      (squareNorm T + squareNorm U + 2 * pairing T (rotated U q)) / 4 := by
  rw [← squareNorm_rotated U q]
  simpa only [squareNorm, pairing, normalDeviation, Matrix.smul_apply,
    Matrix.add_apply, smul_eq_mul] using! norm_add_half T (rotated U q)

private theorem pairing_delta_sum (T U : Fin 3 → Fin 3 → ℝ) :
    (∑ i, ∑ j, ∑ k, ∑ l, T i j * U k l *
      (if i = j then (if k = l then (1 / 3 : ℝ) else 0) else 0)) =
        ((∑ i, T i i) * (∑ k, U k k)) / 3 := by
  simp [mul_ite, div_eq_mul_inv, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  rw [Finset.sum_comm]

theorem integral_mixed_pairing (h : FollandMoments) (T U : Mat3)
    (hT : T.trace = 0) (hU : U.trace = 0) :
    (∫ q, pairing T (rotated U q) ∂sphereMeasure) = 0 := by
  have he : (fun q => pairing T (rotated U q)) = fun q =>
      ∑ i, ∑ j, ∑ k, ∑ l, T i j * U k l * (mixing i k q * mixing j l q) := by
    funext q
    simp only [pairing, rotated, Matrix.mul_apply, Matrix.transpose_apply,
      Finset.sum_mul, Finset.mul_sum]
    simp only [mixingMatrix]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro l _
    ring
  rw [he, integral_sum4 h _ (fun _ _ _ _ => by unfold mixing quadratic; fun_prop)]
  simp_rw [integral_const_mul, integral_mixing_mul h]
  have ht : ∑ i, T i i = 0 := hT
  have hu : ∑ i, U i i = 0 := hU
  have hs := pairing_delta_sum T U
  rw [ht, hu] at hs
  simpa only [zero_mul, zero_div] using! hs

/-- The first identity in the manuscript's geodesic averages, on each
individual unit tangent sphere. -/
theorem integral_squareNorm_normalDeviation (h : FollandMoments) (T U : Mat3)
    (hT : T.trace = 0) (hU : U.trace = 0) :
    (∫ q, squareNorm (normalDeviation T U q) ∂sphereMeasure) =
      (squareNorm T + squareNorm U) / 4 := by
  let : IsProbabilityMeasure sphereMeasure := h.probability
  have hc : Continuous (fun q => pairing T (rotated U q)) := by
    simp only [pairing, rotated, Matrix.mul_apply, Matrix.transpose_apply]
    simp only [mixingMatrix, mixing, quadratic]
    fun_prop
  have hi := continuous_integrable h hc
  have he : (fun q => squareNorm (normalDeviation T U q)) =
      fun q => (squareNorm T + squareNorm U + 2 * pairing T (rotated U q)) / 4 :=
    funext (squareNorm_normalDeviation T U)
  rw [he, integral_div, integral_add (integrable_const _) (hi.const_mul 2),
    integral_const_mul, integral_mixed_pairing h T U hT hU]
  simp

theorem integral_squareNorm_normalDeviation_normalized (h : FollandMoments) (T U : Mat3)
    (hT : T.trace = 0) (hU : U.trace = 0) :
    (∫ q, squareNorm (normalDeviation T U q) ∂sphereMeasure) =
      (3 / 2) * (Geometry.normalizedBlockNorm T ^ 2 +
        Geometry.normalizedBlockNorm U ^ 2) := by
  rw [integral_squareNorm_normalDeviation h T U hT hU,
    Geometry.normalizedBlockNorm_sq, Geometry.normalizedBlockNorm_sq]
  unfold squareNorm
  ring

end

end PositiveEinsteinFour.Angular

end OAI
