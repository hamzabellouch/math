import OAI.Geometry.EinsteinFour.AngularSixth
import OAI.Geometry.EinsteinFour.AngularClifford

namespace OAI

/-! The opposite Weyl blocks have zero mixed directional energy. -/

namespace PositiveEinsteinFour.Angular

open Matrix MeasureTheory

noncomputable section

def weightedMixingMoment (a b : Fin 4) (i j k l : Fin 3) : ℝ :=
  ∫ q, q.val a * q.val b * (mixing i k q * mixing j l q) ∂sphereMeasure

theorem weightedMixingMoment_symm (h : FollandMoments)
    (a b : Fin 4) (i j k l : Fin 3) :
    weightedMixingMoment a b i j k l + weightedMixingMoment a b j i k l =
      if i = j then (if k = l then delta a b / 6 else 0) else 0 := by
  unfold weightedMixingMoment mixing
  rw [integral_weighted_quadratic_mul_traceFree h _ _
    (mixingCoefficient_trace i k) (mixingCoefficient_trace j l)
    (mixingCoefficient_symmetric i k) (mixingCoefficient_symmetric j l),
    integral_weighted_quadratic_mul_traceFree h _ _
    (mixingCoefficient_trace j k) (mixingCoefficient_trace i l)
    (mixingCoefficient_symmetric j k) (mixingCoefficient_symmetric i l)]
  rw [mixingCoefficient_pairing, mixingCoefficient_pairing]
  have hp := congrArg (fun A : Mat4 => A a b) (mixingCoefficient_product_symm i j k l)
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply] at hp
  simp only [Matrix.add_apply]
  by_cases hij : i = j <;> by_cases hkl : k = l <;> by_cases hab : a = b <;>
    simp [hij, hkl, hab, eq_comm, delta] at hp ⊢ <;> linarith

/-- Symmetrize a finite contraction against a symmetric matrix. -/
theorem symmetric_contraction (T X : Fin 3 → Fin 3 → ℝ)
    (hT : ∀ i j, T i j = T j i) :
    2 * (∑ i, ∑ j, T i j * X i j) =
      ∑ i, ∑ j, T i j * (X i j + X j i) := by
  have hs : (∑ i, ∑ j, T i j * X j i) = ∑ i, ∑ j, T i j * X i j := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hT j i]
  simp_rw [mul_add, Finset.sum_add_distrib]
  rw [hs]
  ring

private theorem sum4_swap (f : Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℝ) :
    (∑ i, ∑ j, ∑ k, ∑ l, f i j k l) = ∑ k, ∑ l, ∑ i, ∑ j, f i j k l := by
  calc
    _ = ∑ i, ∑ k, ∑ j, ∑ l, f i j k l := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
    _ = ∑ k, ∑ i, ∑ j, ∑ l, f i j k l := by rw [Finset.sum_comm]
    _ = ∑ k, ∑ i, ∑ l, ∑ j, f i j k l := by
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k _
      rw [Finset.sum_comm]

/-- The sixth moment cancels against a symmetric trace-free plus block.
No differential Bianchi premise is needed for this angular identity. -/
theorem weighted_mixing_contraction_zero (h : FollandMoments)
    (T U : Fin 3 → Fin 3 → ℝ) (hT : ∀ i j, T i j = T j i)
    (ht : ∑ i, T i i = 0) (a b : Fin 4) :
    (∑ i, ∑ j, ∑ k, ∑ l,
      T i j * U k l * weightedMixingMoment a b i j k l) = 0 := by
  have hz (k l : Fin 3) :
      (∑ i, ∑ j, T i j * weightedMixingMoment a b i j k l) = 0 := by
    have hs := symmetric_contraction T (fun i j => weightedMixingMoment a b i j k l) hT
    simp_rw [weightedMixingMoment_symm h] at hs
    by_cases hkl : k = l
    · simp [hkl, mul_ite, ← Finset.sum_mul, ht] at hs
      simpa only [hkl] using hs
    · simp [hkl] at hs
      linarith
  rw [sum4_swap]
  apply Finset.sum_eq_zero
  intro k _
  apply Finset.sum_eq_zero
  intro l _
  calc
    (∑ i, ∑ j, T i j * U k l * weightedMixingMoment a b i j k l) =
        U k l * (∑ i, ∑ j, T i j * weightedMixingMoment a b i j k l) := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = 0 := by rw [hz, mul_zero]

/-- A weighted mixed contraction vanishes pointwise over the base. -/
theorem integral_weighted_pairing_zero (h : FollandMoments) (T U : Mat3)
    (hTs : Tᵀ = T) (hTt : T.trace = 0) (a b : Fin 4) :
    (∫ q, q.val a * q.val b * pairing T (rotated U q) ∂sphereMeasure) = 0 := by
  have he : (fun q : Directions => q.val a * q.val b * pairing T (rotated U q)) =
      fun q => ∑ i, ∑ j, ∑ k, ∑ l, T i j * U k l *
        (q.val a * q.val b * (mixing i k q * mixing j l q)) := by
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
  simp_rw [integral_const_mul]
  have hs (i j : Fin 3) : T i j = T j i :=
    (congrFun (congrFun hTs i) j).symm
  have ht : ∑ i, T i i = 0 := hTt
  simpa only [weightedMixingMoment] using!
    weighted_mixing_contraction_zero h T U hs ht a b

/-- The Frobenius pairing, packaged only to expand finite directional sums. -/
def angularPairingLinear : Mat3 →ₗ[ℝ] Mat3 →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ pairing
    (by intro T V U; simp only [pairing, Matrix.add_apply, add_mul,
          Finset.sum_add_distrib])
    (by intro c T U; simp only [pairing, Matrix.smul_apply, smul_eq_mul,
          mul_assoc, ← Finset.mul_sum])
    (by intro T U V; simp only [pairing, Matrix.add_apply, mul_add,
          Finset.sum_add_distrib])
    (by intro c T U
        have hp (i j : Fin 3) : T i j * (c * U i j) = c * (T i j * U i j) := by ring
        simp only [pairing, Matrix.smul_apply, smul_eq_mul]
        simp_rw [hp, ← Finset.mul_sum])

def rotatedLinear (q : Directions) : Mat3 →ₗ[ℝ] Mat3 :=
  (LinearMap.mulRight ℝ (mixingMatrix q)ᵀ).comp (LinearMap.mulLeft ℝ (mixingMatrix q))

theorem directional_pairing (Z W : Gradient) (q : Directions) :
    pairing (directional Z q) (rotated (directional W q) q) =
      ∑ a, ∑ b, q.val a * q.val b * pairing (Z a) (rotated (W b) q) := by
  let B := angularPairingLinear.compl₂ (rotatedLinear q)
  change B (∑ a, q.val a • Z a) (∑ b, q.val b • W b) =
    ∑ a, ∑ b, q.val a * q.val b * B (Z a) (W b)
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
    smul_eq_mul, Finset.mul_sum, mul_assoc]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

/-- The exact derivative mixed cancellation uses only symmetry and zero trace. -/
theorem integral_directional_pairing_zero (h : FollandMoments) (Z W : Gradient)
    (hZs : ∀ a, (Z a)ᵀ = Z a) (hZt : ∀ a, (Z a).trace = 0) :
    (∫ q, pairing (directional Z q) (rotated (directional W q) q) ∂sphereMeasure) = 0 := by
  have he : (fun q => pairing (directional Z q) (rotated (directional W q) q)) =
      fun q => ∑ a, ∑ b, q.val a * q.val b * pairing (Z a) (rotated (W b) q) :=
    funext (directional_pairing Z W)
  have hc (a b : Fin 4) : Continuous (fun q : Directions =>
      q.val a * q.val b * pairing (Z a) (rotated (W b) q)) := by
    simp only [pairing, rotated, Matrix.mul_apply, Matrix.transpose_apply]
    simp only [mixingMatrix, mixing, quadratic]
    fun_prop
  rw [he, integral_sum h _ (fun a => by fun_prop)]
  have hi (a : Fin 4) :
      (∫ q, ∑ b, q.val a * q.val b * pairing (Z a) (rotated (W b) q) ∂sphereMeasure) = 0 := by
    rw [integral_sum h _ (hc a)]
    simp_rw [integral_weighted_pairing_zero h _ _ (hZs a) (hZt a)]
    simp
  simp only [hi, Finset.sum_const_zero]

/-- The second exact angular energy identity used by the radial estimate. -/
theorem integral_normalDerivative_squareNorm_exact (h : FollandMoments) (Z W : Gradient)
    (hZs : ∀ a, (Z a)ᵀ = Z a) (hZt : ∀ a, (Z a).trace = 0) :
    (∫ q, squareNorm (normalDerivative Z W q) ∂sphereMeasure) =
      (gradientSquareNorm Z + gradientSquareNorm W) / 16 := by
  rw [integral_normalDerivative_squareNorm h,
    integral_directional_pairing_zero h Z W hZs hZt]
  ring

end

end PositiveEinsteinFour.Angular

end OAI
