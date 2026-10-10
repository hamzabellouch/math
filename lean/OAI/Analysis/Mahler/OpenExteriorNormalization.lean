import OAI.Analysis.Mahler.MatrixExteriorPower
import OAI.Analysis.Mahler.LevelForms

namespace OAI

open Complex
open scoped BigOperators

namespace Mahler

noncomputable def coordinateDirection {n : ℕ} (i : Fin n) : ComplexEuclidean n :=
  EuclideanSpace.single i 1

lemma linearMap_coordinate_expansion {n : ℕ} (A : ComplexEuclidean n →L[ℂ] ℂ)
    (v : ComplexEuclidean n) : A v = ∑ i, v i * A (coordinateDirection i) := by
  have hv : v = ∑ i, v i • coordinateDirection i := by
    ext j
    simp [coordinateDirection, Pi.single_apply]
  conv_lhs => rw [hv, map_sum]
  simp [map_smul, smul_eq_mul]

lemma pairing_coordinate_expansion {n : ℕ} {J : Type*} [Fintype J]
    (A : J → ComplexEuclidean n →L[ℂ] ℂ) (w v : ComplexEuclidean n) :
    pairing (fun j => A j w) (fun j => A j v) =
      matrixPairing (fun i j => pairing (fun a => A a (coordinateDirection j))
        (fun a => A a (coordinateDirection i))) w v := by
  have he (z : ComplexEuclidean n) : (fun j => A j z) =
      (fun j => ∑ i, z i * A j (coordinateDirection i)) :=
    funext (fun j => linearMap_coordinate_expansion (A j) z)
  rw [he w, he v, pairing_sum_left]
  simp_rw [pairing_mul_left, pairing_sum_right, pairing_mul_right, Finset.mul_sum]
  rw [Finset.sum_comm]
  unfold matrixPairing
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [show (starRingEnd ℂ) (w j) = star (w j) from rfl]
  ring

lemma logKernel_coordinate_expansion {n : ℕ} {J : Type*} [Fintype J]
    (a : J → ℂ) (A : J → ComplexEuclidean n →L[ℂ] ℂ) (w v : ComplexEuclidean n) :
    logKernel a (fun j => A j w) (fun j => A j v) =
      matrixPairing (fun i j => logKernel a (fun b => A b (coordinateDirection j))
        (fun b => A b (coordinateDirection i))) w v := by
  have he (z : ComplexEuclidean n) : (fun j => A j z) =
      (fun j => ∑ i, z i * A j (coordinateDirection i)) :=
    funext (fun j => linearMap_coordinate_expansion (A j) z)
  rw [he w, he v, logKernel_sum_left]
  simp_rw [logKernel_mul_left, logKernel_sum_right, logKernel_mul_right, Finset.mul_sum]
  rw [Finset.sum_comm]
  unfold matrixPairing
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [show (starRingEnd ℂ) (w j) = star (w j) from rfl]
  ring

variable {n : ℕ} {J : Type*} [Fintype J] {f : J → ComplexEuclidean n → ℂ}
  {U : Set (ComplexEuclidean n)} {x : ComplexEuclidean n}

lemma extDeriv_energy_matrix_of_open (hU : IsOpen U) (hx : x ∈ U)
    (hf : ∀ j, DifferentiableOn ℂ (f j) U) :
    (extDeriv (oneForm (dcLinear (energy f))) x).toAlternatingMap =
      matrixTwoForm (sourceHessian (energy f) x coordinateDirection) := by
  have hmat : sourceHessian (energy f) x coordinateDirection =
      (fun i j => pairing (fun a => fderiv ℂ (f a) x (coordinateDirection j))
        (fun a => fderiv ℂ (f a) x (coordinateDirection i))) := by
    ext i j
    exact mixed_energy_of_open hU hx hf
  ext v
  have hv : v = ![v 0,v 1] := by ext i; fin_cases i <;> rfl
  change extDeriv (oneForm (dcLinear (energy f))) x v = _
  rw [hv, extDeriv_dc_mixed (contDiffAt_energy_of_open hU hx hf), matrixTwoForm_apply, hmat,
    mixed_energy_of_open hU hx hf, mixed_energy_of_open hU hx hf]
  change (I/2) * (pairing (fun j => fderiv ℂ (f j) x (v 1)) (fun j => fderiv ℂ (f j) x (v 0)) -
    pairing (fun j => fderiv ℂ (f j) x (v 0)) (fun j => fderiv ℂ (f j) x (v 1))) = _
  rw [pairing_coordinate_expansion, pairing_coordinate_expansion]

lemma extDeriv_logTau_matrix_of_open (hU : IsOpen U) (hx : x ∈ U)
    (hf : ∀ j, DifferentiableOn ℂ (f j) U) (ht : 0 < tau f x) :
    (extDeriv (oneForm (dcLinear (logTau f))) x).toAlternatingMap =
      matrixTwoForm (sourceHessian (logTau f) x coordinateDirection) := by
  have hmat : sourceHessian (logTau f) x coordinateDirection =
      (fun i j => logKernel (fun a => f a x)
        (fun a => fderiv ℂ (f a) x (coordinateDirection j))
        (fun a => fderiv ℂ (f a) x (coordinateDirection i))) := by
    ext i j
    exact mixed_logTau_of_open hU hx hf ht
  ext v
  have hv : v = ![v 0,v 1] := by ext i; fin_cases i <;> rfl
  change extDeriv (oneForm (dcLinear (logTau f))) x v = _
  rw [hv, extDeriv_dc_logTau_of_open hU hx hf ht, matrixTwoForm_apply, hmat,
    logKernel_coordinate_expansion, logKernel_coordinate_expansion]

/-- The top exterior normalization, under
open-domain first-order holomorphicity, with no additional smoothness premise. -/
theorem extDeriv_energy_top_of_open (hU : IsOpen U) (hx : x ∈ U)
    (hf : ∀ j, DifferentiableOn ℂ (f j) U) :
    wedgePower (extDeriv (oneForm (dcLinear (energy f))) x).toAlternatingMap n =
      ((n.factorial : ℂ) * (sourceHessian (energy f) x coordinateDirection).det) • interleavedVolume n := by
  rw [extDeriv_energy_matrix_of_open hU hx hf, matrixTwoForm_top]

theorem extDeriv_logTau_top_of_open (hU : IsOpen U) (hx : x ∈ U)
    (hf : ∀ j, DifferentiableOn ℂ (f j) U) (ht : 0 < tau f x) :
    wedgePower (extDeriv (oneForm (dcLinear (logTau f))) x).toAlternatingMap n =
      ((n.factorial : ℂ) * (sourceHessian (logTau f) x coordinateDirection).det) • interleavedVolume n := by
  rw [extDeriv_logTau_matrix_of_open hU hx hf ht, matrixTwoForm_top]

/-- The density already used by the exact mass target is the real coefficient
of the actual top exterior form in the positive Euclidean coordinate frame. -/
theorem MassHypotheses.massDensity_eq_topForm {N m : ℕ}
    {f : Fin N → ComplexEuclidean n → ℂ} {G : Fin N → MvPolynomial (Fin n) ℂ}
    (h : MassHypotheses n N m U f G) (hx : x ∈ U) :
    massDensity f x =
      (wedgePower (extDeriv (oneForm (dcLinear (energy f))) x).toAlternatingMap n
        interleavedBasis).re := by
  rw [extDeriv_energy_top_of_open h.open_domain hx h.holomorphic]
  simp only [AlternatingMap.smul_apply, smul_eq_mul, interleavedVolume_basis, mul_one]
  simp only [massDensity, Complex.mul_re, Complex.natCast_re, Complex.natCast_im, zero_mul, sub_zero]
  rfl

end Mahler

end OAI
