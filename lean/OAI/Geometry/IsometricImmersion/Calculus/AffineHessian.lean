import OAI.Geometry.IsometricImmersion.Coordinates.AffinePullback
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

namespace OAI

noncomputable section
open scoped ContDiff Topology BigOperators Matrix
open Filter

namespace SmoothLocal.Geometry

theorem matrix_column_basis_expansion (R : Matrix (Fin 2) (Fin 2) ℝ) (i : Fin 2) :
    R *ᵥ Pi.single i (1 : ℝ) =
      R 0 i • Pi.single 0 (1 : ℝ) + R 1 i • Pi.single 1 (1 : ℝ) := by
  rw [Matrix.mulVec_single_one]
  funext k
  fin_cases k <;> simp

def bilinearMatrix (B : Coord →L[ℝ] Coord →L[ℝ] ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  fun a k => B (Pi.single a 1) (Pi.single k 1)

theorem bilinear_matrix_congruence (B : Coord →L[ℝ] Coord →L[ℝ] ℝ)
    (R : Matrix (Fin 2) (Fin 2) ℝ) (i j : Fin 2) :
    B (R *ᵥ Pi.single i 1) (R *ᵥ Pi.single j 1) =
      (Rᵀ * bilinearMatrix B * R) i j := by
  rw [matrix_column_basis_expansion R i, matrix_column_basis_expansion R j]
  simp only [map_add, map_smul, add_apply,
    smul_apply, smul_eq_mul,
    Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_two, bilinearMatrix]
  ring

theorem second_coordPartial_affine_comp {z : Coord → ℝ} {U : Set Coord}
    (hz : ContDiffOn ℝ ∞ z U) (hU : IsOpen U)
    (b : Coord) (R : Matrix (Fin 2) (Fin 2) ℝ) (q : Coord)
    (hq : affineCoordinates b R q ∈ U) (i j : Fin 2) :
    coordPartial i (coordPartial j (z ∘ affineCoordinates b R)) q =
      fderiv ℝ (fderiv ℝ z) (affineCoordinates b R q)
        (R *ᵥ Pi.single i 1) (R *ᵥ Pi.single j 1) := by
  have hV := isOpen_affine_preimage hU b R
  have heq : coordPartial j (z ∘ affineCoordinates b R) =ᶠ[𝓝 q]
      (fun p => fderiv ℝ z (affineCoordinates b R p) (R *ᵥ Pi.single j 1)) := by
    filter_upwards [hV.mem_nhds hq] with p hp
    exact fderiv_affine_comp_apply b R p (Pi.single j 1)
      (((hz _ hp).contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp))
  have hs : ContDiffOn ℝ ∞ (fderiv ℝ z) U := hz.fderiv_of_isOpen hU (by simp)
  have hd : DifferentiableAt ℝ (fderiv ℝ z) (affineCoordinates b R q) :=
    (((hs _ hq).contDiffAt (hU.mem_nhds hq)).differentiableAt (by simp))
  have hdc : DifferentiableAt ℝ
      (fun p => fderiv ℝ z (affineCoordinates b R p)) q :=
    hd.comp q (affineCoordinates_hasFDerivAt b R q).differentiableAt
  have heval : coordPartial i (coordPartial j (z ∘ affineCoordinates b R)) q =
      fderiv ℝ (fun p => fderiv ℝ z (affineCoordinates b R p)) q
        (Pi.single i 1) (R *ᵥ Pi.single j 1) := by
    change fderiv ℝ (coordPartial j (z ∘ affineCoordinates b R)) q (Pi.single i 1) = _
    rw [heq.fderiv_eq, fderiv_clm_apply hdc
      (differentiableAt_const (c := R *ᵥ Pi.single j (1 : ℝ)))]
    simp
  rw [heval]
  exact congrArg (fun L : Coord →L[ℝ] ℝ => L (R *ᵥ Pi.single j 1))
    (fderiv_affine_comp_apply b R q (Pi.single i 1) hd)

theorem fderiv_affine_comp_eq_zero {z : Coord → ℝ}
    (b : Coord) (R : Matrix (Fin 2) (Fin 2) ℝ) (q : Coord)
    (hz : DifferentiableAt ℝ z (affineCoordinates b R q))
    (hcrit : fderiv ℝ z (affineCoordinates b R q) = 0) :
    fderiv ℝ (z ∘ affineCoordinates b R) q = 0 := by
  apply ContinuousLinearMap.ext
  intro v
  rw [fderiv_affine_comp_apply b R q v hz, hcrit]
  rfl

theorem covHessian_eq_secondFDeriv_at_critical (g : MetricField) {z : Coord → ℝ}
    {U : Set Coord} (hz : ContDiffOn ℝ ∞ z U) (hU : IsOpen U) {p : Coord}
    (hp : p ∈ U) (hcrit : fderiv ℝ z p = 0) :
    covHessian g z p =
      (fun i j => fderiv ℝ (fderiv ℝ z) p (Pi.single i 1) (Pi.single j 1)) := by
  have hdz (k : Fin 2) : coordPartial k z p = 0 := by simp [coordPartial, hcrit]
  ext i j
  simp only [covHessian, hdz, mul_zero, Finset.sum_const_zero, sub_zero]
  exact second_coordPartial_eq_fderiv hz hU hp i j

theorem covHessian_affinePullback_at_critical (g : MetricField) {z : Coord → ℝ}
    {U : Set Coord} (hz : ContDiffOn ℝ ∞ z U) (hU : IsOpen U)
    (b : Coord) (R : Matrix (Fin 2) (Fin 2) ℝ) (q : Coord)
    (hq : affineCoordinates b R q ∈ U)
    (hcrit : fderiv ℝ z (affineCoordinates b R q) = 0) :
    covHessian (affinePullbackMetric g b R) (z ∘ affineCoordinates b R) q =
      Rᵀ * covHessian g z (affineCoordinates b R q) * R := by
  have hzq : DifferentiableAt ℝ z (affineCoordinates b R q) :=
    (((hz _ hq).contDiffAt (hU.mem_nhds hq)).differentiableAt (by simp))
  have hcrit' := fderiv_affine_comp_eq_zero b R q hzq hcrit
  have hdz (k : Fin 2) : coordPartial k (z ∘ affineCoordinates b R) q = 0 := by
    simp [coordPartial, hcrit']
  rw [covHessian_eq_secondFDeriv_at_critical g hz hU hq hcrit]
  ext i j
  simp only [covHessian, hdz, mul_zero, Finset.sum_const_zero, sub_zero]
  rw [second_coordPartial_affine_comp hz hU b R q hq i j]
  exact bilinear_matrix_congruence (fderiv ℝ (fderiv ℝ z) (affineCoordinates b R q)) R i j

theorem covHessian_affinePullback_at_zero (g : MetricField) {z : Coord → ℝ}
    {U : Set Coord} (hz : ContDiffOn ℝ ∞ z U) (hU : IsOpen U)
    (b : Coord) (R : Matrix (Fin 2) (Fin 2) ℝ) (hb : b ∈ U)
    (hcrit : fderiv ℝ z b = 0) :
    covHessian (affinePullbackMetric g b R) (z ∘ affineCoordinates b R) 0 =
      Rᵀ * covHessian g z b * R := by
  simpa only [affineCoordinates_zero] using
    covHessian_affinePullback_at_critical g hz hU b R 0
      (by simpa only [affineCoordinates_zero] using hb)
      (by simpa only [affineCoordinates_zero] using hcrit)

end SmoothLocal.Geometry

end

end OAI
