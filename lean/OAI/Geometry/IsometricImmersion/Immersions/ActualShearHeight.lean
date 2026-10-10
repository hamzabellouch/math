import OAI.Geometry.IsometricImmersion.Pulses.PulseCurvaturePrincipal
import OAI.Geometry.IsometricImmersion.Darboux.QPrincipal
import OAI.Geometry.IsometricImmersion.Calculus.AffineCovariantHessian

namespace OAI

noncomputable section
open Set
open scoped ContDiff Matrix

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry SmoothLocal.HighEquation

def heightInShearCoordinates (z : Coord → ℝ) (q0 : ℝ) : Coord → ℝ :=
  z ∘ inverseShearCoordinates q0

theorem heightInShearCoordinates_contDiffOn {z : Coord → ℝ} {U : Set Coord}
    (hz : ContDiffOn ℝ ∞ z U) (q0 : ℝ) :
    ContDiffOn ℝ ∞ (heightInShearCoordinates z q0) (inverseShearCoordinates q0 ⁻¹' U) :=
  hz.comp (inverseShearCoordinates_contDiff q0).contDiffOn (fun _ hp => hp)

theorem covHessian_in_shear_coordinates {g : MetricField} {z : Coord → ℝ}
    {U : Set Coord} (hg : SmoothPositiveOn g U) (hz : ContDiffOn ℝ ∞ z U)
    (hU : IsOpen U) (q0 : ℝ) {p : Coord} (hp : inverseShearCoordinates q0 p ∈ U) :
    covHessian (metricInShearCoordinates g q0) (heightInShearCoordinates z q0) p =
      (inverseShearMatrix q0)ᵀ * covHessian g z (inverseShearCoordinates q0 p) *
        inverseShearMatrix q0 := by
  simpa only [metricInShearCoordinates, heightInShearCoordinates,
    inverseShearCoordinates_eq_affine] using
    covHessian_affinePullback hg hz hU 0 (inverseShearMatrix q0)
      (inverseShearMatrix_isUnit q0) p (by simpa only [← inverseShearCoordinates_eq_affine] using hp)

theorem covHessian_shear_entries {g : MetricField} {z : Coord → ℝ}
    {U : Set Coord} (hg : SmoothPositiveOn g U) (hz : ContDiffOn ℝ ∞ z U)
    (hU : IsOpen U) (q0 : ℝ) {p : Coord} (hp : inverseShearCoordinates q0 p ∈ U) :
    let H := covHessian g z (inverseShearCoordinates q0 p)
    let S := covHessian (metricInShearCoordinates g q0) (heightInShearCoordinates z q0) p
    S 1 1 = H 1 1 ∧ S 0 1 = H 0 1 - q0 * H 1 1 ∧
      S 0 0 = H 0 0 - 2 * q0 * H 0 1 + q0 ^ 2 * H 1 1 := by
  dsimp only
  rw [covHessian_in_shear_coordinates hg hz hU q0 hp]
  simp only [inverseShearMatrix, Matrix.mul_apply, Matrix.transpose_apply,
    Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [covHessian_symm hg hU hz hp 1 0]
  constructor
  · ring
  constructor <;> ring

theorem heightEnergy_in_shear_coordinates {g : MetricField} {z : Coord → ℝ}
    {U : Set Coord} (hz : ContDiffOn ℝ ∞ z U) (hU : IsOpen U)
    (q0 : ℝ) {p : Coord} (hp : inverseShearCoordinates q0 p ∈ U) :
    heightEnergy (metricInShearCoordinates g q0) (heightInShearCoordinates z q0) p =
      heightEnergy g z (inverseShearCoordinates q0 p) := by
  have hd := (hz.contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)
  simpa only [metricInShearCoordinates, heightInShearCoordinates,
    ← inverseShearCoordinates_eq_affine, inverseShearMatrix_det, one_pow, one_mul] using
    heightEnergy_affinePullback (g := g) 0 (inverseShearMatrix q0)
      (inverseShearMatrix_isUnit q0) p
      (by simpa only [← inverseShearCoordinates_eq_affine] using hd)

theorem hessianQuotient_in_shear_coordinates {g : MetricField} {z : Coord → ℝ}
    {U : Set Coord} (hg : SmoothPositiveOn g U) (hz : ContDiffOn ℝ ∞ z U)
    (hU : IsOpen U) (q0 : ℝ) {p : Coord} (hp : inverseShearCoordinates q0 p ∈ U)
    (hyy : covHessian g z (inverseShearCoordinates q0 p) 1 1 ≠ 0) :
    hessianQuotient (metricInShearCoordinates g q0) (heightInShearCoordinates z q0) p =
      hessianQuotient g z (inverseShearCoordinates q0 p) - q0 := by
  obtain ⟨h11, h01, h00⟩ := covHessian_shear_entries hg hz hU q0 hp
  unfold hessianQuotient
  rw [h01, h11]
  field_simp [hyy]

theorem sheared_Hxx_factor {g : MetricField} {z : Coord → ℝ}
    {U : Set Coord} (hg : SmoothPositiveOn g U) (hz : ContDiffOn ℝ ∞ z U)
    (hU : IsOpen U) (q0 : ℝ) {p : Coord} (hp : inverseShearCoordinates q0 p ∈ U)
    (hyy : covHessian g z (inverseShearCoordinates q0 p) 1 1 ≠ 0)
    (hD : (covHessian g z (inverseShearCoordinates q0 p)).det =
      gaussianCurvature g (inverseShearCoordinates q0 p) *
        heightEnergy g z (inverseShearCoordinates q0 p)) :
    covHessian (metricInShearCoordinates g q0) (heightInShearCoordinates z q0) p 0 0 =
      ((hessianQuotient g z (inverseShearCoordinates q0 p) - q0)^2 +
        gaussianCurvature g (inverseShearCoordinates q0 p) *
          darbouxG g z (inverseShearCoordinates q0 p)) *
            covHessian g z (inverseShearCoordinates q0 p) 1 1 := by
  have hratio := hessian_time_ratio hg hU hz hp hyy hD
  obtain ⟨h11, h01, h00⟩ := covHessian_shear_entries hg hz hU q0 hp
  rw [h00]
  have hf : covHessian g z (inverseShearCoordinates q0 p) 0 0 =
      ((hessianQuotient g z (inverseShearCoordinates q0 p))^2 +
        gaussianCurvature g (inverseShearCoordinates q0 p) *
          darbouxG g z (inverseShearCoordinates q0 p)) *
            covHessian g z (inverseShearCoordinates q0 p) 1 1 := by
    rw [hratio, div_mul_cancel₀ _ hyy]
  rw [hf]
  unfold hessianQuotient
  field_simp [hyy]
  ring

end SmoothLocal.Pulse

end

end OAI
