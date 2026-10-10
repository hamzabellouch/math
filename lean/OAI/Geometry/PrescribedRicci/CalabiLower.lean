import Mathlib
import OAI.Geometry.PrescribedRicci.CalabiBochner
import OAI.Geometry.PrescribedRicci.CalabiTensorBounds
import OAI.Geometry.PrescribedRicci.HermitianCoercivity
import OAI.Geometry.PrescribedRicci.MatrixWirtinger

namespace OAI

/-! Calabi Lower. -/

section

 
noncomputable section
open Matrix Set Filter Topology
open scoped ComplexOrder ContDiff MatrixOrder Matrix.Norms.Elementwise
namespace Anticanonical.SourceSmooth.KaehlerMetric
open MongeAmpere
variable {d : ℕ} {X : Type*} [TopologicalSpace X] {A : ComplexAtlas d X}
local notation "TI" => TensorIndex (Fin d)

lemma chernConnection_norm_le_calabiTensor (g : KaehlerMetric A) (q : Fin A.count)
    (z : Coordinates d) (a : Fin d) : ‖g.chernConnection q z a‖ ≤ ‖g.calabiTensor q z‖ := by
  apply matrix_norm_le_of_entries (norm_nonneg _)
  intro i j
  exact norm_le_pi_norm (g.calabiTensor q z) (a,i,j)

lemma calabiTensor_sq_bound (g : KaehlerMetric A) (q : Fin A.count)
    {z : Coordinates d} (hz : z ∈ (A.chart q).target) {M : ℝ} (hM : 0 ≤ M)
    (hH : ‖g.matrix q z‖ ≤ M) (hI : ‖(g.matrix q z)⁻¹‖ ≤ M) :
    ‖g.calabiTensor q z‖^2 ≤ M^3*g.calabiNorm q z := by
  exact (norm_sq_le_hermPair (g.calabiMetric_posDef q hz) _).trans
    (mul_le_mul_of_nonneg_right (tensorMetric_inv_norm_bound (g.positive q z hz) hM hH hI)
      (g.calabiNorm_nonneg q hz))

lemma calabiRoughTerm_bound (g : KaehlerMetric A) (q : Fin A.count) (z : Coordinates d)
    {M R : ℝ} (hM : 0 ≤ M) (hR : 0 ≤ R) (hI : ‖(g.matrix q z)⁻¹‖ ≤ M)
    (hRc : ‖g.curvatureRicci q z‖ ≤ R)
    (hDR : ∀ a, ‖holDerivative (g.curvatureRicci q) z a‖ ≤ R) :
    ‖g.calabiRoughTerm q z‖ ≤ (d:ℝ)*M*R+(d:ℝ)^2*M*R*‖g.calabiTensor q z‖ := by
  have hn : (0:ℝ) ≤ d := Nat.cast_nonneg _
  have hb : ‖(g.matrix q z)⁻¹*g.curvatureRicci q z‖ ≤ (d:ℝ)*M*R := by
    apply (matrix_norm_mul_le _ _).trans
    simp only [Fintype.card_fin]
    exact mul_le_mul (mul_le_mul_of_nonneg_left hI hn) hRc (norm_nonneg _) (by positivity)
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  change ‖(-(g.matrix q z)⁻¹*holDerivative (g.curvatureRicci q) z i.1+
    ((g.matrix q z)⁻¹*g.curvatureRicci q z)*g.chernConnection q z i.1) i.2.1 i.2.2‖ ≤ _
  apply (norm_entry_le_entrywise_sup_norm _).trans
  apply (norm_add_le _ _).trans
  have h1 : ‖-(g.matrix q z)⁻¹*holDerivative (g.curvatureRicci q) z i.1‖ ≤ (d:ℝ)*M*R := by
    rw [neg_mul,norm_neg]
    apply (matrix_norm_mul_le _ _).trans
    simp only [Fintype.card_fin]
    exact mul_le_mul (mul_le_mul_of_nonneg_left hI hn) (hDR i.1) (norm_nonneg _) (by positivity)
  have h2 : ‖((g.matrix q z)⁻¹*g.curvatureRicci q z)*g.chernConnection q z i.1‖ ≤
      (d:ℝ)^2*M*R*‖g.calabiTensor q z‖ := by
    apply (matrix_norm_mul_le _ _).trans
    simp only [Fintype.card_fin]
    calc
      _ ≤ (d:ℝ)*((d:ℝ)*M*R)*‖g.calabiTensor q z‖ :=
        mul_le_mul (mul_le_mul_of_nonneg_left hb hn)
          (g.chernConnection_norm_le_calabiTensor q z i.1) (norm_nonneg _) (by positivity)
      _ = _ := by ring
  exact add_le_add h1 h2

lemma tensorCurvature_bound (g : KaehlerMetric A) (q : Fin A.count) (z : Coordinates d)
    {M R : ℝ} (hM : 0 ≤ M) (_hR : 0 ≤ R) (hI : ‖(g.matrix q z)⁻¹‖ ≤ M)
    (hRc : ‖g.curvatureRicci q z‖ ≤ R) :
    ‖tensorConnection (-((g.matrix q z)⁻¹*g.curvatureRicci q z))‖ ≤ 3*(d:ℝ)*M*R := by
  apply (tensorConnection_norm_le _).trans
  rw [norm_neg]
  have h := matrix_norm_mul_le (g.matrix q z)⁻¹ (g.curvatureRicci q z)
  simp only [Fintype.card_fin] at h
  calc
    _ ≤ 3*((d:ℝ)*M*R) := mul_le_mul_of_nonneg_left
      (h.trans (mul_le_mul (mul_le_mul_of_nonneg_left hI (Nat.cast_nonneg _)) hRc
        (norm_nonneg _) (by positivity))) (by norm_num)
    _ = _ := by ring

 

theorem calabiNorm_lower_bound (d : ℕ) (M R : ℝ) (hM : 0 ≤ M) (hR : 0 ≤ R) :
    ∃ C : ℝ, 0 < C ∧ ∀ {X : Type*} [TopologicalSpace X] {A : ComplexAtlas d X}
      (g : KaehlerMetric A) (q : Fin A.count) (z : Coordinates d), z ∈ (A.chart q).target →
      ‖g.matrix q z‖ ≤ M → ‖(g.matrix q z)⁻¹‖ ≤ M → ‖g.curvatureRicci q z‖ ≤ R →
      (∀ a, ‖holDerivative (g.curvatureRicci q) z a‖ ≤ R) →
      g.calabiEnergy q z-C*(g.calabiNorm q z+1) ≤
        ((g.matrix q z)⁻¹*PotentialKaehler.potentialMatrix (g.calabiNorm q) z).trace.re := by
  let N : ℝ := Fintype.card (TensorIndex (Fin d))
  let A₀ := N^2*M^3*((d:ℝ)*M*R+(d:ℝ)^2*M*R)
  let B₀ := N^2*M^3*(N*(3*(d:ℝ)*M*R))
  have hN : 0 ≤ N := Nat.cast_nonneg _
  have hA : 0 ≤ A₀ := by dsimp [A₀]; positivity
  have hB : 0 ≤ B₀ := by dsimp [B₀]; positivity
  refine ⟨1+2*A₀*(1+2*M^3)+B₀*M^3,by positivity,?_⟩
  intro X _ A g q z hz hH hI hRc hDR
  let f := g.calabiTensor q z
  let S := g.calabiNorm q z
  have hS : 0 ≤ S := g.calabiNorm_nonneg q hz
  have hf : ‖f‖^2 ≤ M^3*S := g.calabiTensor_sq_bound q hz hM hH hI
  have hK : ‖g.calabiMetric q z‖ ≤ M^3 := tensorMetric_norm_bound hM hH hI
  have hr : ‖g.calabiRoughTerm q z‖ ≤ ((d:ℝ)*M*R+(d:ℝ)^2*M*R)*(1+‖f‖) := by
    apply (g.calabiRoughTerm_bound q z hM hR hI hRc hDR).trans
    dsimp [f]
    nlinarith [mul_nonneg (show 0 ≤ (d:ℝ)*M*R by positivity) (norm_nonneg (g.calabiTensor q z)),
      show (0:ℝ) ≤ (d:ℝ)^2*M*R by positivity]
  have hpair1 : ‖hermPair (g.calabiMetric q z) f (g.calabiRoughTerm q z)‖ ≤ A₀*(1+2*M^3*S) := by
    apply (pair_norm_le _ _ _).trans
    calc
      _ ≤ N^2*M^3*‖f‖*(((d:ℝ)*M*R+(d:ℝ)^2*M*R)*(1+‖f‖)) :=
        mul_le_mul (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hK (sq_nonneg N))
          (norm_nonneg f)) hr (norm_nonneg _) (by positivity)
      _ = A₀*(‖f‖+‖f‖^2) := by dsimp [A₀]; ring
      _ ≤ A₀*(1+2*M^3*S) := mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg (‖f‖-1)]) hA
  have ha : ‖tensorConnection (-((g.matrix q z)⁻¹*g.curvatureRicci q z))*ᵥ f‖ ≤
      N*(3*(d:ℝ)*M*R)*‖f‖ := by
    exact (mulVec_norm_le _ _).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (g.tensorCurvature_bound q z hM hR hI hRc) hN) (norm_nonneg f))
  have hpair2 : ‖hermPair (g.calabiMetric q z) f
      (tensorConnection (-((g.matrix q z)⁻¹*g.curvatureRicci q z))*ᵥ f)‖ ≤ B₀*M^3*S := by
    apply (pair_norm_le _ _ _).trans
    calc
      _ ≤ N^2*M^3*‖f‖*(N*(3*(d:ℝ)*M*R)*‖f‖) :=
        mul_le_mul (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hK (sq_nonneg N))
          (norm_nonneg f)) ha (norm_nonneg _) (by positivity)
      _ = B₀*‖f‖^2 := by dsimp [B₀]; ring
      _ ≤ B₀*(M^3*S) := mul_le_mul_of_nonneg_left hf hB
      _ = _ := by ring
  rw [g.calabiNorm_laplacian q hz]
  have hp1 := (abs_le.mp (Complex.abs_re_le_norm (hermPair (g.calabiMetric q z) f (g.calabiRoughTerm q z)))).1
  have hp2 := (abs_le.mp (Complex.abs_re_le_norm (hermPair (g.calabiMetric q z) f
    (tensorConnection (-((g.matrix q z)⁻¹*g.curvatureRicci q z))*ᵥ f)))).1
  change g.calabiEnergy q z-(1+2*A₀*(1+2*M^3)+B₀*M^3)*(S+1) ≤ _
  change _ ≤ g.calabiEnergy q z+2*(hermPair (g.calabiMetric q z) f (g.calabiRoughTerm q z)).re+
    (hermPair (g.calabiMetric q z) f (tensorConnection (-((g.matrix q z)⁻¹*g.curvatureRicci q z))*ᵥ f)).re
  nlinarith [mul_nonneg hA hS, mul_nonneg hB (pow_nonneg hM 3),
    mul_nonneg hA (pow_nonneg hM 3)]

end Anticanonical.SourceSmooth.KaehlerMetric

end
end

end OAI
