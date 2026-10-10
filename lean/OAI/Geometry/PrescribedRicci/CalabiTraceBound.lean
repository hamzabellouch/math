import Mathlib
import OAI.Geometry.PrescribedPotential.AnalyticSupport
import OAI.Geometry.PrescribedRicci.CalabiTensorBounds
import OAI.Geometry.PrescribedRicci.CalabiTrace
import OAI.Geometry.PrescribedRicci.HermitianCoercivity

namespace OAI

/-! Calabi Trace Bound. -/

noncomputable section
open Matrix Set Filter Topology
open scoped ComplexOrder ContDiff MatrixOrder Kronecker Matrix.Norms.Elementwise
namespace MongeAmpere
variable {n : Type*} [Fintype n] [DecidableEq n]
lemma flatTensor_inv {H : Matrix n n ℂ} (hH : H.PosDef) :
    (tensor3 H⁻¹.transpose H 1)⁻¹ = tensor3 H.transpose H⁻¹ 1 := by
  apply Matrix.inv_eq_right_inv
  rw [tensor3_mul,← Matrix.transpose_mul,
    Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hH.det_pos.ne'),
    Matrix.transpose_one,one_mul,tensor3_one]

lemma entrywise_norm_one_le : ‖(1 : Matrix n n ℂ)‖ ≤ 1 := by
  apply matrix_norm_le_of_entries zero_le_one
  intro i j
  simp only [Matrix.one_apply]
  split_ifs <;> simp

lemma flatTensor_inv_norm {H : Matrix n n ℂ} (hHp : H.PosDef) {M : ℝ}
    (hM : 0 ≤ M) (hH : ‖H‖ ≤ M) (hI : ‖H⁻¹‖ ≤ M) :
    ‖(tensor3 H⁻¹.transpose H 1)⁻¹‖ ≤ M^2 := by
  rw [flatTensor_inv hHp]
  apply (tensor3_norm_le _ _ _).trans
  rw [Matrix.norm_transpose]
  exact (mul_le_mul (mul_le_mul hH hI (norm_nonneg _) hM) entrywise_norm_one_le
    (norm_nonneg _) (mul_nonneg hM hM)).trans_eq (by ring)
end MongeAmpere
namespace Anticanonical.SourceSmooth.KaehlerMetric
open MongeAmpere
variable {d : ℕ} {X : Type*} [TopologicalSpace X] {A : ComplexAtlas d X}
local notation "TI" => TensorIndex (Fin d)

lemma calabiNorm_le_flatEnergy (g : KaehlerMetric A) (q : Fin A.count)
    {z : Coordinates d} (hz : z ∈ (A.chart q).target) {M : ℝ} (hM : 0 ≤ M)
    (hH : ‖g.matrix q z‖ ≤ M) (hI : ‖(g.matrix q z)⁻¹‖ ≤ M) :
    g.calabiNorm q z ≤ (Fintype.card TI:ℝ)^2*M^5*
      (hermPair (tensor3 (g.matrix q z)⁻¹.transpose (g.matrix q z) 1)
        (g.calabiTensor q z) (g.calabiTensor q z)).re := by
  let f := g.calabiTensor q z
  let K := tensor3 (g.matrix q z)⁻¹.transpose (g.matrix q z) 1
  have hK : K.PosDef := (g.positive q z hz).inv.transpose.kronecker
    ((g.positive q z hz).kronecker Matrix.PosDef.one)
  have hE : 0 ≤ (hermPair K f f).re := hermPair_nonneg hK.posSemidef _
  have hf : ‖f‖^2 ≤ M^2*(hermPair K f f).re := (norm_sq_le_hermPair hK f).trans
    (mul_le_mul_of_nonneg_right (flatTensor_inv_norm (g.positive q z hz) hM hH hI) hE)
  have hb : g.calabiNorm q z ≤ (Fintype.card TI:ℝ)^2*M^3*‖f‖^2 := by
    apply (Complex.re_le_norm (hermPair (g.calabiMetric q z) f f)).trans
    apply (pair_norm_le _ _ _).trans
    have hh := tensorMetric_norm_bound hM hH hI
    calc
      _ ≤ (Fintype.card TI:ℝ)^2*M^3*‖f‖*‖f‖ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hh (sq_nonneg _)) (norm_nonneg _)) (norm_nonneg _)
      _ = _ := by ring
  apply hb.trans
  calc
    _ ≤ (Fintype.card TI:ℝ)^2*M^3*(M^2*(hermPair K f f).re) :=
      mul_le_mul_of_nonneg_left hf (by positivity)
    _ = _ := by dsimp [K,f]; ring

lemma flatTrace_lower_bound (g : KaehlerMetric A) (q : Fin A.count)
    {z : Coordinates d} (hz : z ∈ (A.chart q).target) {M R : ℝ} (hM : 0 ≤ M)
    (hH : ‖g.matrix q z‖ ≤ M) (hI : ‖(g.matrix q z)⁻¹‖ ≤ M)
    (hR : ‖g.curvatureRicci q z‖ ≤ R) :
    (1+(Fintype.card TI:ℝ)^2*M^5)⁻¹*g.calabiNorm q z-(d:ℝ)*R ≤
      ((g.matrix q z)⁻¹*PotentialKaehler.potentialMatrix (g.flatTrace q) z).trace.re := by
  let E := (hermPair (tensor3 (g.matrix q z)⁻¹.transpose (g.matrix q z) 1)
    (g.calabiTensor q z) (g.calabiTensor q z)).re
  have hE : 0 ≤ E := hermPair_nonneg
    ((g.positive q z hz).inv.transpose.kronecker
      ((g.positive q z hz).kronecker Matrix.PosDef.one)).posSemidef _
  have hb := g.calabiNorm_le_flatEnergy q hz hM hH hI
  have hδ : 0 < 1+(Fintype.card TI:ℝ)^2*M^5 := by positivity
  have hS : (1+(Fintype.card TI:ℝ)^2*M^5)⁻¹*g.calabiNorm q z ≤ E := by
    rw [← div_eq_inv_mul,div_le_iff₀ hδ]
    change g.calabiNorm q z ≤ E*(1+(Fintype.card TI:ℝ)^2*M^5)
    change g.calabiNorm q z ≤ (Fintype.card TI:ℝ)^2*M^5*E at hb
    nlinarith
  have hRc : (g.curvatureRicci q z).trace.re ≤ (d:ℝ)*R := by
    apply (Complex.re_le_norm _).trans
    simpa only [Fintype.card_fin] using trace_entry_bound (fun i j =>
      (norm_entry_le_entrywise_sup_norm (g.curvatureRicci q z) (i:=i) (j:=j)).trans hR)
  rw [g.flatTrace_laplacian q hz]
  exact sub_le_sub hS hRc

lemma flatTrace_bound (g : KaehlerMetric A) (q : Fin A.count) (z : Coordinates d)
    {M : ℝ} (hH : ‖g.matrix q z‖ ≤ M) : g.flatTrace q z ≤ (d:ℝ)*M := by
  apply (Complex.re_le_norm _).trans
  simpa only [Fintype.card_fin] using trace_entry_bound (fun i j =>
    (norm_entry_le_entrywise_sup_norm (g.matrix q z) (i:=i) (j:=j)).trans hH)

end Anticanonical.SourceSmooth.KaehlerMetric

end

end OAI
