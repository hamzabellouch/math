import Mathlib
import OAI.Geometry.PrescribedRicci.CalabiBochner
import OAI.Geometry.PrescribedRicci.CalabiLower
import OAI.Geometry.PrescribedRicci.CalabiTensorBounds
import OAI.Geometry.PrescribedRicci.TensorEnergyBounds

namespace OAI

/-! Calabi Gradient. -/

section

 

noncomputable section
open Matrix Set Filter Topology
open scoped ComplexOrder ContDiff MatrixOrder Matrix.Norms.Elementwise
namespace Anticanonical.SourceSmooth.KaehlerMetric
open MongeAmpere
variable {d : ℕ} {X : Type*} [TopologicalSpace X] {A : ComplexAtlas d X}
local notation "TI" => TensorIndex (Fin d)

lemma calabiNorm_hol (g : KaehlerMetric A) (q : Fin A.count)
    {z : Coordinates d} (hz : z ∈ (A.chart q).target) (a : Fin d) :
    holRealDeriv (g.calabiNorm q) z a =
      hermPair (g.calabiMetric q z) (barVector (g.calabiTensor q) z a) (g.calabiTensor q z)+
      hermPair (g.calabiMetric q z) (g.calabiTensor q z)
        (covHol (g.calabiConnection q) (g.calabiTensor q) z a) := by
  rw [← holDeriv_ofReal ((g.calabiNorm_smooth q hz).differentiableAt (by simp))]
  have he : (fun y => (g.calabiNorm q y : ℂ)) =ᶠ[nhds z]
      fun y => hermPair (g.calabiMetric q y) (g.calabiTensor q y) (g.calabiTensor q y) := by
    filter_upwards [(A.chart q).open_target.mem_nhds hz] with y hy
    exact hermPair_self_ofReal (g.calabiMetric_posDef q hy).isHermitian _
  rw [holDeriv_congr he]
  exact hermPair_hol_compatible (fun i j => (g.calabiMetric_smooth q hz i j).differentiableAt (by simp))
    (fun i => (g.calabiTensor_smooth q hz i).differentiableAt (by simp))
    (fun i => (g.calabiTensor_smooth q hz i).differentiableAt (by simp)) a (g.calabiMetric_hol q hz a)

lemma calabiDerivative_sq_bound (g : KaehlerMetric A) (q : Fin A.count)
    {z : Coordinates d} (hz : z ∈ (A.chart q).target) {M : ℝ} (hM : 0 ≤ M)
    (hH : ‖g.matrix q z‖ ≤ M) (hI : ‖(g.matrix q z)⁻¹‖ ≤ M) (a : Fin d) :
    ‖barVector (g.calabiTensor q) z a‖^2+
      ‖covHol (g.calabiConnection q) (g.calabiTensor q) z a‖^2 ≤ M^4*g.calabiEnergy q z := by
  have hi : ((g.matrix q z)⁻¹)⁻¹ = g.matrix q z := Matrix.inv_eq_right_inv
    (Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (g.positive q z hz).det_pos.ne'))
  have hiT : ((g.matrix q z)⁻¹.transpose)⁻¹ = (g.matrix q z).transpose := by
    rw [← Matrix.transpose_nonsing_inv,hi]
  have hki := tensorMetric_inv_norm_bound (g.positive q z hz) hM hH hI
  have h1 := vectorNorm_sq_le_tensorEnergy (g.positive q z hz).inv (g.calabiMetric_posDef q hz)
    (barVector (g.calabiTensor q) z) a
  have h2 := vectorNorm_sq_le_tensorEnergy (g.positive q z hz).inv.transpose (g.calabiMetric_posDef q hz)
    (covHol (g.calabiConnection q) (g.calabiTensor q) z) a
  rw [hi] at h1
  rw [hiT,Matrix.norm_transpose] at h2
  have hcoeff : ‖g.matrix q z‖*‖(g.calabiMetric q z)⁻¹‖ ≤ M^4 := by
    exact (mul_le_mul hH hki (norm_nonneg _) hM).trans_eq (by ring)
  have hp1 := tensorEnergy_nonneg (g.positive q z hz).inv.posSemidef
    (g.calabiMetric_posDef q hz).posSemidef (barVector (g.calabiTensor q) z)
  have hp2 := tensorEnergy_nonneg (g.positive q z hz).inv.transpose.posSemidef
    (g.calabiMetric_posDef q hz).posSemidef
      (covHol (g.calabiConnection q) (g.calabiTensor q) z)
  apply (add_le_add (h1.trans (mul_le_mul_of_nonneg_right hcoeff hp1))
    (h2.trans (mul_le_mul_of_nonneg_right hcoeff hp2))).trans_eq
  unfold calabiEnergy
  ring

lemma calabiNorm_gradient_sq_bound (g : KaehlerMetric A) (q : Fin A.count)
    {z : Coordinates d} (hz : z ∈ (A.chart q).target) {M : ℝ} (hM : 0 ≤ M)
    (hH : ‖g.matrix q z‖ ≤ M) (hI : ‖(g.matrix q z)⁻¹‖ ≤ M) (a : Fin d) :
    ‖holRealDeriv (g.calabiNorm q) z a‖^2 ≤
      2*(Fintype.card TI : ℝ)^4*M^13*g.calabiNorm q z*g.calabiEnergy q z := by
  let f := g.calabiTensor q z
  let u := barVector (g.calabiTensor q) z a
  let v := covHol (g.calabiConnection q) (g.calabiTensor q) z a
  let N : ℝ := Fintype.card TI
  have hK : ‖g.calabiMetric q z‖ ≤ M^3 := tensorMetric_norm_bound hM hH hI
  have hS := g.calabiNorm_nonneg q hz
  have hE := g.calabiEnergy_nonneg q hz
  have hf := g.calabiTensor_sq_bound q hz hM hH hI
  have hd := g.calabiDerivative_sq_bound q hz hM hH hI a
  have hb : ‖holRealDeriv (g.calabiNorm q) z a‖ ≤ N^2*M^3*‖f‖*(‖u‖+‖v‖) := by
    rw [g.calabiNorm_hol q hz]
    apply (norm_add_le _ _).trans
    have hp1 := (pair_norm_le (g.calabiMetric q z) u f).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hK (sq_nonneg N)) (norm_nonneg u)) (norm_nonneg f))
    have hp2 := (pair_norm_le (g.calabiMetric q z) f v).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hK (sq_nonneg N)) (norm_nonneg f)) (norm_nonneg v))
    exact (add_le_add hp1 hp2).trans_eq (by ring)
  have hsq := (sq_le_sq₀ (norm_nonneg _) (show 0 ≤ N^2*M^3*‖f‖*(‖u‖+‖v‖) by positivity)).mpr hb
  have huv : (‖u‖+‖v‖)^2 ≤ 2*(‖u‖^2+‖v‖^2) := by nlinarith [sq_nonneg (‖u‖-‖v‖)]
  calc
    _ ≤ (N^2*M^3*‖f‖*(‖u‖+‖v‖))^2 := hsq
    _ = N^4*M^6*‖f‖^2*(‖u‖+‖v‖)^2 := by ring
    _ ≤ N^4*M^6*(M^3*g.calabiNorm q z)*(2*(M^4*g.calabiEnergy q z)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hf (by positivity))
        (huv.trans (mul_le_mul_of_nonneg_left hd (by norm_num))) (sq_nonneg _) (by positivity)
    _ = _ := by dsimp [N]; ring

end Anticanonical.SourceSmooth.KaehlerMetric

end
end

end OAI
