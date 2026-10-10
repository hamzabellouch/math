import OAI.GroupTheory.PolycyclicRecognition.Geometry.DominantEigenlineContraction
import Mathlib.Analysis.Normed.Operator.Basic

namespace OAI

/-! # Transversality bounds for eigenline cones

Closeness to one line bounds both the norm and evaluation by any functional
which does not vanish on that line. These bounds supply the uniform input
cones for the dominant-eigenline contraction theorem.
-/

noncomputable section
namespace PolycyclicRecognition

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem eigenline_cone_norm_bound (ψ : V →L[ℝ] ℝ) (w x : V) (ε : ℝ)
    (hx : ‖eigenlineRemainder ψ w x‖ ≤ ε * |ψ x|) :
    ‖x‖ ≤ (‖w‖ + ε) * |ψ x| := by
  have he : x = eigenlineRemainder ψ w x + ψ x • w := by
    simp only [eigenlineRemainder, sub_add_cancel]
  calc
    ‖x‖ = ‖eigenlineRemainder ψ w x + ψ x • w‖ := congrArg norm he
    _ ≤ ‖eigenlineRemainder ψ w x‖ + ‖ψ x • w‖ := norm_add_le _ _
    _ ≤ ε * |ψ x| + |ψ x| * ‖w‖ := by
      rw [norm_smul, Real.norm_eq_abs]
      linarith only [hx]
    _ = (‖w‖ + ε) * |ψ x| := by ring

theorem eigenline_cone_functional_lower (ψ θ : V →L[ℝ] ℝ) (w x : V) (ε : ℝ)
    (hx : ‖eigenlineRemainder ψ w x‖ ≤ ε * |ψ x|) :
    (|θ w| - ‖θ‖ * ε) * |ψ x| ≤ |θ x| := by
  have he : θ x - ψ x * θ w = θ (eigenlineRemainder ψ w x) := by
    simp [eigenlineRemainder]
  have hbound : |θ x - ψ x * θ w| ≤ (‖θ‖ * ε) * |ψ x| := by
    rw [he]
    calc
      |θ (eigenlineRemainder ψ w x)| = ‖θ (eigenlineRemainder ψ w x)‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖θ‖ * ‖eigenlineRemainder ψ w x‖ := θ.le_opNorm _
      _ ≤ ‖θ‖ * (ε * |ψ x|) := mul_le_mul_of_nonneg_left hx (norm_nonneg _)
      _ = _ := by ring
  have htri := abs_sub_abs_le_abs_sub (ψ x * θ w) (θ x)
  rw [abs_sub_comm, abs_mul] at htri
  nlinarith

theorem eigenline_cone_transverse_bound (ψ θ : V →L[ℝ] ℝ) (w x : V) (ε : ℝ)
    (hε : 0 ≤ ε) (hgap : ‖θ‖ * ε < |θ w|)
    (hx : ‖eigenlineRemainder ψ w x‖ ≤ ε * |ψ x|) :
    ‖x‖ ≤ ((‖w‖ + ε) / (|θ w| - ‖θ‖ * ε)) * |θ x| := by
  have hg : 0 < |θ w| - ‖θ‖ * ε := sub_pos.mpr hgap
  have hc : 0 ≤ ‖w‖ + ε := add_nonneg (norm_nonneg _) hε
  have hf := eigenline_cone_functional_lower ψ θ w x ε hx
  calc
    ‖x‖ ≤ (‖w‖ + ε) * |ψ x| := eigenline_cone_norm_bound ψ w x ε hx
    _ ≤ (‖w‖ + ε) * (|θ x| / (|θ w| - ‖θ‖ * ε)) :=
      mul_le_mul_of_nonneg_left ((le_div_iff₀ hg).mpr (by nlinarith [hf])) hc
    _ = _ := by ring

end PolycyclicRecognition

end

end OAI
