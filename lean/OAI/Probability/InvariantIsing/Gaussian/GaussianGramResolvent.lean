import OAI.Probability.InvariantIsing.Gaussian.GaussianPatternModel
import Mathlib.LinearAlgebra.Matrix.PosDef

namespace OAI

/-! The positive real resolvent of the physical Gaussian Gram matrix. -/
noncomputable section
open Matrix
namespace InvariantIsing

def gaussianGramResolvent {N m : ℕ} (t : ℝ)
    (z : EuclideanSpace ℝ (Fin N × Fin m)) : Matrix (Fin N) (Fin N) ℝ :=
  (t • (1 : Matrix (Fin N) (Fin N) ℝ)+gaussianPatternCoupling 1 z)⁻¹

def gaussianGramStieltjes {N m : ℕ} (t : ℝ)
    (z : EuclideanSpace ℝ (Fin N × Fin m)) : ℝ := (gaussianGramResolvent t z).trace/N

lemma gaussianPatternCoupling_posSemidef {N m : ℕ} (z : EuclideanSpace ℝ (Fin N × Fin m)) :
    (gaussianPatternCoupling 1 z).PosSemidef := by
  have h := Matrix.posSemidef_self_mul_conjTranspose (gaussianPatternArray z)
  simpa only [gaussianPatternCoupling,Matrix.conjTranspose_eq_transpose_of_trivial] using
    h.smul (show 0 ≤ (1 : ℝ)/N by positivity)

lemma gaussianGramShift_posDef {N m : ℕ} {t : ℝ} (ht : 0 < t)
    (z : EuclideanSpace ℝ (Fin N × Fin m)) :
    (t • (1 : Matrix (Fin N) (Fin N) ℝ)+gaussianPatternCoupling 1 z).PosDef :=
  ((Matrix.PosDef.one).smul ht).add_posSemidef (gaussianPatternCoupling_posSemidef z)

lemma gaussianGramResolvent_posDef {N m : ℕ} {t : ℝ} (ht : 0 < t)
    (z : EuclideanSpace ℝ (Fin N × Fin m)) : (gaussianGramResolvent t z).PosDef :=
  (gaussianGramShift_posDef ht z).inv

lemma gaussianGramResolvent_identity {N m : ℕ} {t : ℝ} (ht : 0 < t)
    (z : EuclideanSpace ℝ (Fin N × Fin m)) :
    t • gaussianGramResolvent t z+gaussianPatternCoupling 1 z*gaussianGramResolvent t z = 1 := by
  have hd := (gaussianGramShift_posDef ht z).det_pos
  have h := Matrix.mul_nonsing_inv (t • (1 : Matrix (Fin N) (Fin N) ℝ)+gaussianPatternCoupling 1 z)
    (isUnit_iff_ne_zero.mpr hd.ne')
  simpa only [gaussianGramResolvent,add_mul,smul_mul_assoc,one_mul] using h

lemma gaussianGramResolvent_trace_identity {N m : ℕ} {t : ℝ} (ht : 0 < t)
    (z : EuclideanSpace ℝ (Fin N × Fin m)) :
    t*(gaussianGramResolvent t z).trace+
      (gaussianPatternCoupling 1 z*gaussianGramResolvent t z).trace = N := by
  have h := congrArg Matrix.trace (gaussianGramResolvent_identity ht z)
  simpa only [Matrix.trace_add,Matrix.trace_smul,smul_eq_mul,Matrix.trace_one,Fintype.card_fin] using h

lemma gaussianGramStieltjes_nonneg {N m : ℕ} {t : ℝ} (ht : 0 < t)
    (z : EuclideanSpace ℝ (Fin N × Fin m)) : 0 ≤ gaussianGramStieltjes t z :=
  div_nonneg (gaussianGramResolvent_posDef ht z).posSemidef.trace_nonneg (Nat.cast_nonneg N)

end InvariantIsing

end

end OAI
