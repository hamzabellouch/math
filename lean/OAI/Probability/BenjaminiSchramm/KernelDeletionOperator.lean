import OAI.Probability.BenjaminiSchramm.KernelDeletionDiagram
import OAI.Probability.UnimodularPercolation.Kernel.ContactTrace

namespace OAI

open MeasureTheory
open scoped ENNReal

namespace Percolation.BenjaminiSchramm

universe u v
variable {V : Type u} {E : Type v}
attribute [local instance] Classical.propDecidable Classical.decEq

theorem kernelTriangleDiagonal_eq_matrix [Countable E]
    (G : BondGraph V E) (p : unitInterval)
    (T K : Hilbert V →L[ℂ] Hilbert V) (hT : HasKernel G p T)
    (hK : PositiveRealMatrix K) (u : V) :
    kernelTriangleDiagonal G p (ennMatrixCoeff K) u =
      ennMatrixCoeff (T * (K * (T*T))) u u := by
  have ht := hT.positiveRealMatrix G p T
  rw [ennMatrixCoeff_mul ht (hK.mul (ht.mul ht))]
  apply tsum_congr
  intro a
  rw [ennMatrixCoeff_mul hK (ht.mul ht),←ENNReal.tsum_mul_left]
  apply tsum_congr
  intro b
  rw [ennMatrixCoeff_mul ht ht,←ENNReal.tsum_mul_left,←ENNReal.tsum_mul_left]
  apply tsum_congr
  intro z
  simp only [hT.ennMatrixCoeff G p T,connection_measure_symm G p u z]
  ring

theorem matrixCoeff_norm_le (A : Hilbert V →L[ℂ] Hilbert V) (x y : V) :
    ‖matrixCoeff A x y‖ ≤ ‖A‖ := by
  change ‖A (lp.single 2 y (1 : ℂ)) x‖ ≤ ‖A‖
  apply (lp.norm_apply_le_norm (by norm_num : (2 : ENNReal) ≠ 0)
    (A (lp.single 2 y (1 : ℂ))) x).trans
  simpa only [lp.norm_single (by norm_num : 0 < (2 : ENNReal)),norm_one,mul_one] using
    A.le_opNorm (lp.single 2 y (1 : ℂ))

theorem kernelTriangleDiagonal_norm_bound [Countable E]
    (G : BondGraph V E) (p : unitInterval)
    (T K : Hilbert V →L[ℂ] Hilbert V) (hT : HasKernel G p T)
    (hK : PositiveRealMatrix K) (u : V) :
    kernelTriangleDiagonal G p (ennMatrixCoeff K) u ≤ ENNReal.ofReal (‖T‖ ^ 3 * ‖K‖) := by
  rw [kernelTriangleDiagonal_eq_matrix G p T K hT hK u]
  apply ENNReal.ofReal_le_ofReal
  apply (Complex.re_le_norm _).trans ((matrixCoeff_norm_le _ u u).trans _)
  calc
    ‖T * (K * (T*T))‖ ≤ ‖T‖ * ‖K * (T*T)‖ := norm_mul_le _ _
    _ ≤ ‖T‖ * (‖K‖ * ‖T*T‖) :=
      mul_le_mul_of_nonneg_left (norm_mul_le _ _) (norm_nonneg _)
    _ ≤ ‖T‖ * (‖K‖ * (‖T‖ * ‖T‖)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (norm_mul_le _ _) (norm_nonneg _)) (norm_nonneg _)
    _ = _ := by ring

theorem connection_measure_mono [Countable V] [Countable E] (G : BondGraph V E) (x y : V)
    {p q : unitInterval} (hpq : p ≤ q) :
    law p {ω | Conn G ω x y} ≤ law q {ω | Conn G ω x y} := by
  apply (ENNReal.toReal_le_toReal (measure_ne_top _ _) (measure_ne_top _ _)).mp
  exact twoPoint_mono G x y hpq

theorem kernelTriangleDiagonal_mono [Countable V] [Countable E] (G : BondGraph V E)
    (K : V → V → ℝ≥0∞) (u : V) {p q : unitInterval} (hpq : p ≤ q) :
    kernelTriangleDiagonal G p K u ≤ kernelTriangleDiagonal G q K u := by
  apply ENNReal.tsum_le_tsum
  intro a
  apply ENNReal.tsum_le_tsum
  intro b
  apply ENNReal.tsum_le_tsum
  intro z
  exact mul_le_mul' (mul_le_mul'
    (mul_le_mul' (connection_measure_mono G u a hpq) le_rfl)
    (connection_measure_mono G b z hpq)) (connection_measure_mono G u z hpq)

theorem kernelDeletionDiagram_le_critical_norm [Countable V] [Countable E]
    (G : BondGraph V E) (T K : Hilbert V →L[ℂ] Hilbert V)
    (hT : HasKernel G (pc G) T) (hK : PositiveRealMatrix K)
    (p : unitInterval) (hp : p ≤ pc G) (x : V) :
    kernelDeletionDiagram G p (ennMatrixCoeff K) x ≤
      ENNReal.ofReal (‖T‖ ^ 3 * ‖K‖) * ∑' u, law p {ω | Conn G ω x u} := by
  apply kernelDeletionDiagram_bound
  intro u
  exact (kernelTriangleDiagonal_mono G (ennMatrixCoeff K) u hp).trans
    (kernelTriangleDiagonal_norm_bound G (pc G) T K hT hK u)

end Percolation.BenjaminiSchramm

end OAI
