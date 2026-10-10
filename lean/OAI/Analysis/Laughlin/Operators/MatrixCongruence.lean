import Mathlib.Algebra.Order.Star.Real
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic.NoncommRing

namespace OAI

namespace Laughlin.Certificate
open scoped Matrix

theorem compressed_congruence_identity {n : ℕ}
    (D Z Y K : Matrix (Fin n) (Fin n) ℝ) :
    (D*Z*D) * (K-D*Y*D) * (D*Z*D) =
      D * (Z * (D*K*D-(D*D)*Y*(D*D)) * Z) * D := by
  noncomm_ring

theorem compressed_congruence_positive {n : ℕ}
    (D Z Y K : Matrix (Fin n) (Fin n) ℝ) (hD : D.IsHermitian)
    (hM : (Z * (D*K*D-(D*D)*Y*(D*D)) * Z).PosSemidef) :
    ((D*Z*D) * (K-D*Y*D) * (D*Z*D)).PosSemidef := by
  rw [compressed_congruence_identity]
  simpa only [hD.eq] using hM.mul_mul_conjTranspose_same D

end Laughlin.Certificate

end OAI
