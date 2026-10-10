import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Algebra.Algebra.Rat

namespace OAI

/-! # The finite scalar ring used for universal nilpotent series -/

noncomputable section
namespace PolycyclicRecognition

abbrev TruncatedRationalScalars (c : ℕ) :=
  AdjoinRoot ((Polynomial.X : Polynomial ℚ) ^ (c + 1))

def truncatedScalarParameter (c : ℕ) : TruncatedRationalScalars c :=
  AdjoinRoot.root _

theorem truncatedScalarParameter_pow (c : ℕ) :
    truncatedScalarParameter c ^ (c + 1) = 0 := by
  simpa only [Polynomial.eval₂_pow, Polynomial.eval₂_X, truncatedScalarParameter] using
    AdjoinRoot.eval₂_root ((Polynomial.X : Polynomial ℚ) ^ (c + 1))

def truncatedScalarCoefficient (c k : ℕ) : TruncatedRationalScalars c →ₗ[ℚ] ℚ :=
  (Polynomial.lcoeff ℚ k).comp (AdjoinRoot.modByMonicHom (Polynomial.monic_X_pow (c + 1)))

theorem truncatedScalarCoefficient_parameter_pow (c j k : ℕ) (hj : j ≤ c) :
    truncatedScalarCoefficient c k (truncatedScalarParameter c ^ j) =
      if j = k then 1 else 0 := by
  change ((AdjoinRoot.modByMonicHom (Polynomial.monic_X_pow (c + 1)))
    (AdjoinRoot.root _ ^ j)).coeff k = _
  rw [AdjoinRoot.root, ← map_pow, AdjoinRoot.modByMonicHom_mk]
  have hd : (Polynomial.X ^ j : Polynomial ℚ).degree <
      (Polynomial.X ^ (c + 1) : Polynomial ℚ).degree := by
    simpa only [Polynomial.degree_X_pow, Nat.cast_lt] using Nat.lt_succ_of_le hj
  rw [(Polynomial.modByMonic_eq_self_iff (Polynomial.monic_X_pow (c + 1))).mpr hd]
  simpa only [eq_comm] using Polynomial.coeff_X_pow j k

end PolycyclicRecognition

end

end OAI
