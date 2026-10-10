import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint

namespace OAI

noncomputable section
namespace FiniteFactor
open scoped Topology
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A concrete finite tracial von Neumann algebra in a faithful vector-trace
representation. These are operator-algebra data, without approximation assumptions. -/
structure TracialRepresentation (M : VonNeumannAlgebra H) where
  vector : H
  norm_vector : ‖vector‖ = 1
  cyclic : ∀ S T : M.toStarSubalgebra,
    inner ℂ vector ((S : H →L[ℂ] H) ((T : H →L[ℂ] H) vector)) =
    inner ℂ vector ((T : H →L[ℂ] H) ((S : H →L[ℂ] H) vector))
  separating : ∀ T : M.toStarSubalgebra, (T : H →L[ℂ] H) vector = 0 → T = 0

namespace TracialRepresentation
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)
abbrev Algebra := M.toStarSubalgebra

def trace (T : Algebra (M := M)) : ℂ := inner ℂ τ.vector ((T : H →L[ℂ] H) τ.vector)
def norm₂ (T : Algebra (M := M)) : ℝ := ‖(T : H →L[ℂ] H) τ.vector‖

@[simp] theorem trace_one : τ.trace 1 = 1 := by
  simp [trace, inner_self_eq_norm_sq_to_K, τ.norm_vector]

theorem trace_mul_comm (S T : Algebra (M := M)) : τ.trace (S*T) = τ.trace (T*S) :=
  τ.cyclic S T

theorem trace_star_mul (T : Algebra (M := M)) :
    τ.trace (star T*T) = (τ.norm₂ T : ℂ)^2 := by
  unfold trace norm₂
  change inner ℂ τ.vector ((star (T : H →L[ℂ] H)) ((T : H →L[ℂ] H) τ.vector)) = _
  rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right, inner_self_eq_norm_sq_to_K]
  norm_cast

theorem norm₂_star (T : Algebra (M := M)) : τ.norm₂ (star T) = τ.norm₂ T := by
  have h := τ.trace_mul_comm (star T) T
  have h2 := τ.trace_star_mul (star T)
  simp only [star_star] at h2
  rw [τ.trace_star_mul, h2] at h
  have hr := congrArg Complex.re h
  simp only [← Complex.ofReal_pow, Complex.ofReal_re] at hr
  have hn : 0 ≤ τ.norm₂ T := norm_nonneg _
  have hs : 0 ≤ τ.norm₂ (star T) := norm_nonneg _
  nlinarith

@[simp] theorem norm₂_zero : τ.norm₂ 0 = 0 := by simp [norm₂]
@[simp] theorem norm₂_sub (S T : Algebra (M := M)) :
    τ.norm₂ (S-T) = ‖(S : H →L[ℂ] H) τ.vector - (T : H →L[ℂ] H) τ.vector‖ := rfl

theorem norm₂_add_le (S T : Algebra (M := M)) : τ.norm₂ (S+T) ≤ τ.norm₂ S+τ.norm₂ T :=
  norm_add_le _ _

theorem norm₂_smul (c : ℂ) (T : Algebra (M := M)) : τ.norm₂ (c • T) = ‖c‖*τ.norm₂ T :=
  norm_smul _ _

theorem norm₂_mul_le (S T : Algebra (M := M)) : τ.norm₂ (S*T) ≤ ‖S‖ * τ.norm₂ T :=
  (S : H →L[ℂ] H).le_opNorm ((T : H →L[ℂ] H) τ.vector)

theorem norm₂_mul_le_right (S T : Algebra (M := M)) : τ.norm₂ (S*T) ≤ τ.norm₂ S * ‖T‖ := by
  rw [← τ.norm₂_star (S*T), star_mul]
  have h := τ.norm₂_mul_le (star T) (star S)
  simpa [τ.norm₂_star, mul_comm, ContinuousLinearMap.star_eq_adjoint] using h

theorem norm₂_le_norm (T : Algebra (M := M)) : τ.norm₂ T ≤ ‖T‖ := by
  have h := (T : H →L[ℂ] H).le_opNorm τ.vector
  simpa [norm₂, τ.norm_vector] using h

theorem norm_trace_le_norm₂ (T : Algebra (M := M)) : ‖τ.trace T‖ ≤ τ.norm₂ T := by
  simpa [trace, norm₂, τ.norm_vector] using norm_inner_le_norm τ.vector ((T : H →L[ℂ] H) τ.vector)

theorem norm₂_eq_zero_iff (T : Algebra (M := M)) : τ.norm₂ T = 0 ↔ T = 0 := by
  constructor
  · intro h
    exact τ.separating T (norm_eq_zero.mp h)
  · rintro rfl
    exact τ.norm₂_zero

end TracialRepresentation

end FiniteFactor

end

end OAI
