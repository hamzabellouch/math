import Mathlib.LinearAlgebra.Trace
import Mathlib.Basic.Real.Basic

namespace OAI

/-! The finite-dimensional trace cancellation used for a positive Hodge
eigenvalue. Its three identities are the exact/coexact differential identities. -/

namespace PositiveEinsteinFour.Geometry

theorem finite_hodge_trace_cancel {V : Type*} [AddCommGroup V] [Module ℝ V]
    [FiniteDimensional ℝ V] (A S : Module.End ℝ V) (κ : ℝ) (hκ : κ ≠ 0)
    (hAA : A * A = κ • A) (hASA : A * S * A = 0)
    (hSA : S * A + A * S = κ • S) : LinearMap.trace ℝ V S = 0 := by
  have hzero : LinearMap.trace ℝ V (S * (A * A)) = 0 := by
    rw [← mul_assoc, LinearMap.trace_mul_cycle, hASA, map_zero]
  have htraceA : LinearMap.trace ℝ V (S * A) = 0 := by
    rw [hAA, mul_smul_comm, map_smul, smul_eq_mul] at hzero
    exact (mul_eq_zero.mp hzero).resolve_left hκ
  have he := congrArg (LinearMap.trace ℝ V) hSA
  rw [map_add, LinearMap.trace_mul_comm ℝ A S, htraceA, zero_add,
    map_smul, smul_eq_mul] at he
  exact (mul_eq_zero.mp he.symm).resolve_left hκ

end PositiveEinsteinFour.Geometry

end OAI
