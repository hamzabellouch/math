import Mathlib
import OAI.Probability.BinarySweep.Representations.IsotypicTrace
import OAI.Probability.BinarySweep.MatrixBounds.PositiveTraceRestriction

namespace OAI

noncomputable section
open scoped BigOperators Classical ComplexOrder

namespace BinaryCoordinateSweeps.Irrep
open Representation

variable {G V W : Type*} [Group G] [Fintype G]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
  (ρ : Representation ℂ G V) (σ : Representation ℂ G W)

def groupAverage (p : G → ℂ) : V →ₗ[ℂ] V := ∑ g, p g • ρ g

def evenMoment (q : ℕ) (A : V →ₗ[ℂ] V) : ℝ :=
  (LinearMap.trace ℂ V ((A.adjoint*A)^q)).re

omit [Fintype G] in
lemma unitary_rep_adjoint (hρ : ∀ g v, ‖ρ g v‖ = ‖v‖) (g : G) :
    (ρ g).adjoint = ρ g⁻¹ := by
  symm
  apply (LinearMap.eq_adjoint_iff _ _).mpr
  intro x y
  let U : V →ₗᵢ[ℂ] V := { toLinearMap := ρ g, norm_map' := hρ g }
  have he := U.inner_map_map (ρ g⁻¹ x) y
  change inner ℂ (ρ g (ρ g⁻¹ x)) (ρ g y) = inner ℂ (ρ g⁻¹ x) y at he
  rw [← Module.End.mul_apply,← map_mul,mul_inv_cancel,map_one,Module.End.one_apply] at he
  exact he.symm

omit [FiniteDimensional ℂ V] [FiniteDimensional ℂ W] in
lemma average_compatible (p : G → ℂ) (f : IntertwiningMap ρ σ) (v : V) :
    groupAverage σ p (f v) = f (groupAverage ρ p v) := by
  simp only [groupAverage,LinearMap.sum_apply,LinearMap.smul_apply,map_sum,map_smul,
    IntertwiningMap.isIntertwining]

lemma adjoint_average_compatible (p : G → ℂ)
    (hρ : ∀ g v, ‖ρ g v‖ = ‖v‖) (hσ : ∀ g w, ‖σ g w‖ = ‖w‖)
    (f : IntertwiningMap ρ σ) (v : V) :
    (groupAverage σ p).adjoint (f v) = f ((groupAverage ρ p).adjoint v) := by
  simp only [groupAverage,map_sum,map_smulₛₗ,unitary_rep_adjoint ρ hρ,
    unitary_rep_adjoint σ hσ,LinearMap.sum_apply,LinearMap.smul_apply,
    IntertwiningMap.isIntertwining, RingHom.id_apply]

lemma even_compatible (p : G → ℂ)
    (hρ : ∀ g v, ‖ρ g v‖ = ‖v‖) (hσ : ∀ g w, ‖σ g w‖ = ‖w‖)
    (q : ℕ) (f : IntertwiningMap ρ σ) (v : V) :
    (((groupAverage σ p).adjoint * groupAverage σ p)^q) (f v) =
      f ((((groupAverage ρ p).adjoint * groupAverage ρ p)^q) v) := by
  induction q generalizing v with
  | zero => simp
  | succ q ih =>
    rw [pow_succ',pow_succ',Module.End.mul_apply,Module.End.mul_apply,ih]
    rw [Module.End.mul_apply,average_compatible,adjoint_average_compatible ρ σ p hρ hσ]
    rfl

theorem multiplicity_moment_le [ρ.IsIrreducible] (p : G → ℂ)
    (hρ : ∀ g v, ‖ρ g v‖ = ‖v‖) (hσ : ∀ g w, ‖σ g w‖ = ‖w‖) (q : ℕ) :
    (Module.finrank ℂ (IntertwiningMap ρ σ) : ℝ) * evenMoment q (groupAverage ρ p) ≤
      evenMoment q (groupAverage σ p) := by
  let A := ((groupAverage ρ p).adjoint * groupAverage ρ p)^q
  let B := ((groupAverage σ p).adjoint * groupAverage σ p)^q
  have hAB := even_compatible ρ σ p hρ hσ q
  have hBp : B.IsPositive := positive_pow (LinearMap.isPositive_adjoint_comp_self _) q
  have hle := positive_trace_restrict_le (isotypicSpan ρ σ) B hBp
    (isotypic_invariant_of_compatible ρ σ A B hAB)
  rw [isotypic_trace ρ σ A B hAB] at hle
  simpa only [A, B, evenMoment, Complex.mul_re,Complex.natCast_re,Complex.natCast_im,zero_mul,sub_zero] using hle

end BinaryCoordinateSweeps.Irrep

end

end OAI
