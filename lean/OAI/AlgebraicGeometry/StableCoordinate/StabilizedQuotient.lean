import Mathlib

namespace OAI

/-!
# Eliminating the last linear relation in the stabilization

The variables of the six-variable ring are ordered `p,s,u,L,N,w`.
The quotient by `L-u+p*w` is the polynomial algebra on `p,s,u,N,w`.
This file gives an actual algebra equivalence, including its effect on `p`.
-/

noncomputable section

namespace StableCoordinate.StabilizedQuotient

open MvPolynomial

abbrev P := MvPolynomial (Fin 6) ℂ
abbrev S := MvPolynomial (Fin 5) ℂ

def equation : P := X 3 - X 2 + X 0 * X 5

def equationIdeal : Ideal P := Ideal.span ({equation} : Set P)

abbrev A := P ⧸ equationIdeal

def evaluate : P →ₐ[ℂ] S :=
  aeval ![X 0, X 1, X 2, X 2 - X 0 * X 4, X 3, X 4]

@[simp] theorem evaluate_equation : evaluate equation = 0 := by
  simp [evaluate, equation]

def out : A →ₐ[ℂ] S :=
  Ideal.Quotient.liftₐ equationIdeal evaluate (by
    intro r hr
    have hi : equationIdeal ≤ RingHom.ker evaluate.toRingHom := by
      apply Ideal.span_le.mpr
      intro t ht
      rcases Set.mem_singleton_iff.mp ht with rfl
      exact evaluate_equation
    exact hi hr)

def into : S →ₐ[ℂ] A :=
  aeval ![Ideal.Quotient.mkₐ ℂ equationIdeal (X 0),
    Ideal.Quotient.mkₐ ℂ equationIdeal (X 1),
    Ideal.Quotient.mkₐ ℂ equationIdeal (X 2),
    Ideal.Quotient.mkₐ ℂ equationIdeal (X 4),
    Ideal.Quotient.mkₐ ℂ equationIdeal (X 5)]

@[simp] theorem out_mk (r : P) : out (Ideal.Quotient.mk equationIdeal r) = evaluate r := rfl

@[simp] theorem quotient_equation : Ideal.Quotient.mkₐ ℂ equationIdeal equation = 0 := by
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton equation))

theorem out_comp_into : out.comp into = AlgHom.id ℂ S := by
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i <;> simp [into, evaluate]

theorem into_comp_out : into.comp out = AlgHom.id ℂ A := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i <;> simp [evaluate, into]
  have h := quotient_equation
  simp only [equation, map_add, map_sub, map_mul] at h
  change Ideal.Quotient.mk equationIdeal (X 3) -
    Ideal.Quotient.mk equationIdeal (X 2) +
    Ideal.Quotient.mk equationIdeal (X 0) * Ideal.Quotient.mk equationIdeal (X 5) = 0 at h
  linear_combination -h

/-- The quotient by `L-u+p*w` is the five-variable polynomial algebra. -/
def equiv : A ≃ₐ[ℂ] S :=
  AlgEquiv.ofAlgHom out into out_comp_into into_comp_out

@[simp] theorem equiv_mk (r : P) : equiv (Ideal.Quotient.mk equationIdeal r) = evaluate r := rfl

@[simp] theorem equiv_p : equiv (Ideal.Quotient.mkₐ ℂ equationIdeal (X 0)) = X 0 := by
  simp [evaluate]

end StableCoordinate.StabilizedQuotient

end

end OAI
