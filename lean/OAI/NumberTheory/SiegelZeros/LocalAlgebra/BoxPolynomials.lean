import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Data.Fintype.Pi
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Finsupp.Supported
import Mathlib.RingTheory.MvPolynomial.Basic

namespace OAI

namespace SiegelZeros


namespace W17

open scoped BigOperators

abbrev Exponent := Fin 4 →₀ ℕ

def Box (N : ℕ) : Set Exponent := {d | ∀ i, d i < N}

noncomputable def boxEquiv (N : ℕ) : Box N ≃ (Fin 4 → Fin N) where
  toFun d i := ⟨d.1 i, d.2 i⟩
  invFun n := ⟨Finsupp.equivFunOnFinite.symm (fun i => (n i).val), fun i => (n i).isLt⟩
  left_inv d := by apply Subtype.ext; ext i; rfl
  right_inv n := by funext i; rfl

noncomputable instance boxFintype (N : ℕ) : Fintype (Box N) :=
  Fintype.ofEquiv (Fin 4 → Fin N) (boxEquiv N).symm

theorem card_box (N : ℕ) : Fintype.card (Box N) = N ^ 4 := by
  rw [Fintype.card_congr (boxEquiv N)]
  simp

variable (K : Type*) [Field K]

noncomputable def boxPolynomials (N : ℕ) : Submodule K (MvPolynomial (Fin 4) K) :=
  MvPolynomial.restrictSupport K (Box N)

theorem mem_boxPolynomials_iff (N : ℕ) (F : MvPolynomial (Fin 4) K) :
    F ∈ boxPolynomials K N ↔ ∀ d ∈ F.support, ∀ i, d i < N := Iff.rfl

theorem finrank_boxPolynomials (N : ℕ) :
    Module.finrank K (boxPolynomials K N) = N ^ 4 := by
  calc
    Module.finrank K (boxPolynomials K N) = Module.finrank K (Box N →₀ K) :=
      (MvPolynomial.basisRestrictSupport K (Box N)).repr.finrank_eq
    _ = Fintype.card (Box N) := Module.finrank_finsupp_self K
    _ = N ^ 4 := card_box N

theorem boxPolynomials_eq_span (N : ℕ) :
    boxPolynomials K N = Submodule.span K
      (Set.range (fun d : Box N => MvPolynomial.monomial d.1 (1 : K))) := by
  rw [boxPolynomials, MvPolynomial.restrictSupport_eq_span]
  congr 1
  ext F
  constructor
  · rintro ⟨d, hd, rfl⟩
    exact ⟨⟨d, hd⟩, rfl⟩
  · rintro ⟨d, rfl⟩
    exact ⟨d.1, d.2, rfl⟩

theorem linearIndependent_boxMonomials (N : ℕ) :
    LinearIndependent K (fun d : Box N => MvPolynomial.monomial d.1 (1 : K)) := by
  simpa only [MvPolynomial.coe_basisMonomials, Function.comp_def] using
    (MvPolynomial.basisMonomials (Fin 4) K).linearIndependent.comp
      (fun d : Box N => d.1) Subtype.val_injective

theorem exponent_total_lt {N : ℕ} (_hN : 0 < N) {d : Exponent}
    (hd : d ∈ Box N) : d.sum (fun _ n => n) < 4 * N := by
  rw [Finsupp.sum_fintype _ _ (fun _ => rfl)]
  have h := Finset.sum_lt_sum_of_nonempty (s := Finset.univ)
    (f := fun i : Fin 4 => d i) (g := fun _ => N) Finset.univ_nonempty
    (fun i _ => hd i)
  simpa using h

theorem totalDegree_lt {N : ℕ} (hN : 0 < N) {F : MvPolynomial (Fin 4) K}
    (hF : F ∈ boxPolynomials K N) : F.totalDegree < 4 * N := by
  rw [MvPolynomial.totalDegree, Finset.sup_lt_iff (Nat.mul_pos (by decide : 0 < 4) hN)]
  intro d hd
  exact exponent_total_lt hN ((mem_boxPolynomials_iff K N F).mp hF d hd)

end W17


end SiegelZeros

end OAI
