import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
import Mathlib.RingTheory.Ideal.Colon
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.PrincipalIdealDomain

namespace OAI

namespace SiegelZeros

section

namespace WeightedTorusJets.W06

section ColonPowers
variable {R : Type*} [CommRing R]

@[simp] theorem colon_pow_zero (I : Ideal R) (x : R) :
    I.colon {x ^ (0 : ℕ)} = I := by
  ext a
  simp [Submodule.mem_colon_singleton, smul_eq_mul]

theorem colon_pow_succ (I : Ideal R) (x : R) (j : ℕ) :
    I.colon {x ^ (j + 1)} = (I.colon {x ^ j}).colon {x} := by
  ext a
  simp only [Submodule.mem_colon_singleton, smul_eq_mul, pow_succ,
    mul_assoc, mul_comm, mul_left_comm]

theorem colon_powers_monotone (I : Ideal R) (x : R) :
    Monotone (fun j : ℕ => I.colon {x ^ j}) := by
  apply monotone_nat_of_le_succ
  intro j
  rw [colon_pow_succ]
  exact Ideal.le_colon

theorem colon_pow_add_eq_of_succ_eq (I : Ideal R) (x : R) (m : ℕ)
    (hstable : I.colon {x ^ (m + 1)} = I.colon {x ^ m}) (j : ℕ) :
    I.colon {x ^ (m + j)} = I.colon {x ^ m} := by
  induction j with
  | zero => simp
  | succ j ih =>
      rw [Nat.add_succ, colon_pow_succ, ih]
      simpa only [colon_pow_succ] using hstable

theorem exists_colon_powers_eventually_constant [IsNoetherianRing R]
    (I : Ideal R) (x : R) :
    ∃ m : ℕ, ∀ j : ℕ, m ≤ j → I.colon {x ^ j} = I.colon {x ^ m} := by
  let chain : ℕ →o Submodule R R :=
    ⟨fun j => I.colon {x ^ j}, colon_powers_monotone I x⟩
  obtain ⟨m, hm⟩ := monotone_stabilizes_iff_noetherian.mpr
    (inferInstance : IsNoetherian R R) chain
  exact ⟨m, fun j hj => (hm j hj).symm⟩

theorem exists_colon_pow_stable [IsNoetherianRing R] (I : Ideal R) (x : R) :
    ∃ m : ℕ, I.colon {x ^ (m + 1)} = I.colon {x ^ m} := by
  obtain ⟨m, hm⟩ := exists_colon_powers_eventually_constant I x
  exact ⟨m, hm (m + 1) (Nat.le_succ m)⟩

end ColonPowers

section HomogeneousColonPowers
attribute [local instance] MvPolynomial.gradedAlgebra
variable {k σ : Type*} [Field k]

theorem homogeneous_colon_pow (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k))
    {d : ℕ} {f : MvPolynomial σ k} (hf : f.IsHomogeneous d) (j : ℕ) :
    (I.colon {f ^ j}).IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k) := by
  intro n a ha
  apply Submodule.mem_colon_singleton.mpr
  have haf : a * f ^ j ∈ I := by
    simpa only [smul_eq_mul] using Submodule.mem_colon_singleton.mp ha
  have h := hI (n + d * j) haf
  rw [DirectSum.coe_decompose_mul_add_of_right_mem
    (MvPolynomial.homogeneousSubmodule σ k) (hf.pow j)] at h
  exact h

theorem homogeneous_colon_variable_pow (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k)) (i : σ) (j : ℕ) :
    (I.colon {(MvPolynomial.X i) ^ j}).IsHomogeneous
      (MvPolynomial.homogeneousSubmodule σ k) :=
  homogeneous_colon_pow I hI (MvPolynomial.isHomogeneous_X k i) j

theorem exists_homogeneous_stable_colon_variable [Finite σ]
    (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k)) (i : σ) :
    ∃ m : ℕ,
      (I.colon {(MvPolynomial.X i) ^ m}).IsHomogeneous
        (MvPolynomial.homogeneousSubmodule σ k) ∧
      I.colon {(MvPolynomial.X i) ^ (m + 1)} = I.colon {(MvPolynomial.X i) ^ m} ∧
      ∀ j : ℕ, m ≤ j →
        I.colon {(MvPolynomial.X i) ^ j} = I.colon {(MvPolynomial.X i) ^ m} := by
  obtain ⟨m, hm⟩ := exists_colon_powers_eventually_constant I (MvPolynomial.X i)
  exact ⟨m, homogeneous_colon_variable_pow I hI i m,
    hm (m + 1) (Nat.le_succ m), hm⟩

end HomogeneousColonPowers
end WeightedTorusJets.W06

end

end SiegelZeros

end OAI
