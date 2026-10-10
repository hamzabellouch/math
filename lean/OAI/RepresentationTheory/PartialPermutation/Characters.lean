import Mathlib
import OAI.RepresentationTheory.PartialPermutation.MatrixCoefficients

namespace OAI

section
open scoped Classical
open scoped BigOperators ComplexConjugate MonoidAlgebra
open scoped BigOperators ComplexConjugate

namespace PartialPermutation
open scoped BigOperators ComplexConjugate MonoidAlgebra

noncomputable section
variable {G V : Type*} [Group G] [Fintype G]
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) (hρ : IsUnitary ρ)
include hρ

omit [Fintype G] in
lemma unitary_adjoint (g : G) : LinearMap.adjoint (ρ g) = ρ g⁻¹ := by
  ext v
  apply ext_inner_left ℂ
  intro u
  rw [LinearMap.adjoint_inner_right]
  have h := hρ g u (ρ g⁻¹ v)
  simpa using h

omit [Fintype G] in
lemma unitary_character_inv (g : G) : ρ.character g⁻¹ = conj (ρ.character g) := by
  let e := stdOrthonormalBasis ℂ V
  rw [Representation.character, Representation.character, ← unitary_adjoint ρ hρ,
    LinearMap.trace_eq_sum_inner _ e, LinearMap.trace_eq_sum_inner _ e, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [LinearMap.adjoint_inner_right, inner_conj_symm]

variable [Representation.IsIrreducible ρ]

lemma character_norm_sq_sum : ∑ g, ‖ρ.character g‖ ^ 2 = (Fintype.card G : ℝ) := by
  let := invertibleOfNonzero (show (Nat.card G : ℂ) ≠ 0 by simp [Nat.card_eq_fintype_card])
  have h := Representation.char_orthonormal ρ ρ
  have he : Nonempty (Representation.Equiv ρ ρ) := ⟨Representation.Equiv.refl ρ⟩
  simp only [ite_eq_left he, unitary_character_inv ρ hρ] at h
  have hN : (Nat.card G : ℂ) ≠ 0 := by simp [Nat.card_eq_fintype_card]
  have hsum : (∑ g, ρ.character g * conj (ρ.character g)) = (Nat.card G : ℂ) := by
    simpa [hN, mul_assoc] using congrArg (fun z : ℂ => (Nat.card G : ℂ) * z) h
  have ht := congrArg Complex.re hsum
  simpa only [Complex.re_sum, Complex.mul_conj, Complex.ofReal_re,
    Complex.normSq_eq_norm_sq, Complex.natCast_re, Nat.card_eq_fintype_card] using ht

lemma character_kernel_identity :
    complexFourier ρ (fun g => ((Module.finrank ℂ V : ℂ) / Fintype.card G) *
      conj (ρ.character g)) = 1 := by
  classical
  let e := stdOrthonormalBasis ℂ V
  have : Nontrivial V := IsSimpleModule.nontrivial ℂ[G] ρ.asModule
  have hD : (Module.finrank ℂ V : ℂ) ≠ 0 := by
    exact_mod_cast (Module.finrank_pos (R := ℂ) (M := V)).ne'
  have hN : (Fintype.card G : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  ext y
  apply ext_inner_left ℂ
  intro x
  simp only [complexFourier, LinearMap.sum_apply, LinearMap.smul_apply, Module.End.one_apply]
  simp only [inner_sum, inner_smul_right, mul_assoc, ← Finset.mul_sum]
  have hs : (Fintype.card G : ℂ)⁻¹ * ∑ g, conj (ρ.character g) * inner ℂ x (ρ g y) =
      (Module.finrank ℂ V : ℂ)⁻¹ * inner ℂ x y := by
    simp_rw [Representation.character, LinearMap.trace_eq_sum_inner _ e, map_sum,
      Finset.sum_mul]
    rw [Finset.sum_comm, Finset.mul_sum]
    have hc (i : Fin (Module.finrank ℂ V)) :=
      matrixCoefficient_orthogonality ρ hρ x (e i) y (e i)
    simp_rw [mul_comm (conj _), hc, div_eq_mul_inv]
    simpa [Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm] using
      congrArg (fun z : ℂ => (Module.finrank ℂ V : ℂ)⁻¹ * z) (e.sum_inner_mul_inner x y)
  rw [div_eq_mul_inv, mul_assoc, hs, ← mul_assoc, mul_inv_cancel₀ hD, one_mul]

end
end PartialPermutation

end

end OAI
