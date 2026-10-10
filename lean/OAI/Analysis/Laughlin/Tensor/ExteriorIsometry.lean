import OAI.Analysis.Laughlin.Fock.Bidegree
import OAI.Analysis.Laughlin.Tensor.ExteriorContraction

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators

theorem tensorExterior_inner (n Q : ℕ) (ψ φ : State n Q) (hφ : Antisymmetric φ) :
    occupationInner Q (tensorExterior n Q ψ) (tensorExterior n Q φ) =
      (n.factorial : ℂ) * ∑ a, star (ψ a) * φ a := by
  induction n with
  | zero =>
    simp only [tensorExterior, ExteriorAlgebra.ιMulti_zero_apply]
    simp only [occupationInner_sum_left,occupationInner_sum_right]
    simp only [occupationInner_smul_left,occupationInner_smul_right]
    have h1 : occupationInner Q 1 1 = 1 := by
      rw [← occupation_empty]
      simp [occupationInner,Module.Basis.repr_self,Finsupp.single_apply]
    simp [h1,mul_comm]
  | succ n ih =>
    rw [tensorExterior_cons,occupationInner_sum_left]
    simp only [create_annihilate_adjoint,annihilate_tensorExterior n Q φ hφ,
      occupationInner_smul_right]
    simp_rw [ih _ _ (antisymmetric_cons hφ _)]
    rw [sum_config_cons]
    simp only [Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one,
      Finset.mul_sum]
    ring_nf

theorem tensorExterior_norm (n Q : ℕ) (ψ : State n Q) (hψ : Antisymmetric ψ) :
    occupationNormSq Q (tensorExterior n Q ψ) =
      (n.factorial : ℝ) * ∑ a, ‖ψ a‖^2 := by
  have h := tensorExterior_inner n Q ψ ψ hψ
  rw [occupationInner_self] at h
  have he (a : Configuration n Q) : star (ψ a)*ψ a = ((‖ψ a‖^2 : ℝ) : ℂ) := by
    rw [← Complex.normSq_eq_norm_sq,Complex.normSq_eq_conj_mul_self]
    rfl
  simp only [he,← Complex.ofReal_sum,← Complex.ofReal_natCast,← Complex.ofReal_mul] at h
  exact Complex.ofReal_injective h

noncomputable def normalizedTensorExterior (n Q : ℕ) (ψ : State n Q) : Space Q :=
  ((Real.sqrt (n.factorial : ℝ))⁻¹ : ℂ) • tensorExterior n Q ψ

theorem normalizedTensorExterior_inner (n Q : ℕ) (ψ φ : State n Q)
    (hφ : Antisymmetric φ) :
    occupationInner Q (normalizedTensorExterior n Q ψ) (normalizedTensorExterior n Q φ) =
      ∑ a, star (ψ a)*φ a := by
  have hp : 0 < (n.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos n
  have hs : Real.sqrt (n.factorial : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hp)
  have he : ((Real.sqrt (n.factorial : ℝ) : ℂ))^2 = (n.factorial : ℂ) := by
    exact_mod_cast Real.sq_sqrt (le_of_lt hp)
  simp only [normalizedTensorExterior,occupationInner_smul_left,occupationInner_smul_right,
    tensorExterior_inner n Q ψ φ hφ]
  simp only [Complex.star_def, map_inv₀, Complex.conj_ofReal]
  have hsc : (Real.sqrt (n.factorial : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hs
  rw [← he]
  field_simp

theorem normalizedTensorExterior_norm (n Q : ℕ) (ψ : State n Q)
    (hψ : Antisymmetric ψ) :
    occupationNormSq Q (normalizedTensorExterior n Q ψ) = ∑ a, ‖ψ a‖^2 := by
  have h := normalizedTensorExterior_inner n Q ψ ψ hψ
  rw [occupationInner_self] at h
  have he (a : Configuration n Q) : star (ψ a)*ψ a = ((‖ψ a‖^2 : ℝ) : ℂ) := by
    rw [← Complex.normSq_eq_norm_sq,Complex.normSq_eq_conj_mul_self]
    rfl
  simp only [he,← Complex.ofReal_sum] at h
  exact Complex.ofReal_injective h

end Laughlin.Fock

end OAI
