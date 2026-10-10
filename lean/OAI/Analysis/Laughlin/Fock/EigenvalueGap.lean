import OAI.Analysis.Laughlin.Operators.PhysicalFockGap

namespace OAI

namespace Laughlin.Fock
open Filter
open scoped BigOperators

theorem sourceFockHamiltonian_symmetric (Q : ℕ) (x y : Space Q) :
    occupationInner Q (sourceFockHamiltonian Q x) y =
      occupationInner Q x (sourceFockHamiltonian Q y) := by
  simp only [sourceFockHamiltonian,LinearMap.sum_apply,Module.End.mul_apply,
    occupationInner_sum_left,occupationInner_sum_right,pair_annihilate_create_inner]
  apply Finset.sum_congr rfl
  intro p hp
  exact pairCreate_pair_adjoint Q _ _ _

theorem sourceFockHamiltonian_kernel (Q : ℕ) (x : Space Q) :
    sourceFockHamiltonian Q x=0 ↔ sourceFockEnergy Q x=0 := by
  constructor
  · intro h
    have he := sourceFockHamiltonian_quadratic Q x
    rw [h] at he
    have hz : occupationInner Q 0 x=0 := by simp [occupationInner]
    rw [hz] at he
    exact Complex.ofReal_injective he.symm
  · intro h
    have he := (sourceFockEnergy_eq_zero Q x).mp h
    simp only [sourceFockHamiltonian,LinearMap.sum_apply,Module.End.mul_apply]
    apply Finset.sum_eq_zero
    intro p hp
    rw [he p hp,map_zero]

theorem sourceFock_eigen_energy (Q : ℕ) (x : Space Q) (a : ℝ)
    (he : sourceFockHamiltonian Q x=(a : ℂ) • x) :
    sourceFockEnergy Q x=a*occupationNormSq Q x := by
  have h := sourceFockHamiltonian_quadratic Q x
  rw [he,occupationInner_smul_left,occupationInner_self] at h
  simp only [Complex.star_def,Complex.conj_ofReal,← Complex.ofReal_mul] at h
  exact Complex.ofReal_injective h.symm

theorem sourceFock_eigen_nonneg (Q : ℕ) (x : Space Q) (hx : x≠0) (a : ℝ)
    (he : sourceFockHamiltonian Q x=(a : ℂ) • x) : 0 ≤ a := by
  have hn : 0 < occupationNormSq Q x :=
    lt_of_le_of_ne (occupationNormSq_nonneg Q x) (Ne.symm (mt (occupationNormSq_eq_zero Q x).mp hx))
  have hE : 0 ≤ sourceFockEnergy Q x := Finset.sum_nonneg (fun p hp => occupationNormSq_nonneg Q _)
  rw [sourceFock_eigen_energy Q x a he] at hE
  exact nonneg_of_mul_nonneg_left hE hn

theorem physical_fock_eigenvalue_gap_uniform :
    ∃ Q₀ : ℕ, 25 ≤ Q₀ ∧ ∀ Q : ℕ, Q₀ ≤ Q → ∀ x : Space Q, x≠0 → ∀ a : ℝ,
      sourceFockHamiltonian Q x=(a : ℂ) • x → a=0 ∨ (1/100 : ℝ) ≤ a := by
  obtain ⟨Q₀,h25,h⟩ := physical_fock_square_uniform
  refine ⟨Q₀,h25,fun Q hQ x hx a he => ?_⟩
  have hn : 0 < occupationNormSq Q x :=
    lt_of_le_of_ne (occupationNormSq_nonneg Q x) (Ne.symm (mt (occupationNormSq_eq_zero Q x).mp hx))
  have ha := sourceFock_eigen_nonneg Q x hx a he
  have hs := h Q hQ x
  rw [sourceFock_eigen_energy Q x a he,he,occupationNormSq_smul] at hs
  have hnorm : ‖(a : ℂ)‖^2=a^2 := by simp
  rw [hnorm] at hs
  have hs' : (1/100 : ℝ)*a ≤ a^2 := by nlinarith
  by_cases hz : a=0
  · exact Or.inl hz
  · right
    have hp : 0 < a := lt_of_le_of_ne ha (Ne.symm hz)
    nlinarith

end Laughlin.Fock

end OAI
