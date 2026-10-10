import Mathlib
import OAI.Analysis.Commutator.FiniteTrace

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder InnerProductSpace

namespace Kadison.MatrixDiffuse

open Matrix

lemma diagonal_trace {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    (φ : Matrix I I ℂ →ₗ[ℂ] ℂ) (htr : ∀ x y, φ (x*y)=φ (y*x)) (hunit : φ 1=1)
    (i : I) : φ (single i i 1)=(Fintype.card I : ℂ)⁻¹ := by
  have hdiag : ∀ j : I, φ (single i i 1)=φ (single j j 1) := by
    intro j
    simpa using htr (single i j 1) (single j i 1)
  have hcard : (Fintype.card I : ℂ)≠0 := by exact_mod_cast Fintype.card_ne_zero
  have h : (Fintype.card I : ℂ)*φ (single i i 1)=1 := by
    calc
      _=∑ j : I, φ (single j j 1) := by
        simp only [←hdiag,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
      _=φ 1 := by rw [←map_sum,Matrix.sum_single_one]
      _=1 := hunit
  apply mul_left_cancel₀ hcard
  rw [h,mul_inv_cancel₀ hcard]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M : VonNeumannAlgebra H) (τ : (H →L[ℂ] H) →ₚ[ℂ] ℂ)

variable (hτ : ∀ a∈M, ∀ b∈M, τ (a*b)=τ (b*a)) (h1 : τ 1=1)

include hτ h1

lemma exists_matrix_projection {n : ℕ} (hn : 0<n)
    (φ : Matrix (Fin n) (Fin n) ℂ →⋆ₐ[ℂ] M) :
    ∃ q∈M, IsStarProjection q ∧ q≠0 ∧ (τ q).re=(n : ℝ)⁻¹ := by
  let i : Fin n := ⟨0,hn⟩
  let : Nonempty (Fin n) := ⟨i⟩
  let ψ := M.toStarSubalgebra.subtype.comp φ
  have hdiag : τ (ψ (single i i 1))=(n : ℂ)⁻¹ := by
    have hd := diagonal_trace (τ.toLinearMap.comp ψ.toLinearMap)
      (fun x y => by
        change τ (ψ (x*y))=τ (ψ (y*x))
        simp only [map_mul]
        exact hτ _ (φ x).property _ (φ y).property)
      (by change τ (ψ 1)=1; simpa only [map_one] using h1) i
    change τ (ψ (single i i 1))=(Fintype.card (Fin n) : ℂ)⁻¹ at hd
    simpa only [Fintype.card_fin] using hd
  have hp : IsStarProjection (single i i (1 : ℂ)) := by
    constructor
    · change single i i (1 : ℂ)*single i i 1=single i i 1
      simp
    · change star (single i i (1 : ℂ))=single i i 1
      simp only [Matrix.star_eq_conjTranspose,Matrix.conjTranspose_single,star_one]
  refine ⟨ψ (single i i 1),(φ (single i i 1)).property,hp.map ψ,?_,?_⟩
  · intro hz
    have h := hdiag
    rw [hz,map_zero] at h
    have hnn : (n : ℂ)≠0 := by exact_mod_cast Nat.ne_of_gt hn
    exact (inv_ne_zero hnn) h.symm
  · rw [hdiag]
    have hcast : (n : ℂ)=(n : ℝ) := by simp
    rw [hcast,←Complex.ofReal_inv,Complex.ofReal_re]

theorem exists_small_of_matrix_stages (n : ℕ → ℕ)
    (φ : ∀ j, Matrix (Fin (n j)) (Fin (n j)) ℂ →⋆ₐ[ℂ] M)
    (hsize : ∀ N : ℕ, ∃ j, N<n j) {ε : ℝ} (hε : 0<ε) :
    ∃ q∈M, IsStarProjection q ∧ q≠0 ∧ (τ q).re<ε := by
  obtain ⟨N,hN,hNε⟩ := Real.exists_nat_pos_inv_lt hε
  obtain ⟨j,hj⟩ := hsize N
  obtain ⟨q,hqM,hq,hqn,hqt⟩ := exists_matrix_projection M τ hτ h1 (hN.trans hj) (φ j)
  refine ⟨q,hqM,hq,hqn,?_⟩
  rw [hqt]
  have hcastN : (0 : ℝ)<N := by exact_mod_cast hN
  have hcastj : (N : ℝ)<n j := by exact_mod_cast hj
  exact (inv_anti₀ hcastN hcastj.le).trans_lt hNε

theorem noMinimal_of_matrix_stages (hM : FactorCorner.IsFactor M)
    (hfaith : ∀ a∈M, τ (star a*a)=0 → a=0)
    (n : ℕ → ℕ) (φ : ∀ j, Matrix (Fin (n j)) (Fin (n j)) ℂ →⋆ₐ[ℂ] M)
    (hsize : ∀ N : ℕ, ∃ j, N<n j) : DiffuseProjection.HasNoMinimalProjections M := by
  apply FiniteTrace.noMinimal_of_small M τ hM hτ hfaith
  intro ε hε
  exact exists_small_of_matrix_stages M τ hτ h1 n φ hsize hε

end Kadison.MatrixDiffuse

end

end
end

end OAI
