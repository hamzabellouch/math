import OAI.Analysis.Nuclearity.CommutingChoiFactor
import OAI.Analysis.WeakInfiniteness.CPSchwarz

namespace OAI

/-! Positive matrix coefficients from commuting completely positive and
homomorphic ranges. This constructs the finite matrix tensor functional;
positivity is proved by the actual Choi square-root coefficients. -/

noncomputable section
open scoped BigOperators CStarAlgebra ComplexOrder

namespace WeakPureInfiniteness

variable {C D : Type*} [NonUnitalCStarAlgebra C] [NonUnitalCStarAlgebra D]
  [PartialOrder C] [StarOrderedRing C] [PartialOrder D] [StarOrderedRing D]

local instance commutingPositiveRealModule {n : Type*} [Fintype n] :
    Module ℝ (CStarMatrix n n D) := Module.complexToReal _

omit [PartialOrder C] [StarOrderedRing C] in
lemma matrix_quadratic_nonneg {I : Type*} [Fintype I] [DecidableEq I]
    (Y : CStarMatrix I I D) (hY : 0 ≤ Y) (x : I → D) :
    0 ≤ ∑ i, ∑ j, star (x i) * Y i j * x j := by
  cases isEmpty_or_nonempty I with
  | inl h => simp
  | inr h =>
    let i₀ : I := Classical.choice h
    let V : CStarMatrix I I D := CStarMatrix.ofMatrix (fun i j => if j = i₀ then x i else 0)
    have hcol (i : I) : V i i₀ = x i := by
      change (if i₀ = i₀ then x i else 0) = x i
      simp only [ite_true]
    have hp := cstarMatrix_diagonal_nonneg (star V * Y * V)
      (star_left_conjugate_nonneg hY V) i₀
    have he : (star V * Y * V) i₀ i₀ = ∑ i, ∑ j, star (x i) * Y i j * x j := by
      simp only [CStarMatrix.mul_apply, CStarMatrix.star_apply, hcol, Finset.sum_mul]
      exact Finset.sum_comm
    exact he ▸ hp

def commutingMatrixLinearMap {n : ℕ}
    (ψ : CStarMatrix (Fin n) (Fin n) ℂ →L[ℂ] D) (η : C →⋆ₙₐ[ℂ] D) :
    CStarMatrix (Fin n) (Fin n) C →ₗ[ℂ] D where
  toFun M := ∑ i, ∑ j, ψ (matrixUnit i j) * η (M i j)
  map_add' M N := by simp only [CStarMatrix.add_apply, map_add, mul_add, Finset.sum_add_distrib]
  map_smul' c M := by
    simp only [CStarMatrix.smul_apply, map_smul, RingHom.id_apply, mul_smul_comm,
      Finset.smul_sum]

omit [PartialOrder C] [StarOrderedRing C] [PartialOrder D] [StarOrderedRing D] in
@[simp] lemma commutingMatrixLinearMap_apply {n : ℕ}
    (ψ : CStarMatrix (Fin n) (Fin n) ℂ →L[ℂ] D) (η : C →⋆ₙₐ[ℂ] D)
    (M : CStarMatrix (Fin n) (Fin n) C) :
    commutingMatrixLinearMap ψ η M = ∑ i, ∑ j, ψ (matrixUnit i j) * η (M i j) := rfl

theorem commutingMatrixLinearMap_nonneg {n : ℕ} (hn : 1 ≤ n)
    (ψ : CStarMatrix (Fin n) (Fin n) ℂ →L[ℂ] D) (hψ : CompletelyPositive ψ)
    (η : C →⋆ₙₐ[ℂ] D) (hc : ∀ i j c, Commute (ψ (matrixUnit i j)) (η c))
    (M : CStarMatrix (Fin n) (Fin n) C) (hM : 0 ≤ M) :
    0 ≤ commutingMatrixLinearMap ψ η M := by
  obtain ⟨X, hX, hcomm⟩ := completelyPositive_matrix_gram_commuting hn ψ hψ η hc
  have hp : 0 ≤ ∑ k, ∑ i, ∑ j, star (X k i) * η (M i j) * X k j := by
    apply Finset.sum_nonneg
    intro k _
    exact matrix_quadratic_nonneg (CStarMatrix.mapₙₐ η M)
      (map_nonneg (CStarMatrix.mapₙₐ η) hM) (fun i => X k i)
  have ht (i j k : Fin n) : (star (X k i) * X k j) * η (M i j) =
      star (X k i) * η (M i j) * X k j := by
    rw [mul_assoc, (hcomm k j (M i j)).eq, ← mul_assoc]
  have he : commutingMatrixLinearMap ψ η M =
      ∑ k, ∑ i, ∑ j, star (X k i) * η (M i j) * X k j := by
    simp only [commutingMatrixLinearMap_apply, hX, Finset.sum_mul, ht]
    calc
      _ = ∑ i, ∑ k, ∑ j, star (X k i) * η (M i j) * X k j := by
        apply Finset.sum_congr rfl
        intro i _
        exact Finset.sum_comm
      _ = _ := Finset.sum_comm
  exact he.symm ▸ hp

end WeakPureInfiniteness

end

end OAI
