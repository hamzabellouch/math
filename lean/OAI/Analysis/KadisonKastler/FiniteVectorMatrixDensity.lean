import OAI.Analysis.KadisonKastler.ConcreteTraceTransfer
import OAI.Analysis.FactorGeneration.MatrixSequence

namespace OAI

/-! # Matrix-stage density for a finite vector trace

Finite strong approximation on both vectors of each coefficient controls
`τ(y* y)`. A trace vector in the original representation is not required.
-/

namespace KadisonKastler

open Generator Generator.Tracial
open scoped BigOperators

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

/-- The finite vector formula turns strong matrix-stage approximation into trace approximation. -/
theorem FiniteVectorTrace.matrix_stage_approximation
    {τ : FaithfulTracialState (Algebra M)} (hτ : FiniteVectorTrace τ)
    (A : ℕ → FiniteMatrixStage M)
    (hA : Monotone (fun n => (A n).units.concreteAlgebra))
    (x : Algebra M) (hx : x.val ∈ FiniteMatrixStage.generated A)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ n, ∃ a : Algebra M, a.val ∈ (A n).units.concreteAlgebra ∧
      traceTwoNorm τ (x - a) < ε := by
  classical
  obtain ⟨m,ξ,η,hrep⟩ := hτ
  let δ : ℝ := ε / ((m : ℝ) + 1)
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hδ : 0 < δ := div_pos hε (by positivity)
  obtain ⟨n,a,ha⟩ := FiniteMatrixStage.exists_stage_strong_approximation A hA ⟨x.val,hx⟩
    (Finset.univ.image ξ ∪ Finset.univ.image η) δ hδ
  let b : Algebra M := ⟨a.val,(A n).units.concreteAlgebra_le a.property⟩
  let y := x - b
  have hξ (i : Fin m) : ‖y.val (ξ i)‖ < δ := by
    exact ha (ξ i) (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩))
  have hη (i : Fin m) : ‖y.val (η i)‖ < δ := by
    exact ha (η i) (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩))
  have ht : τ.toLinearMap (star y * y) =
      ∑ i, inner ℂ (y.val (η i)) (y.val (ξ i)) := by
    rw [hrep]
    apply Finset.sum_congr rfl
    intro i _
    change inner ℂ (η i) ((star y.val) (y.val (ξ i))) = _
    rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right]
  have hn : (traceTwoNorm τ y) ^ 2 ≤ (m : ℝ) * δ ^ 2 := by
    rw [traceTwoNorm_sq, ht]
    apply (Complex.re_le_norm _).trans
    apply (norm_sum_le _ _).trans
    calc
      (∑ i : Fin m, ‖inner ℂ (y.val (η i)) (y.val (ξ i))‖) ≤
          ∑ _i : Fin m, δ ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        exact (norm_inner_le_norm _ _).trans (by
          nlinarith [norm_nonneg (y.val (η i)), norm_nonneg (y.val (ξ i)), hξ i, hη i])
      _ = (m : ℝ) * δ ^ 2 := by simp
  have hδε : δ * ((m : ℝ) + 1) = ε := by
    dsimp [δ]
    exact div_mul_cancel₀ _ (by positivity)
  have hsmall : (m : ℝ) * δ ^ 2 < ε ^ 2 := by
    have hs : 0 < δ ^ 2 := sq_pos_of_pos hδ
    have hm' : (m : ℝ) < ((m : ℝ) + 1) ^ 2 := by nlinarith
    nlinarith [mul_lt_mul_of_pos_right hm' hs, sq_nonneg (δ * ((m : ℝ) + 1) - ε)]
  refine ⟨n,b,a.property,?_⟩
  change traceTwoNorm τ y < ε
  have hp := traceTwoNorm_nonneg τ y
  nlinarith

end

end KadisonKastler

end OAI
