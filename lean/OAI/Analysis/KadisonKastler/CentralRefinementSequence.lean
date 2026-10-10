import OAI.Analysis.KadisonKastler.MatrixCentralRefinement
import OAI.Analysis.KadisonKastler.GeometricCorrectionScale

namespace OAI

/-! # The increasing central-vector refinement sequence

Summable displacement budgets keep the limit vector nonzero. Successive
finite tests give a single increasing matrix sequence with vanishing
distance-to-line errors on the prescribed countable dense family.
-/

namespace KadisonKastler

open Generator Filter
open scoped Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

def centralRefinementIterates (E₀ : FiniteMatrixStage M)
    (F : ℕ → FiniteMatrixStage M → FiniteMatrixStage M) : ℕ → FiniteMatrixStage M
  | 0 => E₀
  | n + 1 => F n (centralRefinementIterates E₀ F n)

@[simp] theorem centralRefinementIterates_zero (E₀ : FiniteMatrixStage M)
    (F : ℕ → FiniteMatrixStage M → FiniteMatrixStage M) :
    centralRefinementIterates E₀ F 0 = E₀ := rfl

@[simp] theorem centralRefinementIterates_succ (E₀ : FiniteMatrixStage M)
    (F : ℕ → FiniteMatrixStage M → FiniteMatrixStage M) (n : ℕ) :
    centralRefinementIterates E₀ F (n + 1) = F n (centralRefinementIterates E₀ F n) := rfl

theorem centralRefinementIterates_mono (E₀ : FiniteMatrixStage M)
    (F : ℕ → FiniteMatrixStage M → FiniteMatrixStage M)
    (hF : ∀ n E, E.units.concreteAlgebra ≤ (F n E).units.concreteAlgebra) :
    Monotone (fun n => (centralRefinementIterates E₀ F n).units.concreteAlgebra) := by
  apply monotone_nat_of_le_succ
  intro n
  rw [centralRefinementIterates_succ]
  exact hF n _

theorem centralRefinementIterates_displacement
    (J : H ≃ₗᵢ⋆[ℂ] H) (ξ : H) (E₀ : FiniteMatrixStage M)
    (hfix : matrixStageCentralProjection E₀ J ξ = ξ)
    (F : ℕ → FiniteMatrixStage M → FiniteMatrixStage M) (d : ℕ → ℝ)
    (hmove : ∀ n E, ‖matrixStageCentralProjection E J ξ -
      matrixStageCentralProjection (F n E) J ξ‖ ≤ d n) (n : ℕ) :
    ‖ξ - matrixStageCentralProjection (centralRefinementIterates E₀ F n) J ξ‖ ≤
      ∑ i ∈ Finset.range n, d i := by
  induction n with
  | zero => simp only [centralRefinementIterates_zero,hfix,sub_self,norm_zero,
      Finset.sum_range_zero,le_refl]
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have hm := hmove n (centralRefinementIterates E₀ F n)
    have ht := dist_triangle ξ
      (matrixStageCentralProjection (centralRefinementIterates E₀ F n) J ξ)
      (matrixStageCentralProjection (centralRefinementIterates E₀ F (n+1)) J ξ)
    rw [centralRefinementIterates_succ] at ht ⊢
    simp only [dist_eq_norm] at ht
    exact ht.trans (add_le_add ih hm)

theorem central_refinement_sequence_of_refiners
    (J : H ≃ₗᵢ⋆[ℂ] H) (ξ : H) (E₀ : FiniteMatrixStage M)
    (hfix : matrixStageCentralProjection E₀ J ξ = ξ)
    (η : ℕ → H) (δ : ℝ) (hδ : 0 < δ)
    (F : ℕ → FiniteMatrixStage M → FiniteMatrixStage M)
    (hF : ∀ n E, E.units.concreteAlgebra ≤ (F n E).units.concreteAlgebra)
    (hmove : ∀ n E, ‖matrixStageCentralProjection E J ξ -
      matrixStageCentralProjection (F n E) J ξ‖ ≤ correctionScale (δ / 2) n)
    (htest : ∀ n E i, i < n + 1 → ∃ c : ℂ,
      ‖matrixStageCentralProjection (F n E) J (η i) -
        c • matrixStageCentralProjection (F n E) J ξ‖ ≤ correctionScale 1 n) :
    ∃ A : ℕ → FiniteMatrixStage M,
      Monotone (fun n => (A n).units.concreteAlgebra) ∧
      (∀ n, ‖ξ - matrixStageCentralProjection (A n) J ξ‖ ≤ δ) ∧
      ∀ n i, i ≤ n → ∃ c : ℂ,
        ‖matrixStageCentralProjection (A n) J (η i) -
          c • matrixStageCentralProjection (A n) J ξ‖ ≤ correctionScale 1 n := by
  refine ⟨fun n => centralRefinementIterates E₀ F (n+1),?_,?_,?_⟩
  · intro m n hmn
    exact centralRefinementIterates_mono E₀ F hF (Nat.add_le_add_right hmn 1)
  · intro n
    exact (centralRefinementIterates_displacement J ξ E₀ hfix F _ hmove (n+1)).trans
      ((correctionScale_partial_sum (half_pos hδ).le (n+1)).trans_eq (by ring))
  · intro n i hi
    dsimp only
    rw [centralRefinementIterates_succ]
    exact htest n _ i (Nat.lt_succ_iff.mpr hi)

theorem exists_central_refinement_sequence
    (J : H ≃ₗᵢ⋆[ℂ] H) (ξ : H)
    (hstep : ∀ (E : FiniteMatrixStage M) (η : H) (δ ε : ℝ), 0 < δ → 0 < ε →
      ∃ F : FiniteMatrixStage M, E.units.concreteAlgebra ≤ F.units.concreteAlgebra ∧
        ‖matrixStageCentralProjection E J ξ - matrixStageCentralProjection F J ξ‖ ≤ δ ∧
        ∃ c : ℂ, ‖matrixStageCentralProjection F J η -
          c • matrixStageCentralProjection F J ξ‖ ≤ ε)
    (E₀ : FiniteMatrixStage M) (hfix : matrixStageCentralProjection E₀ J ξ = ξ)
    (η : ℕ → H) (δ : ℝ) (hδ : 0 < δ) :
    ∃ A : ℕ → FiniteMatrixStage M,
      Monotone (fun n => (A n).units.concreteAlgebra) ∧
      (∀ n, ‖ξ - matrixStageCentralProjection (A n) J ξ‖ ≤ δ) ∧
      ∀ n i, i ≤ n → ∃ c : ℂ,
        ‖matrixStageCentralProjection (A n) J (η i) -
          c • matrixStageCentralProjection (A n) J ξ‖ ≤ correctionScale 1 n := by
  have hdpos (n : ℕ) : 0 < correctionScale (δ / 2) n := by
    dsimp [correctionScale]
    positivity
  have hepos (n : ℕ) : 0 < correctionScale 1 n := by
    dsimp [correctionScale]
    positivity
  have hall (n : ℕ) (E : FiniteMatrixStage M) :=
    exists_finite_central_refinement J ξ hstep η (n + 1) E
      (correctionScale (δ / 2) n) (correctionScale 1 n) (hdpos n) (hepos n)
  choose F hF hmove htest using hall
  exact central_refinement_sequence_of_refiners J ξ E₀ hfix η δ hδ F hF hmove htest

end

end KadisonKastler

end OAI
