import OAI.Combinatorics.Crossing.EvaluationAmbient
import OAI.Combinatorics.Crossing.SubspaceProjection
import OAI.Combinatorics.Crossing.PolynomialLinearMatrix

namespace OAI

noncomputable section
namespace Zarankiewicz
open PolynomialModule Module Submodule
variable {W ι : Type*} [AddCommGroup W] [Module ℝ W] [FiniteDimensional ℝ W]
variable (U : ι → Submodule ℝ W) (node : ι → ℝ)

theorem off_node_projected_rank (V : Submodule ℝ W) (h : ℕ) (t : ℝ)
    (ht : ∀ i, node i ≠ t) :
    finrank ℝ ((ambientEvalRange U node ⊤ (h+1) t).map V.mkQ) + rankIncrement U node V h ≤
      rankIncrement U node ⊤ h := by
  have hh := finrank_map_add_le V.mkQ
    (ambientEvalRange U node ⊤ (h+1) t) (ambientEvalRange U node V (h+1) t)
    (ambientEvalRange_mono_coeff U node le_top (h+1) t)
    (by rw [Submodule.ker_mkQ]; exact ambientEvalRange_le_coeff U node V (h+1) t)
  rwa [finrank_ambientEvalRange_off_node U node V h t ht,
    finrank_ambientEvalRange_off_node U node ⊤ h t ht] at hh

theorem node_rank_loss [Fintype ι] (V : Submodule ℝ W) (j : ι)
    (hUV : Disjoint (U j) V) (h : ℕ) (tstar : ℝ) (htstar : ∀ i, node i ≠ tstar) :
    finrank ℝ (ambientEvalRange U node ⊤ (h+1) (node j)) + rankIncrement U node V h ≤
      rankIncrement U node ⊤ h := by
  classical
  let bP := finBasis ℝ (constrained U node ⊤ (h+1))
  let bQ := finBasis ℝ (W ⧸ V)
  let f : (⊤ : Submodule ℝ W) →ₗ[ℝ] (W ⧸ V) := V.mkQ.comp (⊤ : Submodule ℝ W).subtype
  let F : constrained U node ⊤ (h+1) →ₗ[ℝ] PolynomialModule ℝ (W ⧸ V) :=
    (PolynomialModule.map ℝ f).comp (constrained U node ⊤ (h+1)).subtype
  let M := polynomialLinearMatrix bP bQ F
  have heval (t : ℝ) : (eval t).comp F = V.mkQ.comp (ambientEval U node ⊤ (h+1) t) := by
    apply LinearMap.ext
    intro p
    change eval t (PolynomialModule.map ℝ f p.val) = f (eval t p.val)
    simpa using PolynomialModule.eval_map ℝ f p.val t
  have hrank (t : ℝ) : (M.map (Polynomial.eval t)).rank =
      finrank ℝ ((ambientEvalRange U node ⊤ (h+1) t).map V.mkQ) := by
    rw [polynomialLinearMatrix_rank, heval, LinearMap.range_comp]
    rfl
  let nodes := Finset.univ.image node
  have hoff (t : ℝ) (ht : t ∉ nodes) : (M.map (Polynomial.eval t)).rank ≤
      rankIncrement U node ⊤ h - rankIncrement U node V h := by
    rw [hrank]
    apply Nat.le_sub_of_add_le
    apply off_node_projected_rank U node V h t
    intro i hi
    exact ht (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, hi⟩)
  have hnode := polynomial_rank_specialization M nodes
    (rankIncrement U node ⊤ h - rankIncrement U node V h) hoff (node j)
  rw [hrank] at hnode
  have hdisj : Disjoint (ambientEvalRange U node ⊤ (h+1) (node j)) (LinearMap.ker V.mkQ) := by
    rw [Submodule.ker_mkQ]
    exact hUV.mono_left (ambientEvalRange_at_node_le U node ⊤ (h+1) j)
  rw [finrank_map_of_disjoint V.mkQ _ hdisj] at hnode
  have hmono := Submodule.finrank_mono
    (ambientEvalRange_mono_coeff U node (show V ≤ ⊤ from le_top) (h+1) tstar)
  rw [finrank_ambientEvalRange_off_node U node V h tstar htstar,
    finrank_ambientEvalRange_off_node U node ⊤ h tstar htstar] at hmono
  omega

end Zarankiewicz

end

end OAI
