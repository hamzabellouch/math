import OAI.Analysis.Quantum.PPTSquare.ExplicitMaps

namespace OAI

noncomputable section
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
open Matrix
namespace ExplicitPencil
open ChannelCompletion TensorCriterion
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
open Matrix

lemma gram_identity (x : Fin 4 → ℂ) : L (projector x) = (pencil x)ᴴ * pencil x := by
  simp only [L_apply, projector, Matrix.vecMulVec_apply, Pi.star_apply, pencil,
    Matrix.conjTranspose_sum, Matrix.conjTranspose_smul, Matrix.sum_mul, Matrix.mul_sum,
    Matrix.smul_mul, Matrix.mul_smul, M_real, Finset.smul_sum, smul_smul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [M_symmetry]

lemma rank_identity (x : Fin 4 → ℂ) : (L (projector x)).rank = (pencil x).rank := by
  rw [gram_identity, Matrix.rank_conjTranspose_mul_self]

lemma positive_test_matrix : L (Matrix.single 0 0 1) = 36 • (1 : Mat (Fin 4)) := by
  rw [L_single]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [M, data, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply]

lemma e0_projector : projector (Pi.single (0 : Fin 4) (1 : ℂ)) = Matrix.single 0 0 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [projector, Matrix.vecMulVec_apply, Pi.single_apply, Matrix.single_apply]

lemma positive_test : (L (projector (Pi.single (0 : Fin 4) (1 : ℂ)))).PosDef := by
  rw [e0_projector, positive_test_matrix]
  exact Matrix.PosDef.one.smul (by norm_num : (0 : ℕ) < 36)

open ChannelCompletion TensorCriterion

theorem twenty_directions :
    ∃ X : Fin 20 → Fin 4 → ℂ, DistinctDirections X ∧
      (∀ i, X i 0 = 1) ∧ (∀ i, (pencil (X i)).rank < 4) ∧
      (∀ x : Fin 4 → ℂ, x ≠ 0 → ((pencil x).rank < 4 ↔
        ∃! i, ∃ c : ℂ, c ≠ 0 ∧ x = c • X i)) ∧ QuadraticEvaluations X := by
  obtain ⟨r,t,hr,hf,hu,he,ht,hm⟩ := PencilField.exists_complex_data
  obtain ⟨hit,_,hpoints⟩ := PencilPoints.affine_points r hr hf t hu he ht
  let X : Fin 20 → Fin 4 → ℂ := fun i => PencilDirections.point (t i)
  have hc := PencilDirections.exact_points t hit hpoints
  refine ⟨X, PencilDirections.distinct t hit, fun i => rfl, hc.1, hc.2, ?_⟩
  exact QuadraticEvaluation.at_most_nine t hm

theorem main_pair : PPT (Phi1 L) ∧ PPT (Phi2 L) ∧ Z L ≠ 0 ∧
    (∀ u v : Fin 10 → ℂ, (∃ w, (Z L).mulVec w = product u v) → product u v = 0) ∧
    ¬ EntanglementBreaking ((Phi2 L).comp (Phi1 L)) := by
  obtain ⟨X,hX,h0,hRank,hAll,hQuad⟩ := twenty_directions
  exact tensor_criterion L L_ppt X hX (fun i => by rw [rank_identity]; exact hRank i)
    hQuad ⟨Pi.single 0 1,positive_test⟩
open ChannelCompletion TensorCriterion

def Theta : Map (Space 10) (Space 10) := theta 10 (Phi1 L) (Phi2 L)

theorem main_channel : Fintype.card (Space 10) = 21 ∧ PPT Theta ∧ TracePreserving Theta ∧
    ¬ EntanglementBreaking (Theta.comp Theta) := by
  obtain ⟨h1,h2,hn,hp,hne⟩ := main_pair
  have hs : ¬ Separable (choi ((Phi2 L).comp (Phi1 L))) := by
    intro h
    obtain ⟨u,v,hne,w,hw⟩ := separable_nonzero_product h hn
    exact hne (hp u v ⟨w,hw⟩)
  obtain ⟨_,_,hd,_,_,hP,hT,_,hE⟩ := channel_completion 10 (Phi1 L) (Phi2 L) h1 h2
  exact ⟨hd,hP,hT,hE hs⟩
end ExplicitPencil

end

end OAI
