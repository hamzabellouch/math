import OAI.Analysis.Pureness.States.ScalarTracialUltraproductValue
import OAI.Analysis.Pureness.States.NormalizedMatrixStateUltraRank
import OAI.Analysis.Pureness.Tensor.CommutingFaithfulProducts
import OAI.Analysis.Pureness.Tensor.CommutingStarTensor

namespace OAI
noncomputable section
namespace CuntzPureness
open CuntzTrace OrderedSemigroup Filter
open scoped Topology NNReal ENNReal ComplexOrder TensorProduct
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] [Nontrivial A]
variable (hsimple : TopologicallySimple A) (y : finiteCuntzSubmonoid (A := A)) (hy : y ≠ 0) (f : StateSpace y)
variable (U : Ultrafilter ℕ)

def matrixStateScalarTensorHom :
    A ⊗[ℂ] ScalarTracialMatrixUltraproduct U →⋆ₐ[ℂ] NormalizedMatrixStateUltraAW hsimple y hy f U :=
  commutingStarTensorHom (matrixStateDiagonalAWEmbedding hsimple y hy f U)
    (scalarTracialMatrixAWEmbedding hsimple y hy f U)
    (scalarTracialMatrixAWEmbedding_commute hsimple y hy f U)

lemma matrixStateScalarTensorHom_tmul (a : A) (z : ScalarTracialMatrixUltraproduct U) :
    matrixStateScalarTensorHom hsimple y hy f U (a ⊗ₜ[ℂ] z) =
      matrixStateDiagonalAWEmbedding hsimple y hy f U a *
        scalarTracialMatrixAWEmbedding hsimple y hy f U z := rfl

lemma matrixStateScalarTensorHom_tmul_eq_zero (a : A) (z : ScalarTracialMatrixUltraproduct U) :
    matrixStateScalarTensorHom hsimple y hy f U (a ⊗ₜ[ℂ] z)=0 ↔ a=0 ∨ z=0 := by
  rw [matrixStateScalarTensorHom_tmul]
  exact commuting_embeddings_mul_eq_zero_iff hsimple
    (matrixStateDiagonalAWEmbedding hsimple y hy f U)
    (scalarTracialMatrixAWEmbedding hsimple y hy f U)
    (scalarTracialMatrixAWEmbedding_injective hsimple y hy f U)
    (scalarTracialMatrixAWEmbedding_commute hsimple y hy f U) a z

lemma matrixStateScalarTensorHom_norm_square (z : A ⊗[ℂ] ScalarTracialMatrixUltraproduct U) :
    ‖matrixStateScalarTensorHom hsimple y hy f U (star z*z)‖ =
      ‖matrixStateScalarTensorHom hsimple y hy f U z‖^2 := by
  let φ := matrixStateScalarTensorHom hsimple y hy f U
  change ‖φ (star z*z)‖ = ‖φ z‖^2
  calc
    _ = ‖φ (star z)*φ z‖ := congrArg norm (φ.map_mul' (star z) z)
    _ = ‖star (φ z)*φ z‖ := congrArg (fun t => ‖t*φ z‖) (φ.map_star' z)
    _ = ‖φ z‖^2 := (CStarRing.norm_star_mul_self (x := φ z)).trans (pow_two ‖φ z‖).symm

lemma matrixStateScalarTensorHom_sum_norm_le {κ : Type*} (s : Finset κ)
    (a : κ → A) (v : κ → lp (fun n : ℕ => FinMatrix ℂ (n+1)) ∞)
    (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ n, ‖∑ i ∈ s, scalarMatrixHom (a i) * scalarCoefficientMatrixHom (A := A) (v i n)‖ ≤ C) :
    ‖matrixStateScalarTensorHom hsimple y hy f U
      (∑ i ∈ s, a i ⊗ₜ[ℂ] filteredQuasitraceQuotientMap scalarMatrixPositiveTrace (U : Filter ℕ)
        scalarMatrixPositiveTrace_metricSize_add scalarMatrixPositiveTrace_unit (v i))‖ ≤ C := by
  let w : lp (fun n : ℕ => FinMatrix A (n+1)) ∞ :=
    ∑ i ∈ s, matrixStateDiagonalProduct (a i)*scalarCoefficientProductHom (v i)
  let φ := ultralimitCompletionMap (normalizedMatrixStatePositiveQuasitrace hsimple y hy f) U
    (normalizedMatrixStatePositiveQuasitrace_unit hsimple y hy f)
    (normalizedMatrixStatePositiveQuasitrace_metricSize_add hsimple y hy f)
  have he : matrixStateScalarTensorHom hsimple y hy f U
      (∑ i ∈ s, a i ⊗ₜ[ℂ] filteredQuasitraceQuotientMap scalarMatrixPositiveTrace (U : Filter ℕ)
        scalarMatrixPositiveTrace_metricSize_add scalarMatrixPositiveTrace_unit (v i)) = φ w := by
    simp only [map_sum,matrixStateScalarTensorHom_tmul,w,map_mul,scalarTracialMatrixAWEmbedding_map]
    rfl
  rw [he]
  apply (NonUnitalStarAlgHom.norm_apply_le φ.toNonUnitalStarAlgHom w).trans
  apply lp.norm_le_of_forall_le hC
  intro n
  have hd (i : κ) : matrixStateDiagonalProduct (a i) n =
      (scalarMatrixHom (ι := Fin (n+1)) (a i)) := rfl
  have hv (i : κ) : scalarCoefficientProductHom (A := A) (v i) n =
      scalarCoefficientMatrixHom (A := A) (v i n) := rfl
  simpa only [w,lp.coeFn_sum,Finset.sum_apply,lp.infty_coeFn_mul,Pi.mul_apply,hd,hv] using hb n
end CuntzPureness

end

end OAI
