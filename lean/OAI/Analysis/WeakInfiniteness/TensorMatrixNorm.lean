import Mathlib
import OAI.Analysis.WeakInfiniteness.MatrixRepresentation

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace

namespace WeakPureInfiniteness

section BasisTensor

variable {n H K : Type*} [Fintype n]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]

def basisTensorMap (b : OrthonormalBasis n ℂ H) :
    PiLp 2 (fun _ : n => K) →ₗ[ℂ] H ⊗[ℂ] K where
  toFun x := ∑ i, b i ⊗ₜ[ℂ] x i
  map_add' x y := by simp [TensorProduct.tmul_add, Finset.sum_add_distrib]
  map_smul' c x := by simp [TensorProduct.tmul_smul, Finset.smul_sum]

lemma basisTensorMap_inner (b : OrthonormalBasis n ℂ H)
    (x y : PiLp 2 (fun _ : n => K)) :
    inner ℂ (basisTensorMap b x) (basisTensorMap b y) = inner ℂ x y := by
  classical
  simp [basisTensorMap, sum_inner, inner_sum, TensorProduct.inner_tmul, b.inner_eq_ite,
    PiLp.inner_apply]

def basisTensorIsometry (b : OrthonormalBasis n ℂ H) :
    PiLp 2 (fun _ : n => K) →ₗᵢ[ℂ] H ⊗[ℂ] K :=
  LinearMap.isometryOfInner (E := PiLp 2 (fun _ : n => K))
    (E' := H ⊗[ℂ] K) (𝕜 := ℂ) (basisTensorMap b) (fun x y => basisTensorMap_inner b x y)

lemma basisTensorMap_surjective (b : OrthonormalBasis n ℂ H) :
    Function.Surjective (basisTensorMap (K := K) b) := by
  intro z
  induction z using TensorProduct.inductionOn with
  | tmul h k =>
    refine ⟨WithLp.toLp 2 (fun i => (b.repr h i) • k), ?_⟩
    change ∑ i, b i ⊗ₜ[ℂ] ((b.repr h i) • k) = h ⊗ₜ[ℂ] k
    conv_rhs => rw [← b.sum_repr h]
    rw [TensorProduct.sum_tmul]
    simp only [TensorProduct.smul_tmul, TensorProduct.tmul_smul]
  | add z w hz hw =>
    obtain ⟨x, rfl⟩ := hz
    obtain ⟨y, rfl⟩ := hw
    exact ⟨x + y, map_add _ _ _⟩

def basisTensorEquiv (b : OrthonormalBasis n ℂ H) :
    PiLp 2 (fun _ : n => K) ≃ₗᵢ[ℂ] H ⊗[ℂ] K :=
  LinearIsometryEquiv.ofSurjective (basisTensorIsometry b) (basisTensorMap_surjective b)

@[simp]
lemma basisTensorEquiv_apply (b : OrthonormalBasis n ℂ H)
    (x : PiLp 2 (fun _ : n => K)) :
    basisTensorEquiv b x = ∑ i, b i ⊗ₜ[ℂ] x i := rfl

def tensorCoefficientMatrix {B : Type*} [AddCommGroup B] [Module ℂ B]
    (b : OrthonormalBasis n ℂ H) (T : H →L[ℂ] H) (a : B) : CStarMatrix n n B :=
  CStarMatrix.ofMatrix fun i j => (b.repr (T (b j)) i) • a

@[simp]
lemma tensorCoefficientMatrix_apply {B : Type*} [AddCommGroup B] [Module ℂ B]
    (b : OrthonormalBasis n ℂ H) (T : H →L[ℂ] H) (a : B) (i j : n) :
    tensorCoefficientMatrix b T a i j = (b.repr (T (b j)) i) • a := rfl

lemma tensorCoefficientMatrix_intertwining (b : OrthonormalBasis n ℂ H)
    (T : H →L[ℂ] H) (S : K →L[ℂ] K) (x : PiLp 2 (fun _ : n => K)) :
    basisTensorEquiv b (matrixOperator (tensorCoefficientMatrix b T S) x) =
      TensorProduct.mapL T S (basisTensorEquiv b x) := by
  simp only [basisTensorEquiv_apply, matrixOperator_apply, tensorCoefficientMatrix_apply,
    smul_apply, TensorProduct.tmul_sum, TensorProduct.tmul_smul,
    map_sum, TensorProduct.mapL_tmul]
  rw [Finset.sum_comm]
  congr 1
  funext j
  simpa only [TensorProduct.sum_tmul, ← TensorProduct.smul_tmul'] using
    congrArg (fun h : H => h ⊗ₜ[ℂ] S (x j)) (b.sum_repr (T (b j)))

lemma norm_eq_of_isometric_intertwining {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (e : E ≃ₗᵢ[ℂ] F) (T : E →L[ℂ] E) (S : F →L[ℂ] F)
    (h : ∀ x, e (T x) = S (e x)) : ‖T‖ = ‖S‖ := by
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro x
    rw [← e.norm_map (T x), h]
    simpa only [e.norm_map] using S.le_opNorm (e x)
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro y
    obtain ⟨x, rfl⟩ := e.surjective y
    rw [← h, e.norm_map, e.norm_map]
    exact T.le_opNorm x

lemma tensorCoefficientSum_intertwining {ι : Type*} (s : Finset ι)
    (b : OrthonormalBasis n ℂ H) (T : ι → H →L[ℂ] H) (S : ι → K →L[ℂ] K)
    (x : PiLp 2 (fun _ : n => K)) :
    basisTensorEquiv b (matrixOperator (∑ i ∈ s, tensorCoefficientMatrix b (T i) (S i)) x) =
      (∑ i ∈ s, TensorProduct.mapL (T i) (S i)) (basisTensorEquiv b x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [matrixOperator_zero]
  | @insert i s hi hs =>
    simp only [Finset.sum_insert hi, matrixOperator_add, add_apply,
      map_add, tensorCoefficientMatrix_intertwining, hs]

lemma norm_tensorCoefficientSum [CompleteSpace K] {ι : Type*} (s : Finset ι)
    (b : OrthonormalBasis n ℂ H) (T : ι → H →L[ℂ] H) (S : ι → K →L[ℂ] K) :
    ‖∑ i ∈ s, TensorProduct.mapL (T i) (S i)‖ =
      ‖∑ i ∈ s, tensorCoefficientMatrix b (T i) (S i)‖ := by
  rw [← norm_matrixOperator]
  exact (norm_eq_of_isometric_intertwining (basisTensorEquiv b) _ _
    (tensorCoefficientSum_intertwining s b T S)).symm

end BasisTensor

end WeakPureInfiniteness
end

end OAI
