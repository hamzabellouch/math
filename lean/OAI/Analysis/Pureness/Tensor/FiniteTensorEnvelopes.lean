import OAI.Analysis.Pureness.Tensor.SpatialTensorMaps
import OAI.Analysis.Pureness.Operators.FiniteHilbertFrames
import Mathlib.Analysis.InnerProductSpace.PiL2

namespace OAI
noncomputable section
namespace CuntzPureness
open CuntzComparison CuntzTrace
open scoped TensorProduct InnerProductSpace
variable {H K : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

lemma finiteFrameSynthesis_reconstruction {n : ℕ} (e : Fin n → K) (x : K) :
    finiteFrameSynthesis e ((finiteFrameSynthesis e).adjoint x) =
      ∑ i, inner ℂ (e i) x • e i := by
  rw [finiteFrameSynthesis_adjoint_apply, map_sum]
  simp only [map_smul, finiteFrameSynthesis_standard]

theorem exists_finiteFrame_fix (s : Set K) (hs : s.Finite) :
    ∃ (n : ℕ) (e : Fin n → K), Orthonormal ℂ e ∧
      ∀ y ∈ s, finiteFrameSynthesis e ((finiteFrameSynthesis e).adjoint y) = y := by
  let V := Submodule.span ℂ s
  let : FiniteDimensional ℂ V := FiniteDimensional.span_of_finite ℂ hs
  let b := stdOrthonormalBasis ℂ V
  let e : Fin (Module.finrank ℂ V) → K := fun i => (b i : K)
  have he : Orthonormal ℂ e := by
    rw [orthonormal_iff_ite]
    intro i j
    exact (orthonormal_iff_ite.mp b.orthonormal) i j
  refine ⟨_, e, he, ?_⟩
  intro y hy
  rw [finiteFrameSynthesis_reconstruction]
  let v : V := ⟨y, Submodule.subset_span hy⟩
  have hb := congrArg (fun v : V => (v : K)) (b.sum_repr' v)
  simpa only [Submodule.coe_sum, Submodule.coe_smul_of_tower, Submodule.coe_inner, e, v] using hb

omit [CompleteSpace K] in
lemma spatialTensor_coe_sum {ι : Type*} (s : Finset ι) (f : ι → H ⊗[ℂ] K) :
    ((∑ i ∈ s, f i : H ⊗[ℂ] K) : SpatialHilbert H K) =
      ∑ i ∈ s, (f i : SpatialHilbert H K) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [UniformSpace.Completion.coe_zero]
  | @insert i s hi ih => simp [hi, UniformSpace.Completion.coe_add, ih]

theorem exists_finiteFrame_fix_tensors (v w : H ⊗[ℂ] K) :
    ∃ (n : ℕ) (e : Fin n → K), Orthonormal ℂ e ∧
      spatialTensorMap (.id ℂ H)
        ((finiteFrameSynthesis e).comp (finiteFrameSynthesis e).adjoint) v = v ∧
      spatialTensorMap (.id ℂ H)
        ((finiteFrameSynthesis e).comp (finiteFrameSynthesis e).adjoint) w = w := by
  obtain ⟨nv, xv, yv, rfl⟩ := TensorProduct.exists_sum_tmul_eq v
  obtain ⟨nw, xw, yw, rfl⟩ := TensorProduct.exists_sum_tmul_eq w
  obtain ⟨n, e, he, hfix⟩ := exists_finiteFrame_fix
    (Set.range yv ∪ Set.range yw) ((Set.finite_range yv).union (Set.finite_range yw))
  refine ⟨n, e, he, ?_, ?_⟩
  · simp only [spatialTensor_coe_sum, map_sum, spatialTensorMap_tmul,
      ContinuousLinearMap.id_apply, ContinuousLinearMap.comp_apply]
    apply Finset.sum_congr rfl
    intro i _
    rw [hfix (yv i) (Set.mem_union_left _ (Set.mem_range_self i))]
  · simp only [spatialTensor_coe_sum, map_sum, spatialTensorMap_tmul,
      ContinuousLinearMap.id_apply, ContinuousLinearMap.comp_apply]
    apply Finset.sum_congr rfl
    intro i _
    rw [hfix (yw i) (Set.mem_union_right _ (Set.mem_range_self i))]

variable [CompleteSpace H]
variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]

theorem spatialStarTensor_preserves_algebraic
    (α : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (β : B →⋆ₐ[ℂ] (K →L[ℂ] K))
    (z : A ⊗[ℂ] B) (v : H ⊗[ℂ] K) :
    ∃ w : H ⊗[ℂ] K, spatialStarTensorHom α β z v = w := by
  induction z using TensorProduct.inductionOn with
  | add x y hx hy =>
    obtain ⟨u, hu⟩ := hx
    obtain ⟨w, hw⟩ := hy
    exact ⟨u + w, by simp [hu, hw, UniformSpace.Completion.coe_add]⟩
  | tmul a b =>
    exact ⟨TensorProduct.mapL (α a) (β b) v, by simp [spatialStarTensorHom_tmul]⟩
end CuntzPureness

end

end OAI
