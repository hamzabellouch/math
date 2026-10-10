import OAI.Analysis.FreeEntropy.TensorMatrices

namespace OAI

noncomputable section
open Filter
open scoped Topology
namespace FiniteEntropySeparation
open FreeSeries FreeTensor
 theorem exists_tensor_matrix_models (p : ℕ) [NeZero p] (hp : 2≤p) :
    ∃ (D : ℕ → ℕ) (A : (k : ℕ) → Fin (p+1) → Matrix (Fin (D k)) (Fin (D k)) ℂ),
      (∀ k,0<D k) ∧ Tendsto D atTop atTop ∧
      (∀ k i,matrixOpNorm (A k i)≤64) ∧ (∀ k i,(A k i).IsHermitian) ∧
      ∀ w : List (Fin (p+1)), Tendsto (fun k => matrixTraceWord (A k) w) atTop (𝓝 (Model.signalMoments p w)) := by
  obtain ⟨D,A,hD0,hD,hA,hAH,hM⟩ := exists_free_matrix_models p
  let E := fun k => D k*p
  let T := fun k (i : Fin (p+1)) => tensorMatrixTuple (A k) ((optionFin p).symm i)
  refine ⟨E,T,fun k => Nat.mul_pos (hD0 k) (by omega),?_,?_,?_,?_⟩
  · apply tendsto_atTop_mono _ hD
    intro k
    dsimp [E]
    exact Nat.le_mul_of_pos_right _ (by omega)
  · intro k i; exact tensorMatrixTuple_norm_le hp (A k) (hA k) _
  · intro k i; exact tensorMatrixTuple_isHermitian (A k) (hAH k) _
  · intro w
    let v := w.map (optionFin p).symm
    have he : v.map (optionFin p)=w := by simp [v,List.map_map]
    have ht (k : ℕ) : matrixTraceWord (T k) w = matrixTraceWord (tensorMatrixTuple (A k)) v := by
      rw [matrixTraceWord_map]; rfl
    have hm : Model.signalMoments p w = FreeSeries.fockMoments p (v.filterMap id) *
        ((p:ℂ)⁻¹ * ∑ l : Fin p, (equidiscreteAtom p l:ℂ)^(v.count none)) := by
      rw [← he,Model.signal_option_moments, equidiscreteSignal_moments]
    simp only [ht,tensorMatrixTuple_moment,hm]
    exact (hM (v.filterMap id)).mul_const _
end FiniteEntropySeparation

end

end OAI
