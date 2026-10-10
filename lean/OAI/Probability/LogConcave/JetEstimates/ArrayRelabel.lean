import Mathlib
import OAI.Probability.LogConcave.Sampling.SpatialTensorArrayBound
import OAI.Probability.LogConcave.JetEstimates.MatrixArray

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling.TensorEnergy
open scoped Classical BigOperators RealInnerProductSpace

def arrayRelabel {d : ℕ} {S T : Type} [Fintype S] [DecidableEq S]
    [Fintype T] [DecidableEq T] (e : S ≃ T) :
    ((S → Fin d) → ℝ) →L[ℝ] ((T → Fin d) → ℝ) :=
  ContinuousLinearMap.pi (fun c => ContinuousLinearMap.proj (c ∘ e))

lemma arrayTensor_relabel {d n : ℕ} {S T : Type} [Fintype S] [DecidableEq S]
    [Fintype T] [DecidableEq T] (e : S ≃ T)
    {f : Point d → (S → Fin d) → ℝ} (hf : ContDiff ℝ (⊤:ℕ∞) f) (y : Point d)
    (c : T ⊕ Fin n → Fin d) :
    arrayTensor (iteratedFDeriv ℝ n ((arrayRelabel e) ∘ f) y) c=
      arrayTensor (iteratedFDeriv ℝ n f y) (c ∘ Equiv.sumCongr e (Equiv.refl (Fin n))) := by
  rw [(arrayRelabel e).iteratedFDeriv_comp_left hf.contDiffAt
    (by exact_mod_cast (le_top : (n:ℕ∞)≤⊤))]
  rfl

lemma AllSplitBound.array_relabel {d n : ℕ} {S T : Type} [Fintype S] [DecidableEq S]
    [Fintype T] [DecidableEq T] (e : S ≃ T)
    {f : Point d → (S → Fin d) → ℝ} (hf : ContDiff ℝ (⊤:ℕ∞) f) (y : Point d) {B : ℝ}
    (h : AllSplitBound (arrayTensor (iteratedFDeriv ℝ n f y)) B) :
    AllSplitBound (arrayTensor (iteratedFDeriv ℝ n ((arrayRelabel e) ∘ f) y)) B := by
  have hh := h.reindex (Equiv.sumCongr e (Equiv.refl (Fin n)))
  convert hh using 1
  ext c
  exact arrayTensor_relabel e hf y c

lemma matrixArray_comp {d : ℕ} (A B : Point d →L[ℝ] Point d) :
    matrixArray d (A.comp B)=singleContract (matrixArray d A)
      (arrayRelabel (Equiv.sumComm Unit Unit) (matrixArray d B)) := by
  funext c
  let v := B (EuclideanSpace.basisFun (Fin d) ℝ (c (Sum.inr ())))
  have he := (EuclideanSpace.basisFun (Fin d) ℝ).sum_repr v
  have hh := congrArg (fun z => inner ℝ (EuclideanSpace.basisFun (Fin d) ℝ (c (Sum.inl ()))) (A z)) he
  simpa only [map_sum,map_smul,inner_sum,real_inner_smul_right,
    OrthonormalBasis.repr_apply_apply,real_inner_comm,singleContract,
    matrixArray_apply,arrayRelabel,ContinuousLinearMap.pi_apply,
    ContinuousLinearMap.proj_apply,Function.comp_apply,Equiv.sumComm_apply,
    Sum.swap_inl,Sum.swap_inr,Sum.elim_inl,Sum.elim_inr,mul_comm,v,ContinuousLinearMap.comp_apply] using hh.symm

lemma matrixComposition_split {d n : ℕ} {f g : Point d → Point d →L[ℝ] Point d}
    (hf : ContDiff ℝ (⊤:ℕ∞) f) (hg : ContDiff ℝ (⊤:ℕ∞) g)
    (A B : ℕ → ℝ) (hA : ∀k,0≤A k) (hB : ∀k,0≤B k) (y : Point d)
    (ha : ∀k≤n,AllSplitBound (arrayTensor (iteratedFDeriv ℝ k ((matrixArray d) ∘ f) y)) (A k))
    (hb : ∀k≤n,AllSplitBound (arrayTensor (iteratedFDeriv ℝ k ((matrixArray d) ∘ g) y)) (B k)) :
    AllSplitBound (arrayTensor (iteratedFDeriv ℝ n (fun z => matrixArray d ((f z).comp (g z))) y))
      (∑s∈(Finset.univ : Finset (Fin n)).powerset,A s.card*B (n-s.card)) := by
  have hfg := (matrixArray d).contDiff.comp hf
  have hgg := (matrixArray d).contDiff.comp hg
  have hh := LogConcaveSampling.arrayBound_spatialContract hfg
    ((arrayRelabel (Equiv.sumComm Unit Unit)).contDiff.comp hgg) A B hA hB y ha
    (fun k hk => AllSplitBound.array_relabel (Equiv.sumComm Unit Unit) hgg y (hb k hk))
  have he : (fun z => matrixArray d ((f z).comp (g z)))=
      fun z => singleContract (matrixArray d (f z))
        (arrayRelabel (Equiv.sumComm Unit Unit) (matrixArray d (g z))) :=
    funext (fun z => matrixArray_comp (f z) (g z))
  rw [he]
  exact hh
end LogConcaveSampling.TensorEnergy

end

end

end

end OAI
