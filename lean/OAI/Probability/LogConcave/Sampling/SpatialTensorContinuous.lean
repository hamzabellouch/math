import Mathlib
import OAI.Probability.LogConcave.Sampling.ScoreAugmented
import OAI.Probability.LogConcave.JetEstimates.SplitBundle

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open Function
open scoped Classical BigOperators RealInnerProductSpace

lemma spatialTensor_continuous {d n : ℕ} {X : ℝ × Point d → Point d}
    (hX : ContDiff ℝ (⊤:ℕ∞) X) (y : Point d) :
    Continuous (fun u => TensorEnergy.multilinearTensor
      (iteratedFDeriv ℝ n (fun z => X (u,z)) y)) := by
  apply continuous_pi
  intro c
  let L := innerSL ℝ (EuclideanSpace.basisFun (Fin d) ℝ (c (Sum.inl ()) ))
  have hA := L.contDiff.comp hX
  have he : (fun u => TensorEnergy.multilinearTensor (iteratedFDeriv ℝ n (fun z => X (u,z)) y) c)=
      fun u => JetCalculus.jet (fun i : Fin n => (0,EuclideanSpace.basisFun (Fin d) ℝ (c (Sum.inr i))))
        (List.finRange n) (L ∘ X) (u,y) := by
    funext u
    have hs : ContDiff ℝ (⊤:ℕ∞) (fun z => X (u,z)) := hX.comp (contDiff_const.prodMk contDiff_id)
    rw [multilinearTensor_iterated_eq_jet hs]
    exact congrFun (JetCalculus.jet_right_slice_at (fun z => hA.contDiffAt) _ _) y
  rw [he]
  exact (JetCalculus.smooth_jet hA _ _).continuous.comp (continuous_id.prodMk continuous_const)

namespace TensorEnergy
lemma allSplitBound_subsingleton {S : Type*} [Fintype S] [Subsingleton S]
    {d : ℕ} (A : (S → Fin d) → ℝ) (M : ℝ) : AllSplitBound A M := by
  intro I O _ _ _ _ hi ho e
  obtain ⟨i⟩ := hi
  obtain ⟨o⟩ := ho
  have h := congrArg e (Subsingleton.elim (e.symm (Sum.inl i)) (e.symm (Sum.inr o)))
  simp only [Equiv.apply_symm_apply] at h
  exact (Sum.inl_ne_inr h).elim

lemma allSplitBound_zero {S : Type*} [Fintype S] {d : ℕ} :
    AllSplitBound (fun _ : S → Fin d => (0:ℝ)) 0 := by
  intro I O _ _ _ _ _ _ e v
  simp

lemma multilinearTensor_id_one {d : ℕ} (y : Point d) :
    AllSplitBound (multilinearTensor (iteratedFDeriv ℝ 1 (id : Point d → Point d) y)) 1 := by
  have hh := (allSplitBound_delta (d:=d)).reindex
    ((Equiv.refl Unit).sumCongr (Equiv.ofUnique (Fin 1) Unit)).symm
  convert hh using 1
  funext c
  simp [multilinearTensor,EuclideanSpace.basisFun,PiLp.inner_apply,EuclideanSpace.single,
    Equiv.ofUnique]

lemma multilinearTensor_id_higher {d n : ℕ} (y : Point d) :
    multilinearTensor (iteratedFDeriv ℝ (n+2) (id : Point d → Point d) y)=0 := by
  funext c
  simp only [multilinearTensor,iteratedFDeriv_succ_apply_right,fderiv_id,
    iteratedFDeriv_succ_const,Pi.zero_apply,zero_apply]
  simp

lemma multilinearTensor_id_bound {d n : ℕ} (y : Point d) :
    AllSplitBound (multilinearTensor (iteratedFDeriv ℝ n (id : Point d → Point d) y)) 1 := by
  cases n with
  | zero =>
    let : Subsingleton (Unit ⊕ Fin 0) := ⟨by intro a b; cases a with
      | inl a => cases b with
        | inl b => rfl
        | inr b => exact Fin.elim0 b
      | inr a => exact Fin.elim0 a⟩
    exact allSplitBound_subsingleton _ _
  | succ n =>
    cases n with
    | zero => exact multilinearTensor_id_one y
    | succ n =>
      rw [show n+1+1=n+2 by omega,multilinearTensor_id_higher]
      exact allSplitBound_zero.mono (by norm_num) (by norm_num)
end TensorEnergy
end LogConcaveSampling

end

end

end

end OAI
