import Mathlib
import OAI.Probability.LogConcave.Sampling.ConditionalMeanArray
import OAI.Probability.LogConcave.Sampling.InnerBasisCoordinate

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open scoped Classical BigOperators RealInnerProductSpace
open TensorEnergy

def harmonicKernel (d : ℕ) : Point d → Point d →L[ℝ] Point d :=
  fun _ => -(ContinuousLinearMap.id ℝ (Point d))
def harmonicSkew (d : ℕ) := jointSkew (harmonicKernel d) 1

lemma harmonicKernel_strong {d : ℕ} (H : Point d → ℝ) (u : Point d) :
    tensorAdjoint H (EuclideanSpace.basisFun (Fin d) ℝ)
      (fun i y => inner ℝ u (harmonicKernel d y (EuclideanSpace.basisFun (Fin d) ℝ i)))=
      fun y => inner ℝ u (-gradient H y) := by
  funext y
  simp only [tensorAdjoint,adjointCoordinate,harmonicKernel,neg_apply,
    ContinuousLinearMap.id_apply,inner_neg_right]
  simp only [directional,fderiv_fun_const,Pi.zero_apply,zero_apply,neg_zero,zero_add]
  change (∑i : Fin d,directional (EuclideanSpace.basisFun (Fin d) ℝ i) H y*
    (-inner ℝ u (EuclideanSpace.basisFun (Fin d) ℝ i)))= -inner ℝ u (gradient H y)
  have hcu (i : Fin d) : inner ℝ u (EuclideanSpace.basisFun (Fin d) ℝ i)=u i := by
    rw [real_inner_comm]
    exact inner_basis_coordinate u i
  simp only [directional_basis_gradient,hcu,mul_neg,Finset.sum_neg_distrib]
  congr 1

lemma harmonicSkew_field {d : ℕ} {H : Point d → ℝ} (hH : Differentiable ℝ H)
    (y : Point (d+d)) :
    productPointEquiv d d (skewLieField (productPotential H (fun z : Point d => ‖z‖^2/2))
      (harmonicSkew d) y)=((productPointEquiv d d y).2,-gradient H (productPointEquiv d d y).1) := by
  have ha (z : Point d) : (harmonicKernel d z).adjoint=-(ContinuousLinearMap.id ℝ (Point d)) := by
    change ContinuousLinearMap.adjoint (-(ContinuousLinearMap.id ℝ (Point d)))=_
    rw [map_neg,ContinuousLinearMap.adjoint_id]
  have h := jointSkew_field (K:=harmonicKernel d) (m:=fun z => -gradient H z)
    hH (fun _ _ => by simpa only [harmonicKernel] using (differentiable_const _)) (harmonicKernel_strong H) 1 y
  simpa only [harmonicSkew,skewCenteringField,ha,inv_one,one_smul,neg_smul,
    neg_apply,ContinuousLinearMap.id_apply,neg_neg] using h
end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open scoped Classical BigOperators RealInnerProductSpace
open TensorEnergy

lemma harmonicKernel_spatial_bound {d n : ℕ} (y : Point d) :
    AllSplitBound (spatialTensor (fun c z => matrixArray d (harmonicKernel d z) c)
      (List.finRange n) y) 1 := by
  have hh := ((allSplitBound_spatial_delta (d:=d) (List.finRange n) (by simp)).reindex
    (Equiv.sumAssoc (Fin n) Unit Unit)).abs_const_mul (-1)
  have he : spatialTensor (fun c z => matrixArray d (harmonicKernel d z) c) (List.finRange n) y=
      fun c => (-1:ℝ)*(if List.finRange n=[] then
        (if c (.inr (.inl ()))=c (.inr (.inr ())) then (1:ℝ) else 0) else 0) := by
    funext c
    unfold spatialTensor
    simp only [matrixArray_apply,harmonicKernel,neg_apply,ContinuousLinearMap.id_apply,
      inner_neg_right,EuclideanSpace.basisFun_inner,JetCalculus.jet_const]
    by_cases hn : List.finRange n=[] <;> simp [hn,EuclideanSpace.basisFun_apply,eq_comm]
    split_ifs <;> norm_num
  rw [he]
  apply hh.mono
  · split_ifs <;> norm_num
  · split_ifs <;> norm_num

lemma harmonicSkew_polySmooth (d : ℕ) : ∀c,PolySmooth (harmonicSkew d c) :=
  jointSkew_polySmooth (fun _ _ => PolySmooth.const _) 1

lemma harmonicSkew_scaled_bound (d : ℕ) : ∀k y,
    AllSplitBound (spatialTensor (harmonicSkew d) (List.finRange k) y) ((2:ℝ)*1*1^k) := by
  intro k y
  simpa only [harmonicSkew,inv_one,abs_one,mul_one,one_pow] using
    jointSkew_spatial_bound (n:=k) (K:=harmonicKernel d) (fun _ => by simpa only [harmonicKernel] using (contDiff_const (c:=_)))
      (by norm_num : (0:ℝ)≤1) harmonicKernel_spatial_bound 1 y
end LogConcaveSampling

end

end

end

end OAI
