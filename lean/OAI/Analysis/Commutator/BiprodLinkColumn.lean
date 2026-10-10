import Mathlib
import OAI.Analysis.Commutator.HilbertBiprodProjections
import OAI.Analysis.Commutator.HilbertFiniteMaps
import OAI.Analysis.Commutator.OrthogonalLinkSums

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder InnerProductSpace Topology

open Filter

namespace Kadison.BiprodLinkColumn

open HilbertBiprod PartialIsometryOrder HilbertFiniteMaps

variable {H G : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

variable (N : VonNeumannAlgebra (Space H G))

abbrev Intertwiner := Link N (right (H:=H) (G:=G)) left

omit [CompleteSpace H] [CompleteSpace G] in
lemma inl_norm_le : ‖inlL (H:=H) (G:=G)‖≤1 :=
  (inl (H:=H) (G:=G)).norm_toContinuousLinearMap_le

omit [CompleteSpace H] [CompleteSpace G] in
lemma inr_norm_le : ‖inrL (H:=H) (G:=G)‖≤1 :=
  (inr (H:=H) (G:=G)).norm_toContinuousLinearMap_le

def component (v : Intertwiner N) : H →L[ℂ] G :=
  (inrL (H:=H) (G:=G)).adjoint.comp (v.val.adjoint.comp inlL)

lemma component_adjoint (v : Intertwiner N) :
    (component N v).adjoint=(inlL (H:=H) (G:=G)).adjoint.comp (v.val.comp inrL) := by
  simp only [component,ContinuousLinearMap.adjoint_comp,ContinuousLinearMap.adjoint_adjoint,
    ContinuousLinearMap.comp_assoc]

lemma source_adjoint (v : Intertwiner N) :
    (right (H:=H) (G:=G)).comp v.val.adjoint=v.val.adjoint := by
  have hv : v.val.comp (right (H:=H) (G:=G))=v.val := by
    simpa only [ContinuousLinearMap.mul_def] using v.mul_source right_projection
  have h := congrArg (fun T : Space H G →L[ℂ] Space H G => T.adjoint) hv
  rw [ContinuousLinearMap.adjoint_comp] at h
  have hr : (right (H:=H) (G:=G)).adjoint=right := right_projection.isSelfAdjoint.star_eq
  simpa only [hr] using h

lemma inr_component (v : Intertwiner N) :
    (inrL (H:=H) (G:=G)).comp (component N v)=v.val.adjoint.comp inlL := by
  rw [component,←ContinuousLinearMap.comp_assoc,inr_adjoint,
    ←ContinuousLinearMap.comp_assoc,source_adjoint N v]

lemma component_square (v : Intertwiner N) :
    (component N v).adjoint.comp (component N v)=
      (inlL (H:=H) (G:=G)).adjoint.comp (v.final.comp inlL) := by
  rw [component_adjoint,ContinuousLinearMap.comp_assoc,ContinuousLinearMap.comp_assoc,
    inr_component]
  rfl

variable (S : Set (Intertwiner N)) (hS : OrthogonalLinks N right left S)

def finiteColumn (s : Finset S) : H →L[ℂ] Copies G s :=
  column s (fun v => component N v.val.val)

def compression (s : Finset S) : H →L[ℂ] H :=
  (inlL (H:=H) (G:=G)).adjoint.comp ((finiteProjection N right left S s).comp inlL)

lemma column_square (s : Finset S) :
    (finiteColumn N S s).adjoint.comp (finiteColumn N S s)=compression N S s := by
  classical
  rw [finiteColumn,adjoint_column_comp]
  simp only [component_square]
  ext x
  simp [compression,finiteProjection,ContinuousLinearMap.comp_apply]
  exact Finset.sum_attach s (fun v => (inlL (H:=H) (G:=G)).adjoint (v.val.final (inlL x)))

include hS

lemma compression_norm_le (s : Finset S) : ‖compression N S s‖≤1 := by
  calc
    _≤‖(inlL (H:=H) (G:=G)).adjoint‖*
        (‖finiteProjection N right left S s‖*‖inlL (H:=H) (G:=G)‖) :=
      (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
    _≤1*(1*1) := mul_le_mul (by simpa only [ContinuousLinearMap.adjoint.norm_map] using inl_norm_le (H:=H) (G:=G))
      (mul_le_mul (finiteProjection_norm_le N right left S hS s) (inl_norm_le (H:=H) (G:=G))
        (norm_nonneg (inlL (H:=H) (G:=G))) (by norm_num))
      (mul_nonneg (norm_nonneg (finiteProjection N right left S s)) (norm_nonneg (inlL (H:=H) (G:=G)))) (by norm_num)
    _=1 := by norm_num

lemma column_norm_le (s : Finset S) : ‖finiteColumn N S s‖≤1 := by
  have h := compression_norm_le N S hS s
  rw [←column_square N S s,ContinuousLinearMap.norm_adjoint_comp_self] at h
  nlinarith [norm_nonneg (finiteColumn N S s)]

lemma compression_tendsto (hspan : (familySpace N right left S).starProjection=left) (x : H) :
    Tendsto (fun s : Finset S => compression N S s x) atTop (𝓝 x) := by
  have h := (inlL (H:=H) (G:=G)).adjoint.continuous.tendsto
    (left (inlL (H:=H) (G:=G) x))
  have ht := h.comp (finiteProjection_tendsto N right left S hS left_projection hspan (inlL x))
  have he : (inlL (H:=H) (G:=G)).adjoint (left (inlL x))=x := by
    rw [adjoint_inlL]
    rfl
  rw [he] at ht
  exact ht

omit hS

lemma component_intertwines {A : Type*} [CStarAlgebra A]
    (φ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ψ : A →⋆ₐ[ℂ] (G →L[ℂ] G))
    (v : Intertwiner N) (a : A)
    (hv : block (φ a) (ψ a)*star v.val=star v.val*block (φ a) (ψ a)) :
    (component N v).comp (φ a)=(ψ a).comp (component N v) := by
  ext x
  have h := congrArg (fun T : Space H G →L[ℂ] Space H G => (T (inlL x)).ofLp.2) hv
  simpa only [component,ContinuousLinearMap.comp_apply,adjoint_inrL,WithLp.sndL_apply,
    mul_apply_eq_comp,ContinuousLinearMap.star_eq_adjoint,block_apply,
    inlL_apply,WithLp.ofLp_toLp,WithLp.snd,map_zero] using h.symm

end Kadison.BiprodLinkColumn

end

end
end

end OAI
