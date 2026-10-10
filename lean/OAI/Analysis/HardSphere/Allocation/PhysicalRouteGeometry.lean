import Mathlib
import OAI.Analysis.HardSphere.Geometry.EndpointsExterior
import OAI.Analysis.HardSphere.Allocation.PhysicalVertex

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace HardSphere.Groups
open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital HardSphere.Lattice

def siteIndex {K : ℕ} [NeZero K] (v : DiscreteTorus K) : Fin 3→Fin K :=
  fun j ↦ ⟨(v j).val,ZMod.val_lt _⟩

def indexSite {K : ℕ} (v : Fin 3→Fin K) : DiscreteTorus K :=
  fun j ↦ ((v j).val:ZMod K)

@[simp] lemma indexSite_siteIndex {K : ℕ} [NeZero K] (v : DiscreteTorus K) :
    indexSite (siteIndex v)=v := by
  funext j
  exact ZMod.natCast_zmod_val _

@[simp] lemma siteIndex_indexSite {K : ℕ} [NeZero K] (v : Fin 3→Fin K) :
    siteIndex (indexSite v)=v := by
  funext j
  apply Fin.ext
  change (((v j).val:ZMod K).val)=(v j).val
  rw [ZMod.val_natCast,Nat.mod_eq_of_lt (v j).isLt]

def siteIndexEquiv {K : ℕ} [NeZero K] : DiscreteTorus K ≃ (Fin 3→Fin K) :=
  ⟨siteIndex,indexSite,indexSite_siteIndex,siteIndex_indexSite⟩

lemma intPeriod_project {K : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (z : ℤ) (hz : (z:ZMod K)=0) : ((z:ℝ):AddCircle L.val)=0 := by
  obtain ⟨q,hq⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd z K).mp hz
  apply (AddCircle.coe_eq_zero_iff L.val).mpr
  refine ⟨q,?_⟩
  rw [zsmul_eq_mul,hL]
  norm_cast
  rw [hq,mul_comm]

lemma siteIndex_project_lift {K : ℕ} [NeZero K] {L : Length}
    (hL : L.val=(K:ℝ)) (z : Vertex) :
    projectPoint L (anchorPoint (siteIndex (torusProjection K z)))=
      projectPoint L (fun k ↦ (z k:ℝ)) := by
  ext k
  change ((((z k:ZMod K).val:ℕ):ℝ):AddCircle L.val)=((z k:ℝ):AddCircle L.val)
  apply sub_eq_zero.mp
  rw [←AddCircle.coe_sub]
  have H := intPeriod_project hL (((z k:ZMod K).val:ℤ)-z k) (by
    simp only [Int.cast_sub,Int.cast_natCast,ZMod.natCast_zmod_val,sub_self])
  simpa only [Int.cast_sub,Int.cast_natCast] using H

lemma targetStep_positive (i : Fin 3) :
    targetStep ⟨2*i.val+1,by omega⟩=fun k ↦ if k=i then (1:ℝ) else 0 := by
  funext k
  fin_cases i <;> fin_cases k <;> norm_num [targetStep]

lemma targetStep_negative (i : Fin 3) :
    targetStep ⟨2*i.val+2,by omega⟩=fun k ↦ if k=i then (-1:ℝ) else 0 := by
  funext k
  fin_cases i <;> fin_cases k <;> norm_num [targetStep]

lemma nearest_targetStep {x y : Vertex} (h : nearestStep x y) :
    ∃ j : Fin 7,targetStep j=fun k ↦ ((y k-x k:ℤ):ℝ) := by
  obtain ⟨i,hi,hr⟩ := h
  rcases (abs_eq (by norm_num : (0:ℤ)≤1)).mp hi with hp|hn
  · refine ⟨⟨2*i.val+2,by omega⟩,?_⟩
    rw [targetStep_negative]
    funext k
    by_cases hk : k=i
    · subst k
      simp only
      have H : y i-x i=-1 := by omega
      rw [H]; norm_num
    · simp only [ite_eq_right hk,hr k hk,sub_self,Int.cast_zero]
  · refine ⟨⟨2*i.val+1,by omega⟩,?_⟩
    rw [targetStep_positive]
    funext k
    by_cases hk : k=i
    · subst k
      simp only
      have H : y i-x i=1 := by omega
      rw [H]; norm_num
    · simp only [ite_eq_right hk,hr k hk,sub_self,Int.cast_zero]

theorem adjacent_routeCellPeriod {K : ℕ} [NeZero K] {L : Length}
    (hL : L.val=(K:ℝ)) {w v : DiscreteTorus K} (h : (torusNearestGraph K).Adj w v) :
    ∃ j : Fin 7,projectPoint L (routeCellPeriod (siteIndex v) (siteIndex w) j)=0 := by
  obtain ⟨_,x,y,hx,hy,hn⟩ := h
  obtain ⟨j,hj⟩ := nearest_targetStep hn
  refine ⟨j,?_⟩
  subst w v
  have hx' := siteIndex_project_lift hL x
  have hy' := siteIndex_project_lift hL y
  ext k
  change (((anchorPoint (siteIndex (torusProjection K y)) k-
    (anchorPoint (siteIndex (torusProjection K x)) k+targetStep j k)):ℝ):AddCircle L.val)=0
  rw [AddCircle.coe_sub,AddCircle.coe_add,show targetStep j k=((y k-x k:ℤ):ℝ) from congrFun hj k]
  have HX := congrFun hx' k
  have HY := congrFun hy' k
  change ((anchorPoint (siteIndex (torusProjection K x)) k:ℝ):AddCircle L.val)=((x k:ℝ):AddCircle L.val) at HX
  change ((anchorPoint (siteIndex (torusProjection K y)) k:ℝ):AddCircle L.val)=((y k:ℝ):AddCircle L.val) at HY
  rw [HX,HY,Int.cast_sub,AddCircle.coe_sub]
  abel

lemma self_routeCellPeriod {K : ℕ} {L : Length} (v : Fin 3→Fin K) :
    projectPoint L (routeCellPeriod v v 0)=0 := by
  simp only [routeCellPeriod,targetStep,Fin.val_zero,↓reduceIte,add_zero,sub_self]
  rfl

end HardSphere.Groups
end
end

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace HardSphere.Groups
open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital HardSphere.Lattice

lemma nearest_project_distance {L : Length} {x y : Vertex} (h : nearestStep x y) :
    torusDistance L (projectPoint L (fun k ↦ (x k:ℝ)))
      (projectPoint L (fun k ↦ (y k:ℝ)))≤1 := by
  obtain ⟨j,hj,hh⟩ := h
  have hc (i : Fin 3) : dist (((x i:ℝ):AddCircle L.val)) ((y i:ℝ):AddCircle L.val)≤
      if i=j then (1:ℝ) else 0 := by
    rw [dist_eq_norm,←AddCircle.coe_sub]
    refine (QuotientAddGroup.norm_mk_le_norm (m:=(x i:ℝ)-(y i:ℝ))).trans ?_
    rw [Real.norm_eq_abs]
    by_cases hi : i=j
    · subst i
      simp only
      exact_mod_cast le_of_eq hj
    · simp only [ite_eq_right hi,hh i hi,sub_self,abs_zero,le_refl]
  unfold torusDistance
  apply (Real.sqrt_le_iff).mpr
  refine ⟨by norm_num,?_⟩
  calc
    _ ≤ ∑ i : Fin 3,(if i=j then (1:ℝ) else 0)^2 := Finset.sum_le_sum fun i _ ↦
      (sq_le_sq₀ dist_nonneg (by split_ifs <;> norm_num)).mpr (hc i)
    _ = 1^2 := by simp

lemma adjacent_center_distance {K : ℕ} [NeZero K] {L : Length}
    (hL : L.val=(K:ℝ)) {x y : DiscreteTorus K} (h : (torusNearestGraph K).Adj x y) :
    torusDistance L (gridCenter L (siteIndex x)) (gridCenter L (siteIndex y))≤1 := by
  obtain ⟨_,v,w,hv,hw,hn⟩ := h
  subst x y
  change torusDistance L (projectPoint L (anchorPoint (siteIndex (torusProjection K v))))
    (projectPoint L (anchorPoint (siteIndex (torusProjection K w))))≤1
  rw [siteIndex_project_lift hL,siteIndex_project_lift hL]
  exact nearest_project_distance hn

end HardSphere.Groups
end
end

end OAI
