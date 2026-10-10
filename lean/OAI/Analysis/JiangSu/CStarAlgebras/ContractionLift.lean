import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.CentralSequences.OrderZeroContractiveCut

namespace OAI

section

noncomputable section
namespace CStarLift
open CompletelyPositiveOperations
open scoped ComplexOrder

variable {E D : Type*} [CStarAlgebra E] [CStarAlgebra D]
  [PartialOrder E] [StarOrderedRing E] [PartialOrder D] [StarOrderedRing D]

theorem exists_contraction (q : E →⋆ₐ[ℂ] D) (hq : Function.Surjective q)
    {b : D} (hb : ‖b‖≤1) : ∃ x : E,q x=b ∧ ‖x‖≤1 := by
  rcases subsingleton_or_nontrivial D with hD | hD
  · have := hD
    exact ⟨0,Subsingleton.elim _ _,by simp⟩
  have := hD
  obtain ⟨z,hz⟩ := hq b
  let H := star z*z
  have hHp : 0≤H := star_mul_self_nonneg z
  have hHs : IsSelfAdjoint H := hHp.isSelfAdjoint
  let r := cfc cutoffMultiplier H
  have hrp : 0≤r := cfc_nonneg (fun t _ => cutoffMultiplier_nonneg t)
  have hrc : Commute r H := by
    exact (Commute.refl H).cfc (by simpa only [hHs.star_eq] using Commute.refl H) cutoffMultiplier
  have hqH : q H=star b*b := by simp only [H,map_mul,map_star,hz]
  have hqr : q r=1 := by
    change q (cfc cutoffMultiplier H)=1
    rw [q.map_cfc cutoffMultiplier H cutoffMultiplier_continuous.continuousOn,hqH]
    rw [←cfc_one ℝ (star b*b)]
    apply cfc_congr
    intro t ht
    have ht1 : t≤1 := ((le_abs_self t).trans (spectrum.norm_le_norm_of_mem ht)).trans (by
      rw [CStarRing.norm_star_mul_self]
      nlinarith [norm_nonneg b])
    simp only [cutoffMultiplier,max_eq_left ht1,inv_one,Pi.one_apply]
  let s := CFC.sqrt r
  have hsc : Commute s H := hrc.cfcₙ_nnreal NNReal.sqrt
  have hsq : s*s=r := CFC.sqrt_mul_sqrt_self r hrp
  have hqs : q s=1 := by
    change q (CFC.sqrt r)=1
    change q.toNonUnitalStarAlgHom (cfcₙ NNReal.sqrt r)=1
    rw [q.toNonUnitalStarAlgHom.map_cfcₙ NNReal.sqrt r (by fun_prop) NNReal.sqrt_zero (by fun_prop) hrp (map_nonneg q hrp)]
    change CFC.sqrt (q r)=1
    rw [hqr,CFC.sqrt_one]
  have hprod : 0≤r*H := by
    change 0≤cfc cutoffMultiplier H*H
    nth_rw 2 [←cfc_id' ℝ H]
    rw [←cfc_mul cutoffMultiplier (fun t : ℝ => t) H cutoffMultiplier_continuous.continuousOn]
    apply cfc_nonneg
    intro t ht
    exact mul_nonneg (cutoffMultiplier_nonneg t) (spectrum_nonneg_of_nonneg hHp ht)
  have hprod1 : r*H≤1 := by
    change cfc cutoffMultiplier H*H≤1
    nth_rw 2 [←cfc_id' ℝ H]
    rw [←cfc_mul cutoffMultiplier (fun t : ℝ => t) H cutoffMultiplier_continuous.continuousOn]
    apply (cfc_le_one_iff _ H (cutoffMultiplier_continuous.mul continuous_id).continuousOn hHs).mpr
    intro t _
    exact cutoffMultiplier_mul_le_one t
  have hn : ‖r*H‖≤1 := (CStarAlgebra.norm_le_one_iff_of_nonneg _ hprod).mpr hprod1
  refine ⟨z*s,by rw [map_mul,hz,hqs,mul_one],?_⟩
  have hcalc : star (z*s)*(z*s)=r*H := by
    rw [star_mul,(CFC.sqrt_nonneg r).isSelfAdjoint.star_eq]
    change (s*star z)*(z*s)=r*H
    rw [mul_assoc s,←mul_assoc (star z)]
    change s*(H*s)=r*H
    rw [←hsc.eq,←mul_assoc,hsq]
  have hsqu : ‖z*s‖*‖z*s‖≤1 := by
    rw [←CStarRing.norm_star_mul_self,hcalc]
    exact hn
  nlinarith [norm_nonneg (z*s)]

end CStarLift

end
end

end OAI
