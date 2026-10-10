import OAI.NumberTheory.DirichletL.Moments.CommonPairedSource

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentCommonExceptionalCost
open HeckeFamily CenteredMomentCommonLinearNormalization CenteredMomentCommonRadialData
open CenteredMomentCommonAllocationSum CenteredMomentSourceLiveColumn CenteredMomentCommonRawScale
open CenteredMomentCommonRawCost CenteredMomentExceptionalAmplitudePair
open CenteredMomentAllocatedDetectorAmplitude CenteredMomentAllocationCost CenteredMomentCommonProfile
local notation "O" => HeckeFamily.O
variable {ι:Type*} [Fintype ι] [DecidableEq ι]

def frozenProfile (s:Input ι):ℝ:=(∏i,s.M i)*(max 1 s.upper)^Fintype.card ι

omit [DecidableEq ι] in
lemma frozenProfile_nonneg (s:Input ι):0≤frozenProfile s:=by
  unfold frozenProfile
  exact mul_nonneg (Finset.prod_nonneg (fun i _=>zero_le_one.trans (s.M_ge_one i)))
    (pow_nonneg (zero_le_one.trans (le_max_left _ _)) _)

omit [DecidableEq ι] in
theorem scalar_volume_exact (s:Input ι)(C R:Ideal O)(B:actualAllocations s.pools C):
    ‖commonScalar s C R B‖*Real.sqrt (volume (commonData s C R B))=
      ‖frozenCoefficient B.val C R s.ν s.W s.P‖*Real.sqrt (volume s.toData)/rawReduction B.val s.P:=by
  have hv:=volume_pos (commonData s C R B)
  have hr:=rawReduction_pos B.val (alloc_ne s C B) s.P s.P_pos
  have he:volume (commonData s C R B)*rawReduction B.val s.P=volume s.toData:=by
    rw [common_volume]
    exact raw_scale_identity B.val (alloc_ne s C B) (s.X₁*s.X₂) s.P
  have hs:Real.sqrt (volume s.toData)=Real.sqrt (volume (commonData s C R B))*
      Real.sqrt (rawReduction B.val s.P):=by rw [←he,Real.sqrt_mul hv.le]
  rw [commonScalar,norm_mul,norm_inv,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _),hs]
  have hsq:=Real.sq_sqrt hr.le
  have hn:Real.sqrt (rawReduction B.val s.P)≠0:=(Real.sqrt_pos.mpr hr).ne'
  field_simp
  rw [hsq]
  ring

omit [DecidableEq ι] in
theorem scalar_volume_bound (s:Input ι)(C R:Ideal O)(hC:C≠0)(B:actualAllocations s.pools C):
    ‖commonScalar s C R B‖*Real.sqrt (volume (commonData s C R B))≤
      frozenProfile s*Real.sqrt (volume s.toData)/(Ideal.absNorm C:ℝ):=by
  rw [scalar_volume_exact]
  have hr:=rawReduction_pos B.val (alloc_ne s C B) s.P s.P_pos
  have hN:(0:ℝ)<Ideal.absNorm C:=by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hC)
  by_cases hz:frozenCoefficient B.val C R s.ν s.W s.P=0
  · rw [hz,norm_zero,zero_mul,zero_div]
    exact div_nonneg (mul_nonneg (frozenProfile_nonneg s) (Real.sqrt_nonneg _)) hN.le
  · have hn:=(actual_reduction_norm B.val (alloc_ne s C B) C R
      (Finset.mem_filter.mp B.property).2 s.ν s.W s.P s.P_pos s.lower s.upper
      s.lower_pos s.slot_support hz).2
    have hc:=frozenCoefficient_norm B.val C R s.ν s.W s.P s.M s.ν_bound s.W_bound s.M_ge_one
    have hi:(1:ℝ)/rawReduction B.val s.P≤(max 1 s.upper)^Fintype.card ι/(Ideal.absNorm C:ℝ):=
      (div_le_div_iff₀ hr hN).mpr (by simpa using hn)
    calc
      _≤((∏i,s.M i)*Real.sqrt (volume s.toData))/rawReduction B.val s.P:=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hc (Real.sqrt_nonneg _)) hr.le
      _=((∏i,s.M i)*Real.sqrt (volume s.toData))*(1/rawReduction B.val s.P):=by ring
      _≤((∏i,s.M i)*Real.sqrt (volume s.toData))*
          ((max 1 s.upper)^Fintype.card ι/(Ideal.absNorm C:ℝ)):=
        mul_le_mul_of_nonneg_left hi (mul_nonneg
          (Finset.prod_nonneg (fun i _=>zero_le_one.trans (s.M_ge_one i))) (Real.sqrt_nonneg _))
      _=_:=by unfold frozenProfile;ring

omit [DecidableEq ι] in
theorem common_slotControl (s:Input ι)(C R:Ideal O)(B:actualAllocations s.pools C):
    slotControl (commonData s C R B)≤slotControl s.toData:=by
  unfold slotControl
  change (∏i:liveIndices B.val,s.M i.val)*
    (∏i:liveIndices B.val,max 1 (128*max 0 (s.hi i.val)*s.M i.val))≤_
  rw [Finset.prod_coe_sort (liveIndices B.val) s.M,
    Finset.prod_coe_sort (liveIndices B.val) (fun i:ι=>max 1 (128*max 0 (s.hi i)*s.M i))]
  apply mul_le_mul
  · exact Finset.prod_le_prod_of_subset_of_one_le₀ (Finset.subset_univ _)
      (fun i _=>zero_le_one.trans (s.M_ge_one i)) (fun i _ _=>s.M_ge_one i)
  · exact Finset.prod_le_prod_of_subset_of_one_le₀ (Finset.subset_univ _)
      (fun i _=>zero_le_one.trans (le_max_left _ _)) (fun i _ _=>le_max_left _ _)
  · exact Finset.prod_nonneg (fun i _=>zero_le_one.trans (le_max_left _ _))
  · exact Finset.prod_nonneg (fun i _=>zero_le_one.trans (s.M_ge_one i))

end SevenEighths.CenteredMomentCommonExceptionalCost

end

end OAI
