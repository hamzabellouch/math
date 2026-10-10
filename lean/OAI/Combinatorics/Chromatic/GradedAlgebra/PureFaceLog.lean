import Mathlib
import OAI.Combinatorics.Chromatic.Walls.SimpleIncomingData
import OAI.Combinatorics.Chromatic.QuantumTorus.PureFaceProjection

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries WallUnits
noncomputable section
variable {M I : Type*} [AddCommGroup M] [Fintype I] [DecidableEq I]
variable (Ω : M →+ M →+ ℤ) (C : (I → ℤ) →+ M)
variable (coord : M →+ (I → ℤ)) (hcoord : ∀d,coord (C d)=d) (pc : I)
local instance pureFaceLogAddCommGroup : AddCommGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommGroup
local instance pureFaceLogAddCommMonoid : AddCommMonoid (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid
local instance pureFaceLogAddGroup : AddGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddGroup
local instance pureFaceLogSub : Sub (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toSub
omit [DecidableEq I] in
lemma graded_series_pow (F : PowerSeries (Torus LaurentRay.vUnit Ω))
    (hF : ∀n,coeff n F∈rootGrade LaurentRay.vUnit Ω C n) (k : ℕ) :
    ∀n,coeff n (F^k)∈rootGrade LaurentRay.vUnit Ω C n := by
  induction k with
  | zero=>simpa only [pow_zero] using FormalLog.graded_one _ (rootGrade_one LaurentRay.vUnit Ω C)
  | succ k ih=>simpa only [pow_succ] using FormalLog.graded_multiply _ (rootGrade_mul LaurentRay.vUnit Ω C) _ _ ih hF
include hcoord in
lemma pureFaceSeries_pow (F : PowerSeries (Torus LaurentRay.vUnit Ω))
    (hF : ∀n,coeff n F∈rootGrade LaurentRay.vUnit Ω C n) (k : ℕ) :
    pureFaceSeries Ω coord pc (F^k)=(pureFaceSeries Ω coord pc F)^k := by
  induction k with
  | zero=>simpa only [pow_zero] using pureFaceSeries_one Ω coord pc
  | succ k ih=>rw [pow_succ,pureFaceSeries_mul Ω C coord hcoord pc _ _
      (graded_series_pow Ω C F hF k) hF,ih,pow_succ]
lemma zeroProject_rat_smul (h : M →+ ℝ) (a : ℚ) (x : Torus LaurentRay.vUnit Ω) :
    zeroProject LaurentRay.vUnit Ω h (a • x)=a • zeroProject LaurentRay.vUnit Ω h x := by
  classical
  exact map_rat_smul (zeroProject LaurentRay.vUnit Ω h) a x
include hcoord in
lemma pureFaceSeries_log (F : CompletedPositive LaurentRay.vUnit Ω C) :
    pureFaceSeries Ω coord pc (FormalLog.log F.val)=FormalLog.log (pureFace Ω C coord pc F).val := by
  have hu : ∀n,coeff n (F.val-1)∈rootGrade LaurentRay.vUnit Ω C n:=by
    intro n
    rw [map_sub]
    exact (rootGrade LaurentRay.vUnit Ω C n).sub_mem (F.property.2 n)
      (FormalLog.graded_one _ (rootGrade_one LaurentRay.vUnit Ω C) n)
  apply PowerSeries.ext
  intro n
  rw [coeff_pureFaceSeries]
  simp only [FormalLog.log,coeff_mk,map_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [zeroProject_rat_smul,←coeff_pureFaceSeries,pureFaceSeries_pow Ω C coord hcoord pc _ hu,
    pureFaceSeries_sub,pureFaceSeries_one]
  rfl
include hcoord in
lemma pureFace_log_chart_apply (h : M →+ ℝ) (hp : h (simpleRoot C pc)=0)
    (F : CompletedPositive LaurentRay.vUnit Ω C) (n : ℕ) (m : M)
    (hm : nonpDegree coord pc m=0) :
    coeff n (FormalLog.log (chartZero LaurentRay.vUnit Ω C h F).val) m=
      coeff n (FormalLog.log F.val) m := by
  have H:=congrArg (fun D : CompletedPositive LaurentRay.vUnit Ω C=>coeff n (FormalLog.log D.val) m)
    (pureFace_chartZero Ω C coord hcoord pc h hp F)
  rw [←pureFaceSeries_log Ω C coord hcoord pc,←pureFaceSeries_log Ω C coord hcoord pc] at H
  simpa only [pureFaceSeries_apply,hm,ite_true] using H
include hcoord in
lemma pureFace_simpleTransport (hΩ : ∀m,Ω m m=0) :
    pureFace Ω C coord pc (simpleTotalTransport Ω C)=
      literalIncomingCompleted Ω C (simpleIncomingList C) (simpleIncomingList_allowed C) (simpleRoot C pc) := by
  let F:=simpleTotalTransport Ω C
  let D:=literalIncomingCompleted Ω C (simpleIncomingList C) (simpleIncomingList_allowed C) (simpleRoot C pc)
  apply Subtype.ext
  apply PowerSeries.ext
  intro N
  apply FormalLog.log_injective_through (pureFace Ω C coord pc F).val D.val N
    (pureFace Ω C coord pc F).property.1 D.property.1
  intro n hn
  apply Finsupp.ext
  intro m
  rw [←pureFaceSeries_log Ω C coord hcoord pc,pureFaceSeries_apply]
  have hdlog : ∀j m,coeff j (FormalLog.log D.val) m≠0→OnPositiveRay (simpleRoot C pc) m:=by
    intro j m hm
    by_contra hh
    exact hm (strict_log_support LaurentRay.vUnit Ω (fun a b ha hb=>ha.add hb) D.val D.property.1
      (literalRootProducts_strictSupport Ω C (OnPositiveRay (simpleRoot C pc))
        (fun a b ha hb=>ha.add hb)
        (literalIncomingRay_mem Ω C (simpleIncomingList C) (simpleIncomingList_allowed C) (simpleRoot C pc))) j m hh)
  by_cases hz : nonpDegree coord pc m=0
  · rw [ite_eq_left hz]
    by_cases hr : HasRootDegree C n m
    · cases n with
      | zero=>simp only [coeff_zero_eq_constantCoeff_apply,FormalLog.log_constant,Finsupp.zero_apply]
      | succ n=>
        have hmray : OnPositiveRay (simpleRoot C pc) m:=by
          refine ⟨1,n+1,by omega,by omega,?_⟩
          rw [one_nsmul,nonp_zero_root C coord hcoord pc hr hz]
        have hp : incomingCovector Ω m (simpleRoot C pc)=0:=by
          change (Ω (simpleRoot C pc) m : ℝ)=0
          rw [nonp_zero_root C coord hcoord pc hr hz,map_nsmul,hΩ,nsmul_zero,Int.cast_zero]
        rw [←pureFace_log_chart_apply Ω C coord hcoord pc (incomingCovector Ω m) hp F _ m hz]
        exact literalTotalTransport_ray_prescription Ω C hΩ _ (simpleIncomingList_allowed C) _ _ _ hmray
    · rw [root_graded_log LaurentRay.vUnit Ω C F n m hr,root_graded_log LaurentRay.vUnit Ω C D n m hr]
  · rw [ite_eq_right hz]
    by_contra hh
    have hmr:=hdlog n m (Ne.symm hh)
    obtain ⟨a,b,ha,hb,he⟩:=hmr
    have HH:=congrArg (nonpDegree coord pc) he
    rw [map_nsmul,map_nsmul,nonpDegree_simple_self C coord hcoord,nsmul_zero,nsmul_eq_mul] at HH
    exact hz ((mul_eq_zero.mp HH).resolve_left (by exact_mod_cast (Nat.ne_of_gt ha)))
  exact Nat.le_refl N
end
end ElementaryPositivity.QuantumTorus

end

end OAI
