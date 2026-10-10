import Mathlib
import OAI.Combinatorics.Chromatic.GradedAlgebra.GradedFormalLog
import OAI.Combinatorics.Chromatic.Walls.HNTorusFactor
import OAI.Combinatorics.Chromatic.QuantumTorus.TorusProjection
import OAI.Combinatorics.Chromatic.GradedAlgebra.MutationCoordinates

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries WallUnits
noncomputable section
variable {M I : Type*} [AddCommGroup M] [Fintype I] [DecidableEq I]
variable (Ω : M →+ M →+ ℤ) (C : (I → ℤ) →+ M)
variable (coord : M →+ (I → ℤ)) (hcoord : ∀d,coord (C d)=d) (pc : I)
local instance pureFaceProjectionAddCommGroup : AddCommGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommGroup
local instance pureFaceProjectionAddCommMonoid : AddCommMonoid (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid
local instance pureFaceProjectionAddGroup : AddGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddGroup
local instance pureFaceProjectionSub : Sub (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toSub

def pureFaceCovector : M →+ ℝ := -(Int.castAddHom ℝ).comp (nonpDegree coord pc)
lemma pureFaceCovector_apply (m : M) : pureFaceCovector coord pc m= -(nonpDegree coord pc m : ℝ) := rfl
lemma pureFaceCovector_zero_iff (m : M) : pureFaceCovector coord pc m=0 ↔ nonpDegree coord pc m=0 := by
  rw [pureFaceCovector_apply,neg_eq_zero,Int.cast_eq_zero]

def pureFaceSeries (F : PowerSeries (Torus LaurentRay.vUnit Ω)) : PowerSeries (Torus LaurentRay.vUnit Ω) :=
  PowerSeries.mk (fun n=>zeroProject LaurentRay.vUnit Ω (pureFaceCovector coord pc) (coeff n F))
lemma coeff_pureFaceSeries (F : PowerSeries (Torus LaurentRay.vUnit Ω)) (n : ℕ) :
    coeff n (pureFaceSeries Ω coord pc F)=zeroProject LaurentRay.vUnit Ω (pureFaceCovector coord pc) (coeff n F) := coeff_mk _ _
lemma pureFaceSeries_apply (F : PowerSeries (Torus LaurentRay.vUnit Ω)) (n : ℕ) (m : M) :
    coeff n (pureFaceSeries Ω coord pc F) m=if nonpDegree coord pc m=0 then coeff n F m else 0 := by
  rw [coeff_pureFaceSeries]
  change (coeff n F).filter (fun m=>pureFaceCovector coord pc m=0) m=_
  simp only [Finsupp.filter_apply,pureFaceCovector_zero_iff]
lemma pureFaceSeries_one : pureFaceSeries Ω coord pc 1=1 := by
  apply PowerSeries.ext
  intro n
  rw [coeff_pureFaceSeries,coeff_one]
  split_ifs with hn
  · exact zeroProject_one _ _ _
  · exact map_zero _
lemma pureFaceSeries_sub (F G : PowerSeries (Torus LaurentRay.vUnit Ω)) :
    pureFaceSeries Ω coord pc (F-G)=pureFaceSeries Ω coord pc F-pureFaceSeries Ω coord pc G := by
  apply PowerSeries.ext
  intro n
  simp only [coeff_pureFaceSeries,map_sub]
include hcoord in
lemma rootGrade_nonpositive_face (n : ℕ) (x : Torus LaurentRay.vUnit Ω)
    (hx : x∈rootGrade LaurentRay.vUnit Ω C n) :
    x∈supportedSubring LaurentRay.vUnit Ω (nonpositiveCone (pureFaceCovector coord pc)) := by
  intro m hm
  by_contra hh
  have hroot : HasRootDegree C n m:=by by_contra hk; exact hh (hx m hk)
  have hpos:=nonpDegree_root_nonneg C coord hcoord pc hroot
  exact hm (show pureFaceCovector coord pc m≤0 by rw [pureFaceCovector_apply]; exact neg_nonpos.mpr (by exact_mod_cast hpos))
include hcoord in
lemma pureFaceSeries_mul (F G : PowerSeries (Torus LaurentRay.vUnit Ω))
    (hF : ∀n,coeff n F∈rootGrade LaurentRay.vUnit Ω C n)
    (hG : ∀n,coeff n G∈rootGrade LaurentRay.vUnit Ω C n) :
    pureFaceSeries Ω coord pc (F*G)=pureFaceSeries Ω coord pc F*pureFaceSeries Ω coord pc G := by
  apply PowerSeries.ext
  intro n
  rw [coeff_pureFaceSeries,coeff_mul,coeff_mul,map_sum]
  apply Finset.sum_congr rfl
  intro p hp
  rw [coeff_pureFaceSeries,coeff_pureFaceSeries]
  exact zeroProject_mul_nonpositive _ _ _ _ _
    (rootGrade_nonpositive_face Ω C coord hcoord pc _ _ (hF _))
    (rootGrade_nonpositive_face Ω C coord hcoord pc _ _ (hG _))
lemma pureFaceSeries_graded (F : PowerSeries (Torus LaurentRay.vUnit Ω))
    (hF : ∀n,coeff n F∈rootGrade LaurentRay.vUnit Ω C n) :
    ∀n,coeff n (pureFaceSeries Ω coord pc F)∈rootGrade LaurentRay.vUnit Ω C n := by
  intro n m hm
  rw [pureFaceSeries_apply]
  split_ifs <;> simp only [hF n m hm]
def pureFace (F : CompletedPositive LaurentRay.vUnit Ω C) : CompletedPositive LaurentRay.vUnit Ω C :=
  ⟨pureFaceSeries Ω coord pc F.val,by
    constructor
    · rw [←coeff_zero_eq_constantCoeff_apply,coeff_pureFaceSeries,coeff_zero_eq_constantCoeff_apply,F.property.1]
      exact zeroProject_one _ _ _
    · exact pureFaceSeries_graded Ω C coord pc F.val F.property.2⟩
include hcoord in
lemma pureFaceSeries_chart_sides (h : M →+ ℝ) (hp : h (simpleRoot C pc)=0)
    (F : CompletedPositive LaurentRay.vUnit Ω C) :
    (pureFace Ω C coord pc (chartPositive LaurentRay.vUnit Ω C h F)).val=1 ∧
    (pureFace Ω C coord pc (chartNegative LaurentRay.vUnit Ω C h F)).val=1 := by
  have HS:=chart_three_support LaurentRay.vUnit Ω C h F
  constructor
  all_goals
    apply PowerSeries.ext
    intro n
    cases n with
    | zero => simpa only [coeff_zero_eq_constantCoeff_apply,map_one] using (pureFace _ _ _ _ _).property.1
    | succ n =>
      rw [coeff_one,ite_eq_right (by omega)]
      apply Finsupp.ext
      intro m
      change coeff (n+1) (pureFaceSeries Ω coord pc _) m=0
      rw [pureFaceSeries_apply]
      split_ifs with hz
      · by_contra hh
        have hm : HasRootDegree C (n+1) m:=by
          by_contra hn
          first | exact hh ((chartPositive _ _ _ _ F).property.2 _ m hn) | exact hh ((chartNegative _ _ _ _ F).property.2 _ m hn)
        have hm0 : h m=0:=by rw [nonp_zero_root C coord hcoord pc hm hz,map_nsmul,hp,nsmul_zero]
        first
        | have he:=HS.1 n m hh; rw [hm0] at he; exact lt_irrefl _ he
        | have he:=HS.2.2 n m hh; rw [hm0] at he; exact lt_irrefl _ he
      · rfl
include hcoord in
lemma pureFace_chartZero (h : M →+ ℝ) (hp : h (simpleRoot C pc)=0)
    (F : CompletedPositive LaurentRay.vUnit Ω C) :
    pureFace Ω C coord pc (chartZero LaurentRay.vUnit Ω C h F)=pureFace Ω C coord pc F := by
  apply Subtype.ext
  have H:=congrArg (pureFaceSeries Ω coord pc) (chart_three_factorization LaurentRay.vUnit Ω C h F)
  rw [pureFaceSeries_mul Ω C coord hcoord pc _ _
    (FormalLog.graded_multiply _ (rootGrade_mul LaurentRay.vUnit Ω C) _ _
      (chartPositive _ _ _ _ F).property.2 (chartZero _ _ _ _ F).property.2)
    (chartNegative _ _ _ _ F).property.2,
    pureFaceSeries_mul Ω C coord hcoord pc _ _
      (chartPositive _ _ _ _ F).property.2 (chartZero _ _ _ _ F).property.2] at H
  have HH:=pureFaceSeries_chart_sides Ω C coord hcoord pc h hp F
  change (pureFace _ _ _ _ (chartPositive _ _ _ _ F)).val*
    (pureFace _ _ _ _ (chartZero _ _ _ _ F)).val*
    (pureFace _ _ _ _ (chartNegative _ _ _ _ F)).val=(pureFace _ _ _ _ F).val at H
  simpa only [HH.1,HH.2,one_mul,mul_one] using H
end
end ElementaryPositivity.QuantumTorus

end

end OAI
