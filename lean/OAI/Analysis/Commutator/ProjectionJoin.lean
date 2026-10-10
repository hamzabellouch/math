import Mathlib
import OAI.Analysis.Commutator.DiffuseProjection
import OAI.Analysis.Commutator.FactorCorner
import OAI.Analysis.Commutator.DyadicDimensionAdd
import OAI.Analysis.Commutator.DyadicDimensionComparison

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder InnerProductSpace

namespace Kadison.ProjectionJoin

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def remainder (p q : H →L[ℂ] H) : H →L[ℂ] H := Polar.leftSupport ((1-p)*q)

def join (p q : H →L[ℂ] H) : H →L[ℂ] H := p+remainder p q

lemma remainder_projection (p q : H →L[ℂ] H) : IsStarProjection (remainder p q) :=
  Polar.isProjection_leftSupport _

lemma remainder_le {p : H →L[ℂ] H} (hp : IsStarProjection p) (q : H →L[ℂ] H) :
    remainder p q≤1-p := by
  apply Polar.leftSupport_le _ _ hp.one_sub
  rw [←mul_assoc,hp.one_sub.isIdempotentElem.eq]

lemma remainder_mul {p : H →L[ℂ] H} (hp : IsStarProjection p) (q : H →L[ℂ] H) :
    remainder p q*p=0 := by
  have h := ((remainder_projection p q).le_iff_mul_eq_left hp.one_sub).mp (remainder_le hp q)
  rw [mul_sub,mul_one] at h
  exact sub_eq_self.mp h

lemma mul_remainder {p : H →L[ℂ] H} (hp : IsStarProjection p) (q : H →L[ℂ] H) :
    p*remainder p q=0 := by
  simpa only [star_mul,hp.isSelfAdjoint.star_eq,(remainder_projection p q).isSelfAdjoint.star_eq,
    star_zero] using congrArg star (remainder_mul hp q)

lemma join_projection {p : H →L[ℂ] H} (hp : IsStarProjection p) (q : H →L[ℂ] H) :
    IsStarProjection (join p q) := by
  refine ⟨?_,hp.isSelfAdjoint.add (remainder_projection p q).isSelfAdjoint⟩
  change (p+remainder p q)*(p+remainder p q)=p+remainder p q
  rw [add_mul,mul_add,mul_add,hp.isIdempotentElem.eq,(remainder_projection p q).isIdempotentElem.eq,
    mul_remainder hp q,remainder_mul hp q,add_zero,zero_add]

lemma left_le {p : H →L[ℂ] H} (hp : IsStarProjection p) (q : H →L[ℂ] H) : p≤join p q := by
  apply (hp.le_iff_mul_eq_left (join_projection hp q)).mpr
  change p*(p+remainder p q)=p
  rw [mul_add,hp.isIdempotentElem.eq,mul_remainder hp q,add_zero]

lemma right_le {p q : H →L[ℂ] H} (hp : IsStarProjection p) (hq : IsStarProjection q) : q≤join p q := by
  apply (hq.le_iff_mul_eq_right (join_projection hp q)).mpr
  have hs : remainder p q*((1-p)*q)=(1-p)*q := Polar.leftSupport_mul _
  have hsp : remainder p q*(1-p)=remainder p q := by
    rw [mul_sub,mul_one,remainder_mul hp q,sub_zero]
  rw [←mul_assoc,hsp] at hs
  change (p+remainder p q)*q=q
  rw [add_mul,hs,sub_mul,one_mul]
  abel

lemma join_le {p q r : H →L[ℂ] H} (hp : IsStarProjection p) (hq : IsStarProjection q)
    (hr : IsStarProjection r) (hpr : p≤r) (hqr : q≤r) : join p q≤r := by
  have hrp := (hp.le_iff_mul_eq_right hr).mp hpr
  have hrq := (hq.le_iff_mul_eq_right hr).mp hqr
  have hs : remainder p q≤r := by
    apply Polar.leftSupport_le _ _ hr
    rw [←mul_assoc,mul_sub,mul_one,hrp,sub_mul,hrq,sub_mul,one_mul]
  apply ((join_projection hp q).le_iff_mul_eq_right hr).mpr
  change r*(p+remainder p q)=p+remainder p q
  rw [mul_add,hrp,((remainder_projection p q).le_iff_mul_eq_right hr).mp hs]

lemma remainder_mem (M : VonNeumannAlgebra H) {p q : H →L[ℂ] H} (hp : p∈M) (hq : q∈M) :
    remainder p q∈M := Polar.leftSupport_mem M (M.mul_mem (M.sub_mem M.one_mem hp) hq)

lemma join_mem (M : VonNeumannAlgebra H) {p q : H →L[ℂ] H} (hp : p∈M) (hq : q∈M) :
    join p q∈M := M.add_mem hp (remainder_mem M hp hq)

open PartialIsometryOrder PartialIsometryOrder.DyadicPartition

variable [Nontrivial H] (M : VonNeumannAlgebra H) (hfac : FactorCorner.IsFactor M)
  (hd : DiffuseProjection.HasNoMinimalProjections M) (hfin : IsFiniteAlgebra M)

include hfin in
theorem dimension_join_le {p q : H →L[ℂ] H} (hpM : p∈M) (hqM : q∈M)
    (hp : IsStarProjection p) (hq : IsStarProjection q) :
    dimension M hfac hd (join p q)≤dimension M hfac hd p+dimension M hfac hd q := by
  let T := (1-p)*q
  have hTM : T∈M := M.mul_mem (M.sub_mem M.one_mem hpM) hqM
  have heq : Equivalent M (Polar.rightSupport T) (Polar.leftSupport T) := by
    let v := Polar.partialIsometry T
    refine ⟨⟨v,Polar.partialIsometry_mem_vonNeumann M hTM,Polar.partialIsometry_triple T,?_,le_rfl⟩,?_,rfl⟩
    · rw [Polar.rightSupport,Polar.partialIsometry_initial]
    · exact Polar.partialIsometry_initial T
  have hdim := dimension_congr_equivalent M hfac hd (Polar.isProjection_rightSupport T)
    (Polar.isProjection_leftSupport T) heq
  have hle : Polar.rightSupport T≤q := by
    apply Polar.rightSupport_le T q hq
    dsimp [T]
    rw [mul_assoc,hq.isIdempotentElem.eq]
  have hdle := dimension_mono M hfac hd (Polar.rightSupport_mem M hTM)
    (Polar.isProjection_rightSupport T) hle
  rw [join,dimension_orthogonal_add M hfac hd hfin hpM (remainder_mem M hpM hqM)
    hp (remainder_projection p q) (mul_remainder hp q)]
  apply add_le_add le_rfl
  change dimension M hfac hd (Polar.leftSupport T)≤_
  rw [←hdim]
  exact hdle

end Kadison.ProjectionJoin

end

end
end

end OAI
