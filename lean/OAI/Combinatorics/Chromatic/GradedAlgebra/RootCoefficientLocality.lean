import Mathlib
import OAI.Combinatorics.Chromatic.GradedAlgebra.RootSectionHalfspace

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries PowerSeriesAdjoint WallUnits
open scoped BigOperators
open Classical
noncomputable section
variable {M I:Type*} [AddCommGroup M] [Fintype I] [DecidableEq I]
variable (Ω:M →+ M →+ ℤ) (hΩ:∀m,Ω m m=0)
variable (C:(I → ℤ) →+ M) (coord:M →+ (I → ℤ)) (hcoord:∀d,coord (C d)=d)
local instance rootCoefficientLocalityRing : Ring (Torus LaurentRay.vUnit Ω) :=
  Torus.instRing LaurentRay.vUnit Ω
local instance rootCoefficientLocalityAddCommMonoid : AddCommMonoid (Torus LaurentRay.vUnit Ω) :=
  (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid
local instance rootCoefficientLocalityAddGroup : AddGroup (Torus LaurentRay.vUnit Ω) :=
  (Torus.instRing LaurentRay.vUnit Ω).toAddGroup

include hcoord in
lemma root_interval_orthogonal (base m b r s:M) (d:I → ℕ)
    (hm:m=base+C (fun i=>(d i:ℤ)))
    (hb:∃k,HasRootDegree C k (b-base))
    (hr:∃k,HasRootDegree C k r) (hs:∃k,HasRootDegree C k s)
    (he:r+(s+b)=m) (ho:∀i,0<d i → Ω (simpleRoot C i) m=0) : Ω r m=0 := by
  obtain ⟨kb,hb⟩:=hb
  obtain ⟨kr,hr⟩:=hr
  obtain ⟨ks,hs⟩:=hs
  obtain ⟨ab,_,hcb,_⟩:=root_coordinates C coord hcoord hb
  obtain ⟨ar,_,hcr,_⟩:=root_coordinates C coord hcoord hr
  obtain ⟨as',_,hcs,_⟩:=root_coordinates C coord hcoord hs
  have hc:coord r+(coord s+coord (b-base))=(fun i=>(d i:ℤ)) := by
    rw [←map_add,←map_add]
    have he':r+(s+(b-base))=C (fun i=>(d i:ℤ)):=by rw [←add_sub_assoc,←add_sub_assoc,he,hm]; abel
    rw [he',hcoord]
  have hid:∀i,(ar i:ℤ)+(as' i:ℤ)+(ab i:ℤ)=(d i:ℤ):=by
    intro i
    have H:=congrFun hc i
    simp only [Pi.add_apply] at H
    rw [hcb,hcr,hcs] at H
    omega
  rw [root_simple_expansion C coord hcoord hr,map_sum]
  simp only [AddMonoidHom.finsetSum_apply,map_zsmul,AddMonoidHom.zsmul_apply,smul_eq_mul]
  apply Finset.sum_eq_zero
  intro i _
  by_cases hi:0<d i
  · rw [ho i hi,mul_zero]
  · have hai:ar i=0:=by have H:=hid i; omega
    rw [hcr,hai,Int.natCast_zero,zero_mul]

include hΩ hcoord in
lemma actualMonomialAdjoint_locality (f:CompletedPositive LaurentRay.vUnit Ω C)
    (base m b:M) (d:I → ℕ) (hm:m=base+C (fun i=>(d i:ℤ)))
    (hb:∃k,HasRootDegree C k (b-base))
    (ho:∀i,0<d i → Ω (simpleRoot C i) m=0) :
    actualMonomialAdjointCoefficient Ω (rootOrder coord) f.val b m=
      actualMonomialAdjointCoefficient Ω (rootOrder coord) 1 b m := by
  have H:∀N,coeff N (adjoint f.val (PowerSeries.C (Torus.X LaurentRay.vUnit Ω b))) m=
      coeff N (PowerSeries.C (Torus.X LaurentRay.vUnit Ω b)) m := by
    intro N
    apply adjoint_target_cyclic LaurentRay.vUnit Ω hΩ f.val b m N f.property.1
    intro i j hij r hr s hs he
    apply root_interval_orthogonal Ω C coord hcoord base m b r s d hm hb
      ⟨i,chart_root_of_ne LaurentRay.vUnit Ω C f i r (Finsupp.mem_support_iff.mp hr)⟩
      ⟨j,?_⟩ he ho
    by_contra hh
    exact (Finsupp.mem_support_iff.mp hs) (SeriesGraded.inverse LaurentRay.vUnit Ω C f.property.2 j s hh)
  unfold actualMonomialAdjointCoefficient actualRootCoefficient
  split_ifs
  · have H1:=adjoint_monomial_coeff LaurentRay.vUnit Ω hΩ f.val b (m-b)
      ((rootOrder coord (m-b)).toNat)
    have H2:=adjoint_monomial_coeff LaurentRay.vUnit Ω hΩ 1 b (m-b)
      ((rootOrder coord (m-b)).toNat)
    rw [sub_add_cancel] at H1 H2
    rw [←H1,←H2,H]
    have hI:invOfUnit (1:PowerSeries (Torus LaurentRay.vUnit Ω)) 1=1 := by
      simpa only [mul_one] using (invOfUnit_mul (1:PowerSeries (Torus LaurentRay.vUnit Ω)) 1 (by simp))
    simp only [adjoint,hI,one_mul,mul_one]
  · rfl

include hΩ hcoord in
lemma actualPolynomialAdjoint_locality (f:CompletedPositive LaurentRay.vUnit Ω C)
    (base m:M) (d:I → ℕ) (hm:m=base+C (fun i=>(d i:ℤ)))
    (F:Torus LaurentRay.vUnit Ω)
    (hF:∀b∈F.support,∃k,HasRootDegree C k (b-base))
    (ho:∀i,0<d i → Ω (simpleRoot C i) m=0) :
    actualPolynomialAdjointCoefficient Ω (rootOrder coord) f.val F m=F m := by
  rw [←actualPolynomialAdjointCoefficient_one Ω hΩ (rootOrder coord) F m]
  unfold actualPolynomialAdjointCoefficient Finsupp.sum
  apply Finset.sum_congr rfl
  intro b hb
  change F b*actualMonomialAdjointCoefficient Ω (rootOrder coord) f.val b m=
    F b*actualMonomialAdjointCoefficient Ω (rootOrder coord) 1 b m
  exact congrArg (fun x=>F b*x) (actualMonomialAdjoint_locality Ω hΩ C coord hcoord f base m b d hm (hF b hb) ho)
end
end ElementaryPositivity.QuantumTorus

end

end OAI
