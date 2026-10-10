import Mathlib
import OAI.Combinatorics.Chromatic.QuantumTorus.PureProductSplit

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries WallUnits
noncomputable section
variable {M I : Type*} [AddCommGroup M] [Fintype I] [DecidableEq I]
variable (Ω : M →+ M →+ ℤ) (C : (I → ℤ) →+ M)
variable (coord : M →+ (I → ℤ)) (hcoord : ∀d,coord (C d)=d) (pc : I)
include hcoord in
lemma ordered_pure_factor_through (hΩ : ∀m,Ω m m=0) (pos : Bool) (l : List M)
    (K : M → CompletedPositive LaurentRay.vUnit Ω C)
    (hl : l.Pairwise (fun a b=>0<Ω a b))
    (hroot : ∀q∈l,∃d,0<d ∧ HasRootDegree C d q)
    (htrend : ∀q∈l,0≤ sideSign pos*Ω (simpleRoot C pc) q)
    (hRay : ∀q∈l,∀j m,coeff (j+1) (K q).val m≠0 → OnPositiveRay q m)
    (F D : CompletedPositive LaurentRay.vUnit Ω C) (N : ℕ)
    (hprod : ∀j≤N,coeff j F.val=coeff j (completedListProduct LaurentRay.vUnit Ω C l K).val)
    (hface : ∀j≤N,coeff j (pureFace Ω C coord pc F).val=coeff j D.val) :
    let A:=completedListProduct LaurentRay.vUnit Ω C
      (l.filter (fun q=>decide (nonpDegree coord pc q≠0))) K
    ∀j≤N,coeff j F.val=coeff j (if pos then D.val*A.val else A.val*D.val) := by
  classical
  let lP:=l.filter (fun q=>decide (nonpDegree coord pc q=0))
  let lA:=l.filter (fun q=>decide (nonpDegree coord pc q≠0))
  let P:=completedListProduct LaurentRay.vUnit Ω C lP K
  let A:=completedListProduct LaurentRay.vUnit Ω C lA K
  let W:=completedListProduct LaurentRay.vUnit Ω C l K
  have hPW : W.val=if pos then P.val*A.val else A.val*P.val:=by
    have H:=congrArg (fun L : List M=>(L.map (fun q=>(K q).val)).prod)
      (ordered_pure_partition Ω C coord hcoord pc hΩ pos l hl hroot htrend)
    cases pos <;> simpa only [W,P,A,lP,lA,completedListProduct,Bool.false_eq_true,ite_false,ite_true,List.map_append,List.prod_append] using H.symm
  have hPA : (pureFace Ω C coord pc A).val=1:=by
    apply pureFace_list_nonpure Ω C coord hcoord pc lA K
    · intro q hq
      have H:=List.mem_filter.mp hq
      have hn : nonpDegree coord pc q≠0:=of_decide_eq_true H.2
      obtain ⟨d,hd,hr⟩:=hroot q H.1
      have hp:=nonpDegree_root_nonneg C coord hcoord pc hr
      omega
    · intro q hq
      exact hRay q (List.mem_filter.mp hq).1
  have hPP : (pureFace Ω C coord pc P).val=P.val:=by
    apply pureFace_list_pure Ω C coord hcoord pc lP K
    · intro q hq; exact of_decide_eq_true (List.mem_filter.mp hq).2
    · intro q hq; exact hRay q (List.mem_filter.mp hq).1
  have hWP : (pureFace Ω C coord pc W).val=P.val:=by
    change pureFaceSeries Ω coord pc W.val=P.val
    rw [hPW]
    cases pos <;> simp only [Bool.false_eq_true,ite_false,ite_true]
    · rw [pureFaceSeries_mul Ω C coord hcoord pc _ _ A.property.2 P.property.2]
      change (pureFace _ _ _ _ A).val*(pureFace _ _ _ _ P).val=P.val
      rw [hPA,hPP,one_mul]
    · rw [pureFaceSeries_mul Ω C coord hcoord pc _ _ P.property.2 A.property.2]
      change (pureFace _ _ _ _ P).val*(pureFace _ _ _ _ A).val=P.val
      rw [hPA,hPP,mul_one]
  have hPD : ∀j≤N,coeff j P.val=coeff j D.val:=by
    intro j hj
    rw [←hWP,←hface j hj]
    change coeff j (pureFaceSeries Ω coord pc W.val)=coeff j (pureFaceSeries Ω coord pc F.val)
    rw [coeff_pureFaceSeries,coeff_pureFaceSeries,hprod j hj]
  change ∀j≤N,coeff j F.val=coeff j (if pos then D.val*A.val else A.val*D.val)
  intro j hj
  rw [hprod j hj]
  change coeff j W.val=coeff j (if pos then D.val*A.val else A.val*D.val)
  rw [hPW]
  cases pos <;> simp only [Bool.false_eq_true,ite_false,ite_true]
  · exact FormalLog.mul_coeff_congr A.val P.val A.val D.val j (fun _ _=>rfl)
      (fun k hk=>hPD k (hk.trans hj))
  · exact FormalLog.mul_coeff_congr P.val A.val D.val A.val j
      (fun k hk=>hPD k (hk.trans hj)) (fun _ _=>rfl)
end
end ElementaryPositivity.QuantumTorus

end
section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries PowerSeriesAdjoint RootTruncation WallUnits
noncomputable section
variable {M I : Type*} [AddCommGroup M] [Fintype I] [DecidableEq I]
variable (Ω : M →+ M →+ ℤ) (C : (I → ℤ) →+ M)
variable (coord : M →+ (I → ℤ)) (hcoord : ∀d,coord (C d)=d) (pc : I)

def boundedNonpFrame (w : M →+ ℤ) (P : AddSubmonoid M) (n : ℤ) : AddSubmonoid M where
  carrier:={m | 0≤w m ∧ (w m≤n → m∈P)}
  zero_mem':=⟨by simp,fun _=>P.zero_mem⟩
  add_mem':=by
    intro a b ha hb
    refine ⟨by simpa only [map_add] using add_nonneg ha.1 hb.1,?_⟩
    intro hh
    have ha0 : 0≤w a:=ha.1
    have hb0 : 0≤w b:=hb.1
    have hh' : w a+w b≤n:=by simpa only [map_add] using hh
    exact P.add_mem (ha.2 (by omega)) (hb.2 (by omega))

include hcoord in
def simpleCompleted : CompletedPositive LaurentRay.vUnit Ω C :=
  ⟨normalizedSimple Ω (simpleRoot C pc),normalizedSimple_constant Ω _,by
    rw [←literalIncoming_simple Ω C coord hcoord pc]
    exact (literalIncomingCompleted Ω C (simpleIncomingList C) (simpleIncomingList_allowed C)
      (simpleRoot C pc)).property.2⟩

include hcoord in
lemma simpleCompleted_ray (j : ℕ) (m : M)
    (hm : coeff (j+1) (simpleCompleted Ω C coord hcoord pc).val m≠0) :
    OnPositiveRay (simpleRoot C pc) m := by
  change coeff (j+1) (normalizedSimple Ω (simpleRoot C pc)) m≠0 at hm
  rw [normalizedSimple,coeff_raySeries] at hm
  have he : m=(j+1) • simpleRoot C pc:=by
    by_contra hh; exact hm (Finsupp.single_eq_of_ne hh)
  exact ⟨1,j+1,by omega,by omega,by simpa only [one_nsmul] using he⟩

include hcoord in
def simpleOrientedCompleted (pos : Bool) : CompletedPositive LaurentRay.vUnit Ω C :=
  if pos then simpleCompleted Ω C coord hcoord pc else
    completedInverse LaurentRay.vUnit Ω C (simpleCompleted Ω C coord hcoord pc)

include hcoord in
lemma simpleOrientedCompleted_value (pos : Bool) :
    (simpleOrientedCompleted Ω C coord hcoord pc pos).val=
      simpleOriented Ω pos (simpleRoot C pc) := by cases pos <;> rfl

include hcoord in
lemma simple_cut_chart_bound (hΩ : ∀m,Ω m m=0) (pos : Bool)
    (A F : CompletedPositive LaurentRay.vUnit Ω C) (N : ℕ) (n : ℤ)
    (hprod : ∀j≤N,coeff j F.val=coeff j
      (if pos then (normalizedSimple Ω (simpleRoot C pc))*A.val
       else A.val*(normalizedSimple Ω (simpleRoot C pc))))
    (htrend : ∀j≤N,∀m,coeff j A.val m≠0 → 0≤ sideSign pos*Ω (simpleRoot C pc) m)
    (hbound : ∀j≤N,∀m,coeff j A.val m≠0 → nonpDegree coord pc m≤n →
      m∈fiberCone coord pc (mutationPairing Ω C pc) (sideSign pos))
    (h : M →+ ℝ) (hside : cutSide (!pos) h (simpleRoot C pc)) :
    ∀j≤N,∀m,coeff j (chartZero LaurentRay.vUnit Ω C h F).val m≠0 →
      nonpDegree coord pc m≤n → m∈fiberCone coord pc (mutationPairing Ω C pc) (-sideSign pos) := by
  let D:=simpleCompleted Ω C coord hcoord pc
  let O:=simpleOrientedCompleted Ω C coord hcoord pc pos
  let G:=completedConjugate LaurentRay.vUnit Ω C O A
  have hGval : G.val=adjoint (simpleOriented Ω pos (simpleRoot C pc)) A.val:=by
    change O.val*A.val*invOfUnit O.val 1=_
    rw [show O.val=simpleOriented Ω pos (simpleRoot C pc) from simpleOrientedCompleted_value Ω C coord hcoord pc pos]
    rfl
  let P:=fiberCone coord pc (mutationPairing Ω C pc) (-sideSign pos)
  let Q:=boundedNonpFrame (nonpDegree coord pc) P n
  have hQ : ∀j≤N,coeff j G.val∈supportedSubring LaurentRay.vUnit Ω Q:=by
    intro j hj m hmQ
    by_contra hm
    apply hmQ
    refine ⟨nonpDegree_root_nonneg C coord hcoord pc (chart_root_of_ne LaurentRay.vUnit Ω C G j m hm),?_⟩
    intro hn
    apply simpleOriented_adjoint_fiber Ω C coord hcoord pc hΩ pos A.val j n
      (fun a _=>A.property.2 a) (fun a ha=>htrend a (ha.trans hj))
      (fun a ha=>hbound a (ha.trans hj)) m ?_ hn
    rwa [←hGval]
  let Gc:=completedCut LaurentRay.vUnit Ω C N G
  have hchartQ:= (chartThree_supported LaurentRay.vUnit Ω C h Q Gc
    (completedCut_supported LaurentRay.vUnit Ω C N G Q hQ)).2.1
  have hremove : ∀j≤N,coeff j (chartZero LaurentRay.vUnit Ω C h F).val=
      coeff j (chartZero LaurentRay.vUnit Ω C h G).val:=by
    cases pos
    · have Hprod : ∀j≤N,coeff j F.val=coeff j (completedMul LaurentRay.vUnit Ω C D G).val:=by
        intro j hj
        rw [hprod j hj]
        simp only [Bool.false_eq_true,ite_false]
        change coeff j (A.val*D.val)=coeff j (D.val*G.val)
        rw [hGval]
        change coeff j (A.val*D.val)=coeff j (D.val*adjoint (invOfUnit D.val 1) A.val)
        rw [adjoint_inverse _ _ D.property.1,←mul_assoc,←mul_assoc,mul_invOfUnit _ 1 D.property.1,one_mul]
      intro j hj
      rw [chartZero_congr_through LaurentRay.vUnit Ω C h F _ N Hprod j hj]
      apply chartZero_left_positive LaurentRay.vUnit Ω C h D G N ?_ j hj
      intro k hk m hm
      have HR:=simpleCompleted_ray Ω C coord hcoord pc k m hm
      exact (HR.eval h).1.mpr hside
    · have Hprod : ∀j≤N,coeff j F.val=coeff j (completedMul LaurentRay.vUnit Ω C G D).val:=by
        intro j hj
        rw [hprod j hj]
        simp only [ite_true]
        change coeff j (D.val*A.val)=coeff j (G.val*D.val)
        rw [hGval]
        change coeff j (D.val*A.val)=coeff j (adjoint D.val A.val*D.val)
        rw [adjoint,mul_assoc,mul_assoc,invOfUnit_mul _ 1 D.property.1,mul_one]
      intro j hj
      rw [chartZero_congr_through LaurentRay.vUnit Ω C h F _ N Hprod j hj]
      apply chartZero_right_negative LaurentRay.vUnit Ω C h G D N ?_ j hj
      intro k hk m hm
      have HR:=simpleCompleted_ray Ω C coord hcoord pc k m hm
      exact (HR.eval h).2.2.mpr hside
  have hcut:=chartZero_congr_through LaurentRay.vUnit Ω C h Gc G N
    (fun j hj=>coeff_cut_of_le G.val hj)
  intro j hj m hm hn
  have hmGc : coeff j (chartZero LaurentRay.vUnit Ω C h Gc).val m≠0:=by
    rw [hcut j hj,←hremove j hj]; exact hm
  have hmQ : m∈Q:=by by_contra hh; exact hmGc (hchartQ j m hh)
  exact hmQ.2 hn
end
end ElementaryPositivity.QuantumTorus

end

end OAI
