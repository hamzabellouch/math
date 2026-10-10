import Mathlib
import OAI.Combinatorics.Chromatic.Walls.SimpleAdjointFiber
import OAI.Combinatorics.Chromatic.Walls.SimpleIncomingElement

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries WallUnits
noncomputable section
variable {M I : Type*} [AddCommGroup M] [Fintype I] [DecidableEq I]
variable (Ω : M →+ M →+ ℤ) (C : (I → ℤ) →+ M)
variable (coord : M →+ (I → ℤ)) (hcoord : ∀d,coord (C d)=d) (pc : I)

lemma ordered_filter_partition {A : Type*} (P : A → Prop) [DecidablePred P] (l : List A)
    (hl : l.Pairwise (fun a b=>P b → P a)) :
    l.filter (fun a=>decide (P a)) ++ l.filter (fun a=>decide (¬P a))=l := by
  induction l with
  | nil=>rfl
  | cons a l ih=>
    have HH:=List.pairwise_cons.mp hl
    by_cases ha : P a
    · simpa [List.filter_cons,ha] using congrArg (List.cons a) (ih HH.2)
    · have hz : l.filter (fun a=>decide (P a))=[]:=by
        apply List.filter_eq_nil_iff.mpr
        intro b hb
        simpa using (fun hp=>ha (HH.1 b hb hp) : ¬ P b)
      have IH:=ih HH.2
      rw [hz,List.nil_append] at IH
      simp [ha,hz]
      intro b hb hp
      exact ha (HH.1 b hb hp)
lemma alternating_int_swap (hΩ : ∀m,Ω m m=0) (a b : M) : Ω a b= -Ω b a := by
  have H:=hΩ (a+b)
  simp only [map_add,AddMonoidHom.add_apply,hΩ,zero_add,add_zero] at H
  omega
include hcoord in
lemma ordered_pure_partition (hΩ : ∀m,Ω m m=0) (pos : Bool) (l : List M)
    (hl : l.Pairwise (fun a b=>0<Ω a b))
    (hroot : ∀q∈l,∃d,0<d ∧ HasRootDegree C d q)
    (htrend : ∀q∈l,0≤ sideSign pos*Ω (simpleRoot C pc) q) :
    (if pos then
      l.filter (fun q=>decide (nonpDegree coord pc q=0)) ++
        l.filter (fun q=>decide (nonpDegree coord pc q≠0))
     else
      l.filter (fun q=>decide (nonpDegree coord pc q≠0)) ++
        l.filter (fun q=>decide (nonpDegree coord pc q=0)))=l := by
  cases pos
  · simp only [Bool.false_eq_true,ite_false]
    suffices H : l.Pairwise (fun a b => nonpDegree coord pc b ≠ 0 →
        nonpDegree coord pc a ≠ 0) from by
      simpa only [not_not] using ordered_filter_partition (fun q=>nonpDegree coord pc q≠0) l H
    apply hl.imp_of_mem
    intro a b ha hb hab hnb hpa
    obtain ⟨d,hd,hr⟩:=hroot a ha
    rw [nonp_zero_root C coord hcoord pc hr hpa,map_nsmul] at hab
    have HH:=htrend b hb
    simp only [sideSign,Bool.false_eq_true,ite_false,neg_one_mul] at HH
    have hdZ : 0<(d:ℤ):=by exact_mod_cast hd
    change 0<(d:ℤ)*Ω (simpleRoot C pc) b at hab
    nlinarith
  · simp only [ite_true]
    apply ordered_filter_partition (fun q=>nonpDegree coord pc q=0) l
    apply hl.imp_of_mem
    intro a b ha hb hab hpb
    obtain ⟨d,hd,hr⟩:=hroot b hb
    rw [nonp_zero_root C coord hcoord pc hr hpb,map_nsmul] at hab
    have HH:=htrend a ha
    simp only [sideSign,ite_true,one_mul] at HH
    rw [alternating_int_swap Ω hΩ a (simpleRoot C pc)] at hab
    have hdZ : 0<(d:ℤ):=by exact_mod_cast hd
    change 0<(d:ℤ)*(-Ω (simpleRoot C pc) a) at hab
    exact (by nlinarith : False).elim

lemma ray_nonp_zero {q m : M} (hq : nonpDegree coord pc q=0) (hm : OnPositiveRay q m) :
    nonpDegree coord pc m=0 := by
  obtain ⟨a,b,ha,hb,he⟩:=hm
  have H:=congrArg (nonpDegree coord pc) he
  rw [map_nsmul,map_nsmul,hq,nsmul_zero,nsmul_eq_mul] at H
  exact (mul_eq_zero.mp H).resolve_left (by exact_mod_cast Nat.ne_of_gt ha)
lemma ray_nonp_pos {q m : M} (hq : 0<nonpDegree coord pc q) (hm : OnPositiveRay q m) :
    0<nonpDegree coord pc m := by
  obtain ⟨a,b,ha,hb,he⟩:=hm
  have H:=congrArg (nonpDegree coord pc) he
  simp only [map_nsmul,nsmul_eq_mul] at H
  have haZ : 0<(a:ℤ):=by exact_mod_cast ha
  have hbZ : 0<(b:ℤ):=by exact_mod_cast hb
  nlinarith
lemma pureFace_of_strict_positive (F : CompletedPositive LaurentRay.vUnit Ω C)
    (hF : ∀j m,coeff (j+1) F.val m≠0 → 0<nonpDegree coord pc m) :
    (pureFace Ω C coord pc F).val=1 := by
  apply PowerSeries.ext
  intro j
  cases j with
  | zero=>simpa only [coeff_zero_eq_constantCoeff_apply,map_one] using (pureFace _ _ _ _ F).property.1
  | succ j=>
    rw [coeff_one,ite_eq_right (by omega)]
    apply Finsupp.ext
    intro m
    change coeff (j+1) (pureFaceSeries Ω coord pc F.val) m=0
    rw [pureFaceSeries_apply]
    split_ifs with hh
    · by_contra hn
      have HG:=hF j m hn
      omega
    · rfl
lemma pureFace_of_strict_zero (F : CompletedPositive LaurentRay.vUnit Ω C)
    (hF : ∀j m,coeff (j+1) F.val m≠0 → nonpDegree coord pc m=0) :
    (pureFace Ω C coord pc F).val=F.val := by
  apply PowerSeries.ext
  intro j
  apply pureFaceSeries_eq_through Ω coord pc F.val j ?_ j le_rfl
  intro k hk m hm
  cases k with
  | zero=>
    rw [coeff_zero_eq_constantCoeff_apply,F.property.1] at hm
    have hm0 : m=0:=by by_contra hh; exact hm (Finsupp.single_eq_of_ne hh)
    rw [hm0,map_zero]
  | succ k=>exact hF k m hm

lemma pureFace_list_nonpure (_hcoord : ∀d,coord (C d)=d) (pc : I)
    (l : List M) (F : M → CompletedPositive LaurentRay.vUnit Ω C)
    (hl : ∀q∈l,0<nonpDegree coord pc q)
    (hF : ∀q∈l,∀j m,coeff (j+1) (F q).val m≠0 → OnPositiveRay q m) :
    (pureFace Ω C coord pc (completedListProduct LaurentRay.vUnit Ω C l F)).val=1 := by
  apply pureFace_of_strict_positive Ω C coord pc
  intro j m hm
  by_contra hn
  apply hm
  apply strict_list_product_through LaurentRay.vUnit Ω C l F
    (fun m=>0<nonpDegree coord pc m)
    (fun a b ha hb=>by simpa only [map_add] using add_pos ha hb) (j+1) ?_ j le_rfl m hn
  intro q hq k hk m hm
  by_contra hv
  exact hm (ray_nonp_pos coord pc (hl q hq) (hF q hq k m hv))
lemma pureFace_list_pure (_hcoord : ∀d,coord (C d)=d) (pc : I)
    (l : List M) (F : M → CompletedPositive LaurentRay.vUnit Ω C)
    (hl : ∀q∈l,nonpDegree coord pc q=0)
    (hF : ∀q∈l,∀j m,coeff (j+1) (F q).val m≠0 → OnPositiveRay q m) :
    (pureFace Ω C coord pc (completedListProduct LaurentRay.vUnit Ω C l F)).val=
      (completedListProduct LaurentRay.vUnit Ω C l F).val := by
  apply pureFace_of_strict_zero Ω C coord pc
  intro j m hm
  by_contra hn
  apply hm
  apply strict_list_product_through LaurentRay.vUnit Ω C l F
    (fun m=>nonpDegree coord pc m=0)
    (fun a b ha hb=>by simp only [map_add,ha,hb,add_zero]) (j+1) ?_ j le_rfl m hn
  intro q hq k hk m hm
  by_contra hv
  exact hm (ray_nonp_zero coord pc (hl q hq) (hF q hq k m hv))
end
end ElementaryPositivity.QuantumTorus

end

end OAI
