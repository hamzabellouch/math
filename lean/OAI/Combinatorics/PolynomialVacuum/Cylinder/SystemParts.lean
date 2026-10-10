import OAI.Combinatorics.PolynomialVacuum.Cylinder.CodedPartition

namespace OAI

namespace PolynomialVacuumCylinder
open Classical PolynomialVacuumAlgebra
variable {M H : ℕ} [NeZero M]
namespace ArcSystem
noncomputable def part (S : ArcSystem (bandSites M H)) (b : Bool) : ArcSystem (bandSites M H) :=
  ⟨S.val.filter (fun A => A.port.1=b),S.property.mono (Finset.filter_subset _ _)⟩
@[simp] theorem mem_part (S : ArcSystem (bandSites M H)) (b : Bool) (A : BoundaryArc (bandSites M H)) :
    A∈(S.part b).val ↔ A∈S.val ∧ A.port.1=b := Finset.mem_filter

theorem part_code (S : ArcSystem (bandSites M H)) (b : Bool) (p : Bool × ZMod M) :
    (S.part b).code p=if p.1=b then S.code p else .inl () := by
  by_cases he : ∃A∈S.val,A.port=p
  · obtain ⟨A,hA,rfl⟩:=he
    by_cases hb : A.port.1=b
    · rw [ite_eq_left hb,code_member _ A ((mem_part _ _ _).mpr ⟨hA,hb⟩),S.code_member A hA]
    · rw [ite_eq_right hb,code_empty]
      rintro ⟨B,hB,hp⟩
      have hh:= (mem_part S b B).mp hB
      exact hb (hp ▸ hh.2)
  · have hn : ¬∃A∈(S.part b).val,A.port=p := by
      rintro ⟨A,hA,hp⟩
      exact he ⟨A,((mem_part _ _ _).mp hA).1,hp⟩
    rw [code_empty _ p hn,S.code_empty p he]
    split <;> rfl

theorem parts_disjoint (S : ArcSystem (bandSites M H)) : Disjoint (S.part false).val (S.part true).val := by
  apply Finset.disjoint_left.mpr
  intro A hA hB
  have ha:=((mem_part S false A).mp hA).2
  have hb:=((mem_part S true A).mp hB).2
  simp [ha] at hb

theorem parts_union (S : ArcSystem (bandSites M H)) : (S.part false).val∪(S.part true).val=S.val := by
  ext A
  simp only [Finset.mem_union,mem_part]
  cases A.port.1 <;> simp

theorem parts_weight (S : ArcSystem (bandSites M H)) : S.weight=(S.part false).weight*(S.part true).weight := by
  unfold weight
  rw [← S.parts_union,Finset.prod_union S.parts_disjoint]

theorem parts_current (S : ArcSystem (bandSites M H)) : S.current=(S.part false).current+(S.part true).current := by
  unfold current
  rw [← S.parts_union,Finset.sum_union S.parts_disjoint]

theorem short_top_zero (S : ArcSystem (bandSites M H)) (hS : arcChoiceLength S.code<H)
    (hb : ∀A∈S.val,A.port.1=false) (i : ZMod M) : S.current ((i,(H : ℤ)),0)=0 := by
  simp only [current,Finsupp.finsetSum_apply]
  apply Finset.sum_eq_zero
  intro A hA
  have hl := lt_of_le_of_lt (S.word_le_code_length A hA) hS
  let B:=A.archOfShort hl
  have hh : B.val.height≤H := by
    have hw:=B.val.height_le_length
    simp only [B,BoundaryArc.archOfShort_word] at hw
    exact (hw.trans_lt hl).le
  rw [eq_atPort_of_shape A B (A.archOfShort_shape hl) hh,atPort_top_current]
  simp [halfArcTop,hb A hA]

theorem short_bottom_zero (S : ArcSystem (bandSites M H)) (hS : arcChoiceLength S.code<H)
    (hb : ∀A∈S.val,A.port.1=true) (i : ZMod M) : S.current ((i,0),0)=0 := by
  simp only [current,Finsupp.finsetSum_apply]
  apply Finset.sum_eq_zero
  intro A hA
  have hl := lt_of_le_of_lt (S.word_le_code_length A hA) hS
  let B:=A.archOfShort hl
  have hh : B.val.height≤H := by
    have hw:=B.val.height_le_length
    simp only [B,BoundaryArc.archOfShort_word] at hw
    exact (hw.trans_lt hl).le
  rw [eq_atPort_of_shape A B (A.archOfShort_shape hl) hh,atPort_bottom_current]
  simp [halfArcBottom,hb A hA]

theorem part_length (S : ArcSystem (bandSites M H)) (b : Bool) :
    arcChoiceLength (S.part b).code≤arcChoiceLength S.code := by
  apply Finset.sup_le
  intro p _
  rw [part_code]
  split_ifs
  · exact Finset.le_sup (f:=fun p => (S.code p).length) (Finset.mem_univ p)
  · exact Nat.zero_le _

theorem parts_matches (S : ArcSystem (bandSites M H)) (hS : arcChoiceLength S.code<H)
    (inp out : ZMod M → Spin) :
    matchesBoundary (recoverVertical H S.current) inp out ↔
      matchesBoundary (recoverVertical H (S.part false).current) inp (fun _ => .zero) ∧
      matchesBoundary (recoverVertical H (S.part true).current) (fun _ => .zero) out := by
  have hb := (S.part true).short_bottom_zero (lt_of_le_of_lt (S.part_length true) hS)
    (fun A hA => ((mem_part S true A).mp hA).2)
  have ht := (S.part false).short_top_zero (lt_of_le_of_lt (S.part_length false) hS)
    (fun A hA => ((mem_part S false A).mp hA).2)
  have h0 : recoverVertical H S.current 0=recoverVertical H (S.part false).current 0 := by
    funext i
    simp only [recoverVertical,Fin.val_zero,Nat.cast_zero,S.parts_current,Finsupp.add_apply,hb,add_zero]
  have hH : recoverVertical H S.current (Fin.last H)=recoverVertical H (S.part true).current (Fin.last H) := by
    funext i
    simp only [recoverVertical,Fin.val_last,S.parts_current,Finsupp.add_apply,ht,zero_add]
  have hz0 : recoverVertical H (S.part true).current 0=(fun _=>Spin.zero) := by
    funext i; simp [recoverVertical,hb,spinOfCharge]
  have hzH : recoverVertical H (S.part false).current (Fin.last H)=(fun _=>Spin.zero) := by
    funext i; simp [recoverVertical,ht,spinOfCharge]
  simp only [matchesBoundary,h0,hH,hz0,hzH,true_and,and_true]
end ArcSystem
end PolynomialVacuumCylinder

end OAI
