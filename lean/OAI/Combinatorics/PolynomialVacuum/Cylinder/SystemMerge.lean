import OAI.Combinatorics.PolynomialVacuum.Cylinder.SystemParts

namespace OAI

namespace PolynomialVacuumCylinder
open Classical
variable {M H : ℕ} [NeZero M]
noncomputable def cutCode (b : Bool) (s : Bool × ZMod M → ArcChoice M) (p : Bool × ZMod M) : ArcChoice M :=
  if p.1=b then s p else .inl ()

theorem cutCode_length (s : Bool × ZMod M → ArcChoice M) (b : Bool) :
    arcChoiceLength (cutCode b s)≤arcChoiceLength s := by
  apply Finset.sup_le
  intro p _
  unfold cutCode
  split_ifs
  · exact Finset.le_sup (f:=fun p => (s p).length) (Finset.mem_univ p)
  · exact Nat.zero_le _

namespace ArcSystem

theorem part_code_eq (S : ArcSystem (bandSites M H)) (b : Bool) : (S.part b).code=cutCode b S.code := by
  funext p; exact S.part_code b p

theorem only_of_cutCode (S : ArcSystem (bandSites M H)) (b : Bool) (s : Bool × ZMod M → ArcChoice M)
    (hc : S.code=cutCode b s) : ∀A∈S.val,A.port.1=b := by
  intro A hA
  have hh:=S.code_member A hA
  rw [hc,cutCode] at hh
  by_contra he
  simp [he] at hh

theorem cross_disjoint (S T : ArcSystem (bandSites M H))
    (hS : ∀A∈S.val,A.port.1=false) (hT : ∀A∈T.val,A.port.1=true)
    (hH : arcChoiceLength S.code+arcChoiceLength T.code<H)
    (A : BoundaryArc (bandSites M H)) (hA : A∈S.val)
    (B : BoundaryArc (bandSites M H)) (hB : B∈T.val) : Disjoint A.vertices B.vertices := by
  have ha : A.word.length<H := by have := S.word_le_code_length A hA; omega
  have hb : B.word.length<H := by have := T.word_le_code_length B hB; omega
  let a:=A.archOfShort ha
  let b:=B.archOfShort hb
  have ah : a.val.height≤H := by
    have hh:=a.val.height_le_length
    simp only [a,BoundaryArc.archOfShort_word] at hh
    exact hh.trans ha.le
  have bh : b.val.height≤H := by
    have hh:=b.val.height_le_length
    simp only [b,BoundaryArc.archOfShort_word] at hh
    exact hh.trans hb.le
  have heA:=eq_atPort_of_shape A a (A.archOfShort_shape ha) ah
  have heB:=eq_atPort_of_shape B b (B.archOfShort_shape hb) bh
  rw [heA,heB]
  apply atPort_cross_disjoint
  · simp [hS A hA,hT B hB]
  · simp only [a,b,BoundaryArc.archOfShort_word]
    exact (Nat.add_le_add (S.word_le_code_length A hA) (T.word_le_code_length B hB)).trans hH.le

noncomputable def merge (S T : ArcSystem (bandSites M H))
    (hS : ∀A∈S.val,A.port.1=false) (hT : ∀A∈T.val,A.port.1=true)
    (hH : arcChoiceLength S.code+arcChoiceLength T.code<H) : ArcSystem (bandSites M H) :=
  ⟨S.val∪T.val,by
    intro A hA B hB hne
    rcases Finset.mem_union.mp hA with hA | hA <;> rcases Finset.mem_union.mp hB with hB | hB
    · exact S.property hA hB hne
    · exact cross_disjoint S T hS hT hH A hA B hB
    · exact (cross_disjoint S T hS hT hH B hB A hA).symm
    · exact T.property hA hB hne⟩

theorem merge_parts (S T : ArcSystem (bandSites M H))
    (hS : ∀A∈S.val,A.port.1=false) (hT : ∀A∈T.val,A.port.1=true)
    (hH : arcChoiceLength S.code+arcChoiceLength T.code<H) :
    (merge S T hS hT hH).part false=S ∧ (merge S T hS hT hH).part true=T := by
  constructor <;> apply Subtype.ext <;> apply Finset.ext <;> intro A
  · simp only [mem_part,merge,Finset.mem_union]
    constructor
    · rintro ⟨ha,hb⟩
      rcases ha with ha | ha
      · exact ha
      · have hh:=hT A ha; simp [hb] at hh
    · intro ha; exact ⟨Or.inl ha,hS A ha⟩
  · simp only [mem_part,merge,Finset.mem_union]
    constructor
    · rintro ⟨ha,hb⟩
      rcases ha with ha | ha
      · have hh:=hS A ha; simp [hb] at hh
      · exact ha
    · intro ha; exact ⟨Or.inr ha,hT A ha⟩

theorem code_of_parts (R : ArcSystem (bandSites M H)) (s : Bool × ZMod M → ArcChoice M)
    (hf : (R.part false).code=cutCode false s) (ht : (R.part true).code=cutCode true s) : R.code=s := by
  funext p
  have h0:=congrFun hf p
  have h1:=congrFun ht p
  simp only [part_code,cutCode] at h0 h1
  cases hp:p.1 <;> simp [hp] at h0 h1 <;> assumption

theorem exists_code_cut_iff (s : Bool × ZMod M → ArcChoice M) (hH : 2*arcChoiceLength s<H) :
    (∃S : ArcSystem (bandSites M H),S.code=s) ↔
      (∃S : ArcSystem (bandSites M H),S.code=cutCode false s) ∧
      (∃T : ArcSystem (bandSites M H),T.code=cutCode true s) := by
  constructor
  · rintro ⟨S,rfl⟩
    exact ⟨⟨S.part false,S.part_code_eq false⟩,⟨S.part true,S.part_code_eq true⟩⟩
  · rintro ⟨⟨S,hS⟩,⟨T,hT⟩⟩
    have hs:=S.only_of_cutCode false s hS
    have ht:=T.only_of_cutCode true s hT
    have hh : arcChoiceLength S.code+arcChoiceLength T.code<H := by
      rw [hS,hT]
      have := cutCode_length s false; have := cutCode_length s true; omega
    let R:=S.merge T hs ht hh
    have hp:=merge_parts S T hs ht hh
    refine ⟨R,R.code_of_parts s ?_ ?_⟩
    · rw [hp.1]; exact hS
    · rw [hp.2]; exact hT
end ArcSystem
end PolynomialVacuumCylinder

end OAI
