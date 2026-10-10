import OAI.Combinatorics.ThinTrees.Records

namespace OAI

section
open scoped Classical
open Matrix

namespace StrongThinTree.MultiGraph.Hierarchy
noncomputable section
open Finset StrongThinTree.Geometry
variable {n m h : ℕ} (H : Hierarchy n)

lemma predecessor_dichotomy {A t : Finset (Fin n)} {P : Finset (Finset (Fin n))}
    (ht : t ∈ H.domain A P) (hP : ∀S ∈ P, S ∈ H.nodes)
    {S : Finset (Fin n)} (hS : S ∈ P) : S ⊂ t ∨ Disjoint S t := by
  obtain ⟨htn,hta,htP⟩ := H.mem_domain.mp ht
  rcases H.laminar S (hP S hS) t htn with hSt | htS | hdis
  · left
    apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨hSt,?_⟩
    intro heq
    exact htP S hS (heq ▸ Subset.refl _)
  · exact (htP S hS htS).elim
  · exact Or.inr hdis

lemma domain_descendant_partition {A t : Finset (Fin n)} {P : Finset (Finset (Fin n))}
    (ht : t ∈ H.domain A P) (hP : ∀S ∈ P, S ∈ H.nodes) :
    H.domain t (P.filter (fun S => S ⊂ t)) =
      (H.domain A P).filter (fun C => C ⊆ t) := by
  obtain ⟨htn,htA,htP⟩ := H.mem_domain.mp ht
  ext C
  simp only [mem_filter,mem_domain]
  constructor
  · rintro ⟨hCn,hCt,hCP⟩
    refine ⟨⟨hCn,hCt.trans htA,?_⟩,hCt⟩
    intro S hS hCS
    rcases H.predecessor_dichotomy ht hP hS with hSt | hdis
    · exact hCP S ⟨hS,hSt⟩ hCS
    · obtain ⟨v,hv⟩ := H.nonempty C hCn
      exact Finset.disjoint_left.mp hdis (hCS hv) (hCt hv)
  · rintro ⟨⟨hCn,hCA,hCP⟩,hCt⟩
    exact ⟨hCn,hCt,fun S hS => hCP S hS.1⟩

lemma domain_avoid_partition (A t : Finset (Fin n)) (P : Finset (Finset (Fin n))) :
    H.domain A (insert t P) = (H.domain A P).filter (fun C => ¬C ⊆ t) := by
  ext C
  simp only [mem_domain,mem_filter,mem_insert]
  constructor
  · rintro ⟨hCn,hCA,hCP⟩
    exact ⟨⟨hCn,hCA,fun S hS => hCP S (Or.inr hS)⟩,hCP t (Or.inl rfl)⟩
  · rintro ⟨⟨hCn,hCA,hCP⟩,hCt⟩
    exact ⟨hCn,hCA,fun S hS => by rcases hS with rfl | hS; exact hCt; exact hCP S hS⟩

namespace Record
variable (G : MultiGraph n m) (X : Fin n → Fin h → ℝ)

def innerRecord (B : Record n) (t : Finset (Fin n)) (a b : ℝ) : Record n :=
  ⟨RadialShell.hollow B.shell.center a b,t,B.predecessors.filter (fun S => S ⊂ t),none⟩
def outsideRecord (B : Record n) (t : Finset (Fin n)) (a b : ℝ) : Record n :=
  ⟨RadialShell.hollow B.shell.center a b,B.owner,B.predecessors,some t⟩

lemma central_conflict {B : Record n} (hshape : B.Shape H) (hno : B.avoided = none)
    {t : Finset (Fin n)} (ht : t ∈ B.conflict H) (a b c d : ℝ) :
    (B.innerRecord t a b).conflict H = (B.conflict H).filter (fun C => C ⊆ t) ∧
    (B.outsideRecord t c d).conflict H = (B.conflict H).filter (fun C => ¬C ⊆ t) := by
  have heq : B.excluded = B.predecessors := by simp [excluded,hno]
  have hP : ∀S ∈ B.predecessors, S ∈ H.nodes := fun S hS => (hshape.2 S (heq.symm ▸ hS)).1
  have ht' : t ∈ H.domain B.owner B.predecessors := by simpa only [conflict,heq] using ht
  constructor
  · simpa only [conflict,innerRecord,excluded,Option.toFinset_none,union_empty,hno] using
      H.domain_descendant_partition ht' hP
  · simpa only [conflict,outsideRecord,excluded,Option.toFinset_some,union_singleton,hno,Option.toFinset_none,union_empty] using
      H.domain_avoid_partition B.owner t B.predecessors

lemma central_domain_disjoint {B : Record n} (hshape : B.Shape H) (hno : B.avoided = none)
    {t : Finset (Fin n)} (ht : t ∈ B.conflict H) (a b c d : ℝ) :
    Disjoint ((B.innerRecord t a b).conflict H) ((B.outsideRecord t c d).conflict H) := by
  obtain ⟨h1,h2⟩ := central_conflict H hshape hno ht a b c d
  rw [h1,h2,Finset.disjoint_left]
  intro C hC hD
  exact (mem_filter.mp hD).2 (mem_filter.mp hC).2

lemma protected_same_side {B : Record n} (hB : B.Protected G X)
    {u v : Fin n} {e : Fin m}
    (he : (G.left e = u ∧ G.right e = v) ∨ (G.left e = v ∧ G.right e = u))
    (hu : l1dist (X u) (X B.shell.center) < B.shell.outer) :
    ∀S ∈ B.predecessors, u ∈ S ↔ v ∈ S := by
  intro S hS
  have hn : e ∉ G.cut univ S := by
    intro hc
    have hh := hB S hS e hc
    rcases he with he | he
    · rw [he.1] at hh
      linarith [hh.1]
    · rw [he.2] at hh
      linarith [hh.2]
  simp only [cut,mem_filter,mem_univ,true_and] at hn
  rcases he with he | he <;> simp only [he.1,he.2] at hn <;> tauto

lemma central_valid {q a b δ : ℝ} {B : Record n}
    (hB : B.Valid H G X (q/4)) (hno : B.avoided = none)
    (hq : 0 ≤ q) (hconn : H.LocallyConnectedReal G q)
    {t : Finset (Fin n)} (ht : t ∈ B.conflict H) (htstrict : t ⊂ B.owner)
    (ha : B.shell.inner ≤ a) (hb : b ≤ B.shell.outer)
    (hδ : 0 < δ) (hab : a+δ < b-δ)
    {R : Finset (Fin n)} (hR : R ⊆ H.parent t \ t)
    (hRc : G.EdgeConnectedReal R (q/4))
    {u₁ u₂ v₁ v₂ : Fin n} (hu₁ : u₁ ∈ t) (hu₂ : u₂ ∈ t)
    (hv₁ : v₁ ∈ R) (hv₂ : v₂ ∈ R)
    (hu₁rad : l1dist (X u₁) (X B.shell.center) ≤ a+δ)
    (hu₂rad : b-δ ≤ l1dist (X u₂) (X B.shell.center))
    (hv₁rad : l1dist (X v₁) (X B.shell.center) ≤ a)
    (hv₂rad : b ≤ l1dist (X v₂) (X B.shell.center))
    {e : Fin m} (he : (G.left e = u₁ ∧ G.right e = v₁) ∨
      (G.left e = v₁ ∧ G.right e = u₁)) :
    (B.innerRecord t (a+δ) (b-δ)).Valid H G X (q/4) ∧
    (B.outsideRecord t a b).Valid H G X (q/4) := by
  have htn := (H.mem_domain.mp ht).1
  have htne : t ≠ univ := by
    intro hh
    have := htstrict.not_subset (by simp [hh])
    exact this
  have hparent : H.parent t ⊆ B.owner :=
    H.parent_minimal t htn htne B.owner hB.1.1 htstrict
  have hp : ∀S ∈ B.predecessors, S ∈ H.nodes ∧ S ⊂ B.owner :=
    fun S hS => hB.1.2 S (mem_union_left _ hS)
  have htex : t ∈ H.domain B.owner B.predecessors := by
    simpa only [conflict,excluded,hno,Option.toFinset_none,union_empty] using ht
  have hv₁out : v₁ ∉ t := (mem_sdiff.mp (hR hv₁)).2
  have hsame : ∀S ∈ B.predecessors, u₁ ∈ S ↔ v₁ ∈ S :=
    protected_same_side G X hB.2.1 he (by linarith)
  have huvavoid : ∀S ∈ B.predecessors, u₁ ∉ S ∧ v₁ ∉ S := by
    intro S hS
    rcases H.predecessor_dichotomy htex (fun S hS => (hp S hS).1) hS with hSt | hdis
    · have hvS : v₁ ∉ S := fun hh => hv₁out (hSt.subset hh)
      exact ⟨fun hh => hvS ((hsame S hS).mp hh),hvS⟩
    · have huS : u₁ ∉ S := fun hh => Finset.disjoint_left.mp hdis hh hu₁
      exact ⟨huS,fun hh => huS ((hsame S hS).mpr hh)⟩
  constructor
  · refine ⟨?_,?_,?_,?_⟩
    · refine ⟨htn,?_⟩
      intro S hS
      have hS' : S ∈ B.predecessors ∧ S ⊂ t := by
        simpa [excluded,innerRecord] using hS
      exact ⟨(hp S hS'.1).1,hS'.2⟩
    · intro S hS e he
      have hS' : S ∈ B.predecessors := (mem_filter.mp hS).1
      have hh := hB.2.1 S hS' e he
      exact ⟨(by dsimp [innerRecord,RadialShell.hollow]; linarith [hh.1]),
        (by dsimp [innerRecord,RadialShell.hollow]; linarith [hh.2])⟩
    · refine ⟨?_,hab,by simp [innerRecord,RadialShell.hollow],⟨u₁,hu₁rad⟩,⟨u₂,hu₂rad⟩⟩
      dsimp [innerRecord,RadialShell.hollow]
      linarith [hB.2.2.1.1]
    · refine ⟨t,?_,?_,⟨u₁,hu₁,?_,hu₁rad⟩,⟨u₂,hu₂,hu₂rad⟩⟩
      · simp [routing,innerRecord]
      · intro S hSn hSt
        exact (by linarith : q/4 ≤ q).trans (hconn t htn S hSn hSt)
      · apply (mem_leafSet H).mpr
        refine ⟨hu₁,?_⟩
        intro S hS
        have hS' : S ∈ B.predecessors ∧ S ⊂ t := by
          simpa [excluded,innerRecord] using hS
        exact (huvavoid S hS'.1).1
  · refine ⟨?_,?_,?_,?_⟩
    · refine ⟨hB.1.1,?_⟩
      intro S hS
      have hS' : S ∈ B.predecessors ∨ S = t := by
        simpa [excluded,outsideRecord,or_comm] using hS
      rcases hS' with hS | rfl
      · exact hp S hS
      · exact ⟨htn,htstrict⟩
    · intro S hS e he
      have hh := hB.2.1 S hS e he
      exact ⟨hb.trans hh.1,hb.trans hh.2⟩
    · refine ⟨?_,?_,by simp [outsideRecord,RadialShell.hollow],⟨v₁,hv₁rad⟩,⟨v₂,hv₂rad⟩⟩
      · exact hB.2.2.1.1.trans ha
      · dsimp [outsideRecord,RadialShell.hollow]
        linarith
    · refine ⟨R,?_,hRc,⟨v₁,hv₁,?_,hv₁rad⟩,⟨v₂,hv₂,hv₂rad⟩⟩
      · intro v hv
        obtain ⟨hvA,hvt⟩ := mem_sdiff.mp (hR hv)
        exact mem_sdiff.mpr ⟨hparent hvA,hvt⟩
      · apply (mem_leafSet H).mpr
        refine ⟨hparent (mem_sdiff.mp (hR hv₁)).1,?_⟩
        intro S hS
        have hS' : S ∈ B.predecessors ∨ S = t := by
          simpa [excluded,outsideRecord,or_comm] using hS
        rcases hS' with hS | rfl
        · exact (huvavoid S hS).2
        · exact hv₁out

end Record
end
end StrongThinTree.MultiGraph.Hierarchy

namespace StrongThinTree.MultiGraph.Hierarchy
noncomputable section
open Finset StrongThinTree.Geometry
variable {n m h : ℕ} (H : Hierarchy n) (G : MultiGraph n m)
  (X : Fin n → Fin h → ℝ)

namespace Record

def Compatible (B D : Record n) : Prop :=
  Disjoint (B.shell.support X) (D.shell.support X) ∨ Disjoint (B.conflict H) (D.conflict H)

lemma compatible_symm {B D : Record n} (h : B.Compatible H X D) : D.Compatible H X B :=
  h.elim (fun h => Or.inl h.symm) (fun h => Or.inr h.symm)

lemma compatible_self_iff (B : Record n) (hX : ∀v, binary (X v))
    (hshape : B.Shape H) (hvalid : B.shell.Valid X) : ¬B.Compatible H X B := by
  intro hh
  rcases hh with hh | hh
  · obtain ⟨w,hw⟩ := RadialShell.valid_support_nonempty hX hvalid
    exact Set.disjoint_left.mp hh hw hw
  · exact Finset.disjoint_left.mp hh (B.root_mem H hshape) (B.root_mem H hshape)

lemma compatible_heredity {B D C : Record n} (hBD : B.Compatible H X D)
    (hCB : C.shell.support X ⊆ B.shell.support X) (hCC : C.conflict H ⊆ B.conflict H) :
    C.Compatible H X D := by
  rcases hBD with hBD | hBD
  · exact Or.inl (hBD.mono_left hCB)
  · exact Or.inr (hBD.mono_left hCC)

lemma candidate_ancestor {A B : Record n} (hA : A.Shape H) (hB : B.Shape H)
    (horder : B.owner ⊂ A.owner → B.owner ∈ A.excluded)
    (hinter : (A.conflict H ∩ B.conflict H).Nonempty) : A.owner ∈ B.conflict H := by
  have hroots := (H.domain_root_test hA.1 hB.1
    (fun S hS => (hA.2 S hS).2) (fun S hS => (hB.2 S hS).2)).mp hinter
  rcases hroots with hh | hh
  · exact hh
  · have hba := (H.mem_domain.mp hh).2.1
    by_cases heq : B.owner = A.owner
    · exact heq ▸ B.root_mem H hB
    · have hs := horder (Finset.ssubset_iff_subset_ne.mpr ⟨hba,heq⟩)
      exact ((H.mem_domain.mp hh).2.2 B.owner hs (Subset.refl _)).elim

lemma insert_compatible {q : ℝ} {Z : Finset (Record n)}
    (hZ : H.LabeledArrangement G X q Z) {A B D : Record n}
    (hA : A.Shape H) (hB : B ∈ Z) (hD : D ∈ Z) (hne : B ≠ D)
    (hBA : A.owner ∈ B.conflict H)
    (horder : ∀F ∈ Z, F.owner ⊂ A.owner → F.owner ∈ A.excluded)
    (hAB : A.shell.support X ⊆ B.shell.support X) : A.Compatible H X D := by
  by_cases hgeo : Disjoint (A.shell.support X) (D.shell.support X)
  · exact Or.inl hgeo
  right
  by_contra hh
  have hinter : (A.conflict H ∩ D.conflict H).Nonempty := by
    apply Finset.nonempty_iff_ne_empty.mpr
    intro hempty
    exact hh (Finset.disjoint_iff_inter_eq_empty.mpr hempty)
  have hDA := candidate_ancestor H hA (hZ.1 D hD).1 (horder D hD) hinter
  have hBD : ¬Disjoint (B.shell.support X) (D.shell.support X) :=
    fun hd => hgeo (hd.mono_left hAB)
  exact Finset.disjoint_left.mp (hZ.2 hB hD hne hBD) hBA hDA

def Interior (C δ : ℝ) (A B : Record n) : Prop :=
  (A.conflict H ∩ B.conflict H).Nonempty ∧
    B.shell.inner+C*δ < l1dist (X A.shell.center) (X B.shell.center) ∧
    l1dist (X A.shell.center) (X B.shell.center) < B.shell.outer-C*δ

lemma interior_restriction {C δ : ℝ} {A B D : Record n}
    (hcenter : D.shell.center = B.shell.center)
    (ha : B.shell.inner ≤ D.shell.inner) (hb : D.shell.outer ≤ B.shell.outer)
    (hdom : D.conflict H ⊆ B.conflict H) (hh : A.Interior H X C δ D) :
    A.Interior H X C δ B := by
  obtain ⟨⟨S,hS⟩,hl,hr⟩ := hh
  rw [hcenter] at hl hr
  exact ⟨⟨S,mem_inter.mpr ⟨(mem_inter.mp hS).1,hdom (mem_inter.mp hS).2⟩⟩,
    by linarith,by linarith⟩

lemma not_interior_ball {C δ : ℝ} (hC : 1 ≤ C) (hδ : 0 ≤ δ)
    (A B : Record n) (hw : B.shell.width ≤ δ) : ¬A.Interior H X C δ B := by
  rintro ⟨_,hl,hr⟩
  unfold RadialShell.width at hw
  have := mul_le_mul_of_nonneg_right hC hδ
  nlinarith

end Record

lemma labeled_empty (q : ℝ) : H.LabeledArrangement G X q ∅ := by simp [LabeledArrangement]

lemma labeled_subset {q : ℝ} {Z W : Finset (Record n)}
    (hZ : H.LabeledArrangement G X q Z) (hW : W ⊆ Z) :
    H.LabeledArrangement G X q W :=
  ⟨fun B hB => hZ.1 B (hW hB),fun _ hB _ hD hne => hZ.2 (hW hB) (hW hD) hne⟩

lemma labeled_pair {q : ℝ} {Z : Finset (Record n)}
    (hZ : H.LabeledArrangement G X q Z) {B D : Record n}
    (hB : B ∈ Z) (hD : D ∈ Z) (hne : B ≠ D) : B.Compatible H X D := by
  by_cases hh : Disjoint (B.shell.support X) (D.shell.support X)
  · exact Or.inl hh
  · exact Or.inr (hZ.2 hB hD hne hh)

lemma labeled_union {q : ℝ} {Z W : Finset (Record n)}
    (hZ : H.LabeledArrangement G X q Z) (hW : H.LabeledArrangement G X q W)
    (hZW : ∀B ∈ Z, ∀D ∈ W, B.Compatible H X D) :
    H.LabeledArrangement G X q (Z∪W) := by
  constructor
  · intro B hB
    exact (mem_union.mp hB).elim (hZ.1 B) (hW.1 B)
  · intro B hB D hD hne hgeo
    rcases mem_union.mp hB with hB | hB <;> rcases mem_union.mp hD with hD | hD
    · exact hZ.2 hB hD hne hgeo
    · exact (hZW B hB D hD).resolve_left hgeo
    · exact (Record.compatible_symm H X (hZW D hD B hB)).resolve_left hgeo
    · exact hW.2 hB hD hne hgeo

lemma labeled_sets_disjoint (hX : ∀v, binary (X v)) {q : ℝ} {Z W : Finset (Record n)}
    (hZ : H.LabeledArrangement G X q Z)
    (hZW : ∀B ∈ Z, ∀D ∈ W, B.Compatible H X D) : Disjoint Z W := by
  rw [Finset.disjoint_left]
  intro B hB hBW
  exact B.compatible_self_iff H X hX (hZ.1 B hB).1 (hZ.1 B hB).2.2.1 (hZW B hB B hBW)

end
end StrongThinTree.MultiGraph.Hierarchy

namespace StrongThinTree.MultiGraph.Hierarchy
noncomputable section
open Finset StrongThinTree.Geometry
variable {n m h : ℕ} (H : Hierarchy n) (G : MultiGraph n m)
  (X : Fin n → Fin h → ℝ)

namespace Record

def restriction (B : Record n) (a b : ℝ) : Record n :=
  {B with shell := RadialShell.hollow B.shell.center a b}

def Refines (D B : Record n) : Prop :=
  D.shell.support X ⊆ B.shell.support X ∧ D.conflict H ⊆ B.conflict H

lemma restriction_refines (B : Record n) {a b : ℝ}
    (ha : B.shell.inner ≤ a) (hb : b ≤ B.shell.outer) :
    (B.restriction a b).Refines H X B :=
  ⟨RadialShell.restriction_subset X B.shell ha hb,Subset.refl _⟩

lemma compatible_refinements {A B C D : Record n}
    (hBD : B.Compatible H X D) (hAB : A.Refines H X B) (hCD : C.Refines H X D) :
    A.Compatible H X C := by
  have hh := compatible_heredity H X hBD hAB.1 hAB.2
  have hh' := compatible_heredity H X (compatible_symm H X hh) hCD.1 hCD.2
  exact compatible_symm H X hh'

end Record

lemma labeled_replace {q : ℝ} {Z W : Finset (Record n)}
    (hZ : H.LabeledArrangement G X q Z) (hW : H.LabeledArrangement G X q W)
    (B : Record n) (hcompat : ∀D ∈ Z.erase B, ∀A ∈ W, D.Compatible H X A) :
    H.LabeledArrangement G X q (Z.erase B∪W) :=
  H.labeled_union G X (H.labeled_subset G X hZ (erase_subset _ _)) hW hcompat

lemma replacement_credit (hX : ∀v, binary (X v)) {q : ℝ} {Z W : Finset (Record n)}
    (hZ : H.LabeledArrangement G X q Z) {B : Record n} (hB : B ∈ Z)
    (hcompat : ∀D ∈ Z.erase B, ∀A ∈ W, D.Compatible H X A)
    (p : Record n → ℝ) {c : ℝ} (hcredit : p B+c ≤ ∑A ∈ W, p A) :
    (∑D ∈ Z, p D)+c ≤ ∑D ∈ Z.erase B∪W, p D := by
  have hdis := H.labeled_sets_disjoint G X hX
    (H.labeled_subset G X hZ (erase_subset B Z)) hcompat
  rw [sum_union hdis]
  have hh := sum_erase_add Z p hB
  linarith

end
end StrongThinTree.MultiGraph.Hierarchy

end

end OAI
