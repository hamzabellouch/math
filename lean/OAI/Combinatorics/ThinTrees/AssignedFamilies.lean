import OAI.Combinatorics.ThinTrees.Phases

namespace OAI

section
open scoped Classical
open Matrix

namespace StrongThinTree.MultiGraph.Hierarchy
noncomputable section
open Finset StrongThinTree.Geometry
variable {n m h : ℕ} {H : Hierarchy n} {G : MultiGraph n m}
  {X : Fin n → Fin h → ℝ} {η : ℝ}

structure AssignedFamily (H : Hierarchy n) (G : MultiGraph n m)
    (X : Fin n → Fin h → ℝ) (η : ℝ) where
  radius : ℝ
  positive : 0 < radius
  count : ℕ
  bag : Fin count → H.AssignedBag G X radius η
  owner_injective : Function.Injective (fun i => (bag i).owner)
  separated : ∀i, ∀u ∈ (bag i).centers, ∀j, ∀v ∈ (bag j).centers,
    (i ≠ j ∨ u ≠ v) → Disjoint ((RadialShell.ball u radius).support X)
      ((RadialShell.ball v radius).support X)

namespace AssignedFamily
variable (F : AssignedFamily H G X η)

def owners : Finset (Finset (Fin n)) := univ.image (fun i => (F.bag i).owner)
def mass : ℝ := (∑i, ((F.bag i).centers.card : ℝ))*F.radius
def predecessors (E : Finset (Finset (Fin n))) (i : Fin F.count) : Finset (Finset (Fin n)) :=
  E.filter (fun S => S ⊂ (F.bag i).owner)

def ProtectedFrom (E : Finset (Finset (Fin n))) : Prop :=
  ∀i, ∀u ∈ (F.bag i).centers, ((F.bag i).input (F.predecessors E i) u).Protected G X

lemma owner_mem (i : Fin F.count) : (F.bag i).owner ∈ F.owners := mem_image.mpr ⟨i,mem_univ _,rfl⟩
lemma owners_nodes : F.owners ⊆ H.nodes := by
  intro S hS
  obtain ⟨i,hi,rfl⟩ := mem_image.mp hS
  exact (F.bag i).owner_mem

lemma input_valid {q : ℝ} (hX : ∀v, binary (X v)) (hq : 0 < q)
    (hconn : H.LocallyConnectedReal G q) (hη : 3072/q ≤ η)
    {E : Finset (Finset (Fin n))} (hE : E ⊆ H.nodes) (hprot : F.ProtectedFrom E)
    (i : Fin F.count) {u : Fin n} (hu : u ∈ (F.bag i).centers) :
    ((F.bag i).input (F.predecessors E i) u).Valid H G X (q/4) := by
  have hbound := H.parent_boundary_lower G hconn (F.bag i).owner_mem (F.bag i).nonroot
  have hassign := (F.bag i).assignment
  have hc : (3072:ℝ) ≤ ((F.bag i).centers.card : ℝ) := by
    have ha := mul_le_mul_of_nonneg_right hη (Nat.cast_nonneg (H.parentBoundary G (F.bag i).owner).card)
    have hb := mul_le_mul_of_nonneg_left hbound (show 0 ≤ (3072:ℝ)/q by positivity)
    have heq : (3072:ℝ)/q*q = 3072 := by field_simp
    rw [heq] at hb
    linarith
  apply (F.bag i).input_valid hX hq.le hconn
    (by exact_mod_cast (show (1:ℝ) < ((F.bag i).centers.card : ℝ) by linarith))
    (fun S hS => ⟨hE (mem_filter.mp hS).1,(mem_filter.mp hS).2⟩) hu (hprot i u hu)

lemma phase {q ε : ℝ} (hX : ∀v, binary (X v)) (hq : 0 < q)
    (hconn : H.LocallyConnectedReal G q) (hη : 3072/q ≤ η)
    (hε : 0 ≤ ε) (hscale : ε ≤ F.radius/1536)
    {E : Finset (Finset (Fin n))} (hE : E ⊆ H.nodes) (hprot : F.ProtectedFrom E)
    (hdis : Disjoint E F.owners)
    (Z : Finset (Record n)) (hZ : H.LabeledArrangement G X (q/4) Z)
    (hown : ∀D ∈ Z, D.owner ∈ E) :
    ∃Z' : Finset (Record n), H.LabeledArrangement G X (q/4) Z' ∧
      (∑D ∈ Z, D.baseToken F.radius)+(AssignedAccounting.theta/2)*F.mass ≤
        ∑D ∈ Z', D.baseToken ε ∧ (∀D ∈ Z', D.owner ∈ E∪F.owners) := by
  obtain ⟨Z',hZ',hc,ho⟩ := assigned_phase F.bag (F.predecessors E) hX hq hconn hη
    F.positive hε hscale univ F.owner_injective.injOn
    (fun i _ u hu => F.input_valid hX hq hconn hη hE hprot i hu)
    (by
      intro i hi u hu j hj v hv hne
      apply F.separated i u hu j v hv
      by_cases hh : i = j
      · right
        intro he
        subst j; subst v
        exact hne rfl
      · exact Or.inl hh)
    Z hZ
    (fun i _ D hD hs => mem_filter.mpr ⟨hown D hD,hs⟩)
    (fun i _ D hD heq => Finset.disjoint_left.mp hdis (hown D hD) (heq ▸ F.owner_mem i))
  refine ⟨Z',hZ',?_,?_⟩
  · simpa only [mass,mul_assoc] using hc
  · intro D hD
    rcases ho D hD with ⟨i,hi,heq⟩ | ⟨B,hB,heq⟩
    · exact mem_union_right _ (heq ▸ F.owner_mem i)
    · exact mem_union_left _ (heq ▸ hown B hB)

end AssignedFamily

namespace AssignedSequence
abbrev Family := AssignedFamily H G X η

def initialRadius : List (Family (H := H) (G := G) (X := X) (η := η)) → ℝ
  | [] => 0
  | F::_ => F.radius

def mass : List (Family (H := H) (G := G) (X := X) (η := η)) → ℝ
  | [] => 0
  | F::L => F.mass+mass L

def Geometric : List (Family (H := H) (G := G) (X := X) (η := η)) → Prop
  | [] => True
  | F::L => initialRadius L ≤ F.radius/1536 ∧ Geometric L

def Ready (E : Finset (Finset (Fin n))) : List (Family (H := H) (G := G) (X := X) (η := η)) → Prop
  | [] => True
  | F::L => Disjoint E F.owners ∧ F.ProtectedFrom E ∧ Ready (E∪F.owners) L

lemma radius_nonneg (L : List (Family (H := H) (G := G) (X := X) (η := η))) :
    0 ≤ initialRadius L := by
  cases L with
  | nil => exact le_refl _
  | cons F L => exact F.positive.le

lemma construct {q : ℝ} (hX : ∀v, binary (X v)) (hq : 0 < q)
    (hconn : H.LocallyConnectedReal G q) (hη : 3072/q ≤ η)
    (L : List (Family (H := H) (G := G) (X := X) (η := η)))
    (hgeo : Geometric L) (E : Finset (Finset (Fin n))) (hE : E ⊆ H.nodes)
    (hready : Ready E L) (Z : Finset (Record n)) (hZ : H.LabeledArrangement G X (q/4) Z)
    (hown : ∀D ∈ Z, D.owner ∈ E) {credit : ℝ}
    (hcredit : credit ≤ ∑D ∈ Z, D.baseToken (initialRadius L)) :
    ∃Z' : Finset (Record n), H.LabeledArrangement G X (q/4) Z' ∧
      credit+(AssignedAccounting.theta/2)*mass L ≤ ∑D ∈ Z', D.shell.width := by
  induction L generalizing E Z credit with
  | nil =>
    refine ⟨Z,hZ,?_⟩
    simp only [mass,mul_zero,add_zero] at *
    apply hcredit.trans
    exact sum_le_sum (fun D hD => AssignedAccounting.base_le_width D.avoided.isSome
      (by have hh := (hZ.1 D hD).2.2.1.2.1; dsimp [RadialShell.width]; linarith) (le_refl _))
  | cons F L ih =>
    obtain ⟨Z₁,hZ₁,hstep,hown₁⟩ := F.phase hX hq hconn hη (radius_nonneg L)
      hgeo.1 hE hready.2.1 hready.1 Z hZ hown
    have hc : credit+(AssignedAccounting.theta/2)*F.mass ≤
        ∑D ∈ Z₁, D.baseToken (initialRadius L) := by
      change credit ≤ ∑D ∈ Z, D.baseToken F.radius at hcredit
      linarith
    obtain ⟨Z₂,hZ₂,hc₂⟩ := ih hgeo.2 (E∪F.owners) (union_subset hE F.owners_nodes)
      hready.2.2 Z₁ hZ₁ hown₁ hc
    refine ⟨Z₂,hZ₂,?_⟩
    dsimp [mass]
    linarith

lemma insertable_bound {q : ℝ} (hX : ∀v, binary (X v)) (hq : 0 < q)
    (hconn : H.LocallyConnectedReal G q) (hη : 3072/q ≤ η)
    (L : List (Family (H := H) (G := G) (X := X) (η := η)))
    (hgeo : Geometric L) (hready : Ready ∅ L) :
    (q/4096)*mass L ≤ ∑e : Fin m, l1dist (X (G.left e)) (X (G.right e)) := by
  have hempty : H.LabeledArrangement G X (q/4) ∅ := by constructor <;> simp
  obtain ⟨Z,hZ,hwidth⟩ := construct hX hq hconn hη L hgeo ∅ (empty_subset _) hready
    ∅ hempty (by simp) (credit := 0) (by simp)
  have he := H.labeled_energy G X hX hZ
  have hh := mul_le_mul_of_nonneg_left hwidth (show 0 ≤ q/4 by positivity)
  dsimp [AssignedAccounting.theta] at hh
  nlinarith

end AssignedSequence
end
end StrongThinTree.MultiGraph.Hierarchy

namespace StrongThinTree.MultiGraph.Hierarchy
noncomputable section
open Finset StrongThinTree.Geometry
variable {n m h : ℕ} {H : Hierarchy n} {G : MultiGraph n m}
  {X : Fin n → Fin h → ℝ} {η : ℝ}

namespace AssignedFamily
variable (F : AssignedFamily H G X η)

def goodCenters (E : Finset (Finset (Fin n))) (i : Fin F.count) : Finset (Fin n) :=
  (F.bag i).centers.filter (fun u => ((F.bag i).input (F.predecessors E i) u).Protected G X)

def badCenters (E : Finset (Finset (Fin n))) (i : Fin F.count) : Finset (Fin n) :=
  (F.bag i).centers\F.goodCenters E i

def badCount (E : Finset (Finset (Fin n))) : ℕ := ∑i, (F.badCenters E i).card

def boundaryCount (G : MultiGraph n m) (E : Finset (Finset (Fin n))) : ℕ :=
  ∑S ∈ E, (G.cut univ S).card

lemma bad_witness {E : Finset (Finset (Fin n))} (i : Fin F.count) {u : Fin n}
    (hu : u ∈ F.badCenters E i) :
    ∃S ∈ E, ∃e ∈ G.cut univ S, ∃v : Fin n,
      (v = G.left e ∨ v = G.right e) ∧ l1dist (X v) (X u) < F.radius := by
  have hn : ¬((F.bag i).input (F.predecessors E i) u).Protected G X := by
    intro hh
    exact (mem_sdiff.mp hu).2 (mem_filter.mpr ⟨(mem_sdiff.mp hu).1,hh⟩)
  simp only [Record.Protected,not_forall] at hn
  obtain ⟨S,hS,e,he,hn⟩ := hn
  have hSE : S ∈ E := (mem_filter.mp hS).1
  change ¬(F.radius ≤ l1dist (X (G.left e)) (X u) ∧
    F.radius ≤ l1dist (X (G.right e)) (X u)) at hn
  by_cases hl : l1dist (X (G.left e)) (X u) < F.radius
  · exact ⟨S,hSE,e,he,G.left e,Or.inl rfl,hl⟩
  · exact ⟨S,hSE,e,he,G.right e,Or.inr rfl,lt_of_not_ge (fun hr => hn ⟨le_of_not_gt hl,hr⟩)⟩

lemma badCount_le (hX : ∀v, binary (X v)) (E : Finset (Finset (Fin n))) :
    F.badCount E ≤ 2*boundaryCount G E := by
  let B := univ.sigma (F.badCenters E)
  let W := E.biUnion (fun S => (G.cut univ S).biUnion (fun e => {G.left e,G.right e}))
  have hBW : ∀p ∈ B, ∃v ∈ W, l1dist (X v) (X p.2) < F.radius := by
    intro p hp
    obtain ⟨S,hS,e,he,v,hv,hd⟩ := F.bad_witness p.1 (mem_sigma.mp hp).2
    refine ⟨v,mem_biUnion.mpr ⟨S,hS,mem_biUnion.mpr ⟨e,he,?_⟩⟩,hd⟩
    simp only [mem_insert,mem_singleton]
    exact hv
  choose f hfW hfd using hBW
  have hinj : ∀p hp q hq, f p hp = f q hq → p = q := by
    intro p hp r hr heq
    by_contra hh
    have hne : p.1 ≠ r.1 ∨ p.2 ≠ r.2 := by
      by_contra hn
      push Not at hn
      exact hh (Sigma.ext hn.1 (heq_of_eq hn.2))
    have hd := F.separated p.1 p.2 (mem_sdiff.mp (mem_sigma.mp hp).2).1
      r.1 r.2 (mem_sdiff.mp (mem_sigma.mp hr).2).1 hne
    have ha : X (f p hp) ∈ (RadialShell.ball p.2 F.radius).support X := by
      rw [RadialShell.support_ball]
      exact ⟨binary_cube (hX _),hfd p hp⟩
    have hb : X (f p hp) ∈ (RadialShell.ball r.2 F.radius).support X := by
      rw [RadialShell.support_ball,heq]
      exact ⟨binary_cube (hX _),hfd r hr⟩
    exact Set.disjoint_left.mp hd ha hb
  have hcard : B.card ≤ W.card := by
    apply Finset.card_le_card_of_injective (f := fun p : B => (⟨f p.val p.property,hfW p.val p.property⟩ : W))
    intro p r heq
    exact Subtype.ext (hinj p.val p.property r.val r.property (congrArg Subtype.val heq))
  have hW : W.card ≤ 2*boundaryCount G E := by
    calc
      W.card ≤ ∑S ∈ E, ((G.cut univ S).biUnion (fun e => {G.left e,G.right e})).card := card_biUnion_le
      _ ≤ ∑S ∈ E, ∑e ∈ G.cut univ S, ({G.left e,G.right e} : Finset (Fin n)).card :=
        sum_le_sum (fun S hS => card_biUnion_le)
      _ ≤ ∑S ∈ E, ∑_e ∈ G.cut univ S, 2 :=
        sum_le_sum (fun S hS => sum_le_sum (fun e he => card_le_two))
      _ = _ := by simp [boundaryCount,mul_sum,Nat.mul_comm]
  have heq : B.card = F.badCount E := by simp [B,badCount,Finset.card_sigma]
  rw [heq] at hcard
  exact hcard.trans hW

lemma prune (E : Finset (Finset (Fin n))) {η' : ℝ} (hη : 2*η' ≤ η) :
    ∃F' : AssignedFamily H G X η', F'.radius = F.radius ∧ F'.owners ⊆ F.owners ∧
      (∀E' ⊆ E, F'.ProtectedFrom E') ∧
      F.mass-2*(F.badCount E : ℝ)*F.radius ≤ F'.mass := by
  let J := univ.filter (fun i : Fin F.count => (F.bag i).centers.card ≤ 2*(F.goodCenters E i).card)
  let e : Fin (Fintype.card J) ≃ J := (Fintype.equivFin J).symm
  have hnon : ∀i ∈ J, (F.goodCenters E i).Nonempty := by
    intro i hi
    apply card_pos.mp
    have hn := card_pos.mpr (F.bag i).nonempty
    have hc := (mem_filter.mp hi).2
    omega
  let a (i : J) : H.AssignedBag G X F.radius η' := {
    owner := (F.bag i.val).owner
    owner_mem := (F.bag i.val).owner_mem
    nonroot := (F.bag i.val).nonroot
    centers := F.goodCenters E i.val
    nonempty := hnon i.val i.property
    radius_pos := F.positive
    disjoint := (F.bag i.val).disjoint.mono (filter_subset _ _)
    assignment := by
      have hc : ((F.bag i.val).centers.card : ℝ) ≤ 2*((F.goodCenters E i.val).card : ℝ) := by
        exact_mod_cast (mem_filter.mp i.property).2
      have hh := mul_le_mul_of_nonneg_right hη (Nat.cast_nonneg (H.parentBoundary G (F.bag i.val).owner).card)
      have ha := (F.bag i.val).assignment
      nlinarith
    endpoint := fun u hu => (F.bag i.val).endpoint u (mem_filter.mp hu).1 }
  let F' : AssignedFamily H G X η' := {
    radius := F.radius
    positive := F.positive
    count := Fintype.card J
    bag := fun i => a (e i)
    owner_injective := by
      intro i j hij
      apply e.injective
      apply Subtype.ext
      exact F.owner_injective hij
    separated := by
      intro i u hu j v hv hne
      apply F.separated (e i).val u (mem_filter.mp hu).1 (e j).val v (mem_filter.mp hv).1
      rcases hne with hne | hne
      · left
        intro hh
        exact hne (e.injective (Subtype.ext hh))
      · exact Or.inr hne }
  have hsum : ∑i : Fin F'.count, ((F'.bag i).centers.card : ℝ) =
      ∑i ∈ J, ((F.goodCenters E i).card : ℝ) := by
    change (∑i : Fin (Fintype.card J), ((F.goodCenters E (e i).val).card : ℝ)) = _
    rw [e.sum_comp (fun i : J => ((F.goodCenters E i.val).card : ℝ))]
    exact Finset.sum_coe_sort J (fun i : Fin F.count => ((F.goodCenters E i).card : ℝ))
  have hgood : ∀i, ((F.bag i).centers.card : ℝ) ≤
      (if i ∈ J then ((F.goodCenters E i).card : ℝ) else 0)+2*((F.badCenters E i).card : ℝ) := by
    intro i
    have hc : ((F.badCenters E i).card : ℝ)+((F.goodCenters E i).card : ℝ) =
        ((F.bag i).centers.card : ℝ) := by
      exact_mod_cast card_sdiff_add_card_eq_card (filter_subset (fun u =>
        ((F.bag i).input (F.predecessors E i) u).Protected G X) (F.bag i).centers)
    by_cases hi : i ∈ J
    · rw [ite_eq_left hi]
      nlinarith [show (0:ℝ) ≤ (F.badCenters E i).card from Nat.cast_nonneg _]
    · rw [ite_eq_right hi]
      have hh : 2*(F.goodCenters E i).card < (F.bag i).centers.card := by
        simpa only [J,mem_filter,mem_univ,true_and,not_le] using hi
      have hh' : 2*((F.goodCenters E i).card : ℝ) < ((F.bag i).centers.card : ℝ) := by exact_mod_cast hh
      linarith
  have hcount := Finset.sum_le_sum (s := univ) (fun i _ => hgood i)
  have hcounts : (∑i, ((F.bag i).centers.card : ℝ))-2*(F.badCount E : ℝ) ≤
      ∑i ∈ J, ((F.goodCenters E i).card : ℝ) := by
    rw [sum_add_distrib,←mul_sum] at hcount
    have heq : (∑i, if i ∈ J then ((F.goodCenters E i).card : ℝ) else 0) =
        ∑i ∈ J, ((F.goodCenters E i).card : ℝ) := by simp
    rw [heq] at hcount
    apply sub_le_iff_le_add.mpr
    simpa only [badCount,Nat.cast_sum] using hcount
  refine ⟨F',rfl,?_,?_,?_⟩
  · intro S hS
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hS
    exact F.owner_mem (e i).val
  · intro E' hE' i u hu S hS edge hedge
    have hp := (mem_filter.mp hu).2
    exact hp S (mem_filter.mpr ⟨hE' (mem_filter.mp hS).1,(mem_filter.mp hS).2⟩) edge hedge
  · dsimp [mass]
    rw [hsum]
    nlinarith [mul_le_mul_of_nonneg_right hcounts F.positive.le]

end AssignedFamily
end
end StrongThinTree.MultiGraph.Hierarchy

end

end OAI
