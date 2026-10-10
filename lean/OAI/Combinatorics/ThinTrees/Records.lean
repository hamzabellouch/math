import OAI.Combinatorics.ThinTrees.Hierarchy

namespace OAI

section
open scoped Classical
open Matrix

namespace StrongThinTree.MultiGraph.Hierarchy
noncomputable section
open Finset StrongThinTree.Geometry
variable {n h : ℕ} (H : Hierarchy n)

def domain (A : Finset (Fin n)) (P : Finset (Finset (Fin n))) : Finset (Finset (Fin n)) :=
  H.nodes.filter (fun B => B ⊆ A ∧ ∀S ∈ P, ¬B ⊆ S)

def leaves (_H : Hierarchy n) (A : Finset (Fin n)) (P : Finset (Finset (Fin n))) : Finset (Fin n) :=
  A\P.biUnion id

lemma mem_domain {A B : Finset (Fin n)} {P : Finset (Finset (Fin n))} :
    B ∈ H.domain A P ↔ B ∈ H.nodes ∧ B ⊆ A ∧ ∀S ∈ P, ¬B ⊆ S := by
  simp [domain]

lemma mem_leaves {A : Finset (Fin n)} {P : Finset (Finset (Fin n))} {v : Fin n} :
    v ∈ H.leaves A P ↔ v ∈ A ∧ ∀S ∈ P, v ∉ S := by
  simp [leaves]

lemma root_mem_domain {A : Finset (Fin n)} {P : Finset (Finset (Fin n))}
    (hA : A ∈ H.nodes) (hP : ∀S ∈ P, S ⊂ A) : A ∈ H.domain A P := by
  apply H.mem_domain.mpr
  refine ⟨hA,Subset.refl _,?_⟩
  intro S hS hh
  have hs := hP S hS
  exact (Finset.ssubset_iff_subset_ne.mp hs).2 (Subset.antisymm hs.subset hh)

lemma singleton_domain_iff {A : Finset (Fin n)} {P : Finset (Finset (Fin n))} {v : Fin n} :
    {v} ∈ H.domain A P ↔ v ∈ H.leaves A P := by
  simp only [mem_domain,H.singletons,true_and,singleton_subset_iff,mem_leaves]

lemma domain_root_test {A B : Finset (Fin n)} {P Q : Finset (Finset (Fin n))}
    (hA : A ∈ H.nodes) (hB : B ∈ H.nodes)
    (hP : ∀S ∈ P, S ⊂ A) (hQ : ∀S ∈ Q, S ⊂ B) :
    (H.domain A P ∩ H.domain B Q).Nonempty ↔
      A ∈ H.domain B Q ∨ B ∈ H.domain A P := by
  constructor
  · rintro ⟨C,hC⟩
    obtain ⟨hCA,hCB⟩ := mem_inter.mp hC
    obtain ⟨hCnode,hCA,hCP⟩ := H.mem_domain.mp hCA
    obtain ⟨_,hCB,hCQ⟩ := H.mem_domain.mp hCB
    rcases H.laminar A hA B hB with hAB | hBA | hdis
    · left
      apply H.mem_domain.mpr
      exact ⟨hA,hAB,fun S hS hh => hCQ S hS (hCA.trans hh)⟩
    · right
      apply H.mem_domain.mpr
      exact ⟨hB,hBA,fun S hS hh => hCP S hS (hCB.trans hh)⟩
    · obtain ⟨v,hv⟩ := H.nonempty C hCnode
      exact (Finset.disjoint_left.mp hdis (hCA hv) (hCB hv)).elim
  · rintro (hAB | hBA)
    · exact ⟨A,mem_inter.mpr ⟨H.root_mem_domain hA hP,hAB⟩⟩
    · exact ⟨B,mem_inter.mpr ⟨hBA,H.root_mem_domain hB hQ⟩⟩

end
end StrongThinTree.MultiGraph.Hierarchy

namespace StrongThinTree.MultiGraph.Hierarchy
noncomputable section
open Finset StrongThinTree.Geometry

structure Record (n : ℕ) where
  shell : RadialShell (Fin n)
  owner : Finset (Fin n)
  predecessors : Finset (Finset (Fin n))
  avoided : Option (Finset (Fin n))
  deriving DecidableEq

namespace Record
variable {n m h : ℕ} (H : Hierarchy n) (G : MultiGraph n m)
  (X : Fin n → Fin h → ℝ)

def excluded (B : Record n) : Finset (Finset (Fin n)) :=
  B.predecessors ∪ B.avoided.toFinset

def conflict (B : Record n) := H.domain B.owner B.excluded
def leafSet (B : Record n) := H.leaves B.owner B.excluded
def routing (B : Record n) : Finset (Fin n) := B.owner\B.avoided.getD ∅

def Shape (B : Record n) : Prop :=
  B.owner ∈ H.nodes ∧ (∀S ∈ B.excluded, S ∈ H.nodes ∧ S ⊂ B.owner)

def Protected (B : Record n) : Prop :=
  ∀S ∈ B.predecessors, ∀e ∈ G.cut univ S,
    B.shell.outer ≤ l1dist (X (G.left e)) (X B.shell.center) ∧
    B.shell.outer ≤ l1dist (X (G.right e)) (X B.shell.center)

def RoutingCertificate (q : ℝ) (B : Record n) : Prop :=
  ∃R : Finset (Fin n), R ⊆ B.routing ∧ G.EdgeConnectedReal R q ∧
    (∃u ∈ R, u ∈ B.leafSet H ∧ l1dist (X u) (X B.shell.center) ≤ B.shell.inner) ∧
    (∃v ∈ R, B.shell.outer ≤ l1dist (X v) (X B.shell.center))

def Valid (q : ℝ) (B : Record n) : Prop :=
  B.Shape H ∧ B.Protected G X ∧ B.shell.Valid X ∧ B.RoutingCertificate H G X q

lemma root_mem {B : Record n} (hB : B.Shape H) : B.owner ∈ B.conflict H :=
  H.root_mem_domain hB.1 (fun S hS => (hB.2 S hS).2)

lemma mem_leafSet {B : Record n} {v : Fin n} :
    v ∈ B.leafSet H ↔ v ∈ B.owner ∧ ∀S ∈ B.excluded, v ∉ S := H.mem_leaves

lemma mem_routing {B : Record n} {v : Fin n} :
    v ∈ B.routing ↔ v ∈ B.owner ∧ ∀S ∈ B.avoided.toFinset, v ∉ S := by
  cases heq : B.avoided <;> simp [routing,heq]

lemma protected_routing_edges {B : Record n} (hB : B.Protected G X)
    {R : Finset (Fin n)} (hR : R ⊆ B.routing) :
    ∀e ∈ G.inducedEdges R,
      ((G.left e ∈ B.leafSet H ∧ G.right e ∉ B.leafSet H) ∨
       (G.right e ∈ B.leafSet H ∧ G.left e ∉ B.leafSet H)) →
      B.shell.outer ≤ l1dist (X (G.left e)) (X B.shell.center) ∧
      B.shell.outer ≤ l1dist (X (G.right e)) (X B.shell.center) := by
  have hex {u v : Fin n} (hu : u ∈ B.leafSet H) (hv : v ∈ B.routing)
      (hn : v ∉ B.leafSet H) : ∃S ∈ B.predecessors, u ∉ S ∧ v ∈ S := by
    obtain ⟨hu,hup⟩ := (mem_leafSet H).mp hu
    obtain ⟨hv,hva⟩ := mem_routing.mp hv
    have : ∃S ∈ B.excluded, v ∈ S := by
      by_contra hh
      push Not at hh
      exact hn ((mem_leafSet H).mpr ⟨hv,hh⟩)
    obtain ⟨S,hS,hvS⟩ := this
    have hSp : S ∈ B.predecessors := by
      rcases mem_union.mp hS with hh | hh
      · exact hh
      · exact (hva S hh hvS).elim
    exact ⟨S,hSp,hup S hS,hvS⟩
  intro e he hcross
  obtain ⟨hlR,hrR⟩ := (G.mem_inducedEdges _ _).mp he
  rcases hcross with hcross | hcross
  · obtain ⟨S,hS,hl,hr⟩ := hex hcross.1 (hR hrR) hcross.2
    exact hB S hS e (mem_filter.mpr ⟨mem_univ _,Or.inr ⟨hr,hl⟩⟩)
  · obtain ⟨S,hS,hr,hl⟩ := hex hcross.1 (hR hlR) hcross.2
    exact hB S hS e (mem_filter.mpr ⟨mem_univ _,Or.inl ⟨hl,hr⟩⟩)

lemma variation_lower {q : ℝ} {B : Record n} (hB : B.Valid H G X q) :
    q*B.shell.width ≤ ∑e ∈ G.inducedEdges (B.leafSet H),
      |clamp B.shell.inner B.shell.outer (l1dist (X (G.left e)) (X B.shell.center))-
       clamp B.shell.inner B.shell.outer (l1dist (X (G.right e)) (X B.shell.center))| := by
  obtain ⟨R,hR,hconn,hu,hv⟩ := hB.2.2.2
  exact G.routed_variation_lower _ hB.2.2.1.2.1.le hconn hu hv
    (protected_routing_edges H G X hB.2.1 hR)

lemma restrict_valid {q a b : ℝ} {B : Record n} (hB : B.Valid H G X q)
    (ha : B.shell.inner ≤ a) (hb : b ≤ B.shell.outer) (hab : a < b) :
    ({B with shell := RadialShell.hollow B.shell.center a b}).Valid H G X q := by
  refine ⟨hB.1,?_,?_,?_⟩
  · intro S hS e he
    exact ⟨hb.trans (hB.2.1 S hS e he).1,hb.trans (hB.2.1 S hS e he).2⟩
  · obtain ⟨u,hu⟩ := hB.2.2.1.2.2.2.1
    obtain ⟨v,hv⟩ := hB.2.2.1.2.2.2.2
    exact ⟨hB.2.2.1.1.trans ha,hab,by simp [RadialShell.hollow],⟨u,hu.trans ha⟩,⟨v,hb.trans hv⟩⟩
  · obtain ⟨R,hR,hconn,⟨u,huR,huL,hu⟩,⟨v,hvR,hv⟩⟩ := hB.2.2.2
    exact ⟨R,hR,hconn,⟨u,huR,huL,hu.trans ha⟩,⟨v,hvR,hb.trans hv⟩⟩

end Record
end
end StrongThinTree.MultiGraph.Hierarchy

namespace StrongThinTree.MultiGraph.Hierarchy
noncomputable section
open Finset StrongThinTree.Geometry
variable {n m h : ℕ} (H : Hierarchy n) (G : MultiGraph n m)
  (X : Fin n → Fin h → ℝ)

def LabeledArrangement (q : ℝ) (Z : Finset (Record n)) : Prop :=
  (∀B ∈ Z, B.Valid H G X q) ∧
  (Z : Set (Record n)).Pairwise (fun B D =>
    ¬Disjoint (B.shell.support X) (D.shell.support X) →
      Disjoint (B.conflict H) (D.conflict H))

lemma labeled_energy {q : ℝ} (hX : ∀v, binary (X v)) {Z : Finset (Record n)}
    (hZ : H.LabeledArrangement G X q Z) :
    q*(∑B ∈ Z, B.shell.width) ≤ ∑e : Fin m, l1dist (X (G.left e)) (X (G.right e)) := by
  let f (B : Record n) (e : Fin m) :=
    |clamp B.shell.inner B.shell.outer (l1dist (X (G.left e)) (X B.shell.center))-
     clamp B.shell.inner B.shell.outer (l1dist (X (G.right e)) (X B.shell.center))|
  calc
    _ = ∑B ∈ Z, q*B.shell.width := mul_sum _ _ _
    _ ≤ ∑B ∈ Z, ∑e ∈ G.inducedEdges (B.leafSet H), f B e :=
      sum_le_sum (fun B hB => B.variation_lower H G X (hZ.1 B hB))
    _ = ∑e : Fin m, ∑B ∈ Z.filter (fun B => e ∈ G.inducedEdges (B.leafSet H)), f B e := by
      simp only [inducedEdges,sum_filter,mem_filter,mem_univ,true_and]
      rw [sum_comm]
    _ ≤ _ := by
      apply sum_le_sum
      intro e he
      let W := Z.filter (fun B => e ∈ G.inducedEdges (B.leafSet H))
      rw [← Finset.sum_coe_sort]
      apply binary_shell_edge_bound (binary_cube (hX _)) (binary_cube (hX _))
        (fun B : W => X B.val.shell.center) (fun B => hX _) _ _
      · intro B
        exact (hZ.1 B.val (mem_filter.mp B.property).1).2.2.1.2.1.le
      · intro B D hBD w hw hbad
        have hB : B.val ∈ Z := (mem_filter.mp B.property).1
        have hD : D.val ∈ Z := (mem_filter.mp D.property).1
        have hinter : ¬Disjoint (B.val.shell.support X) (D.val.shell.support X) := by
          intro hh
          exact Set.disjoint_left.mp hh ⟨hw,hbad.2.1,Or.inr hbad.1⟩
            ⟨hw,hbad.2.2.2,Or.inr hbad.2.2.1⟩
        have hdis := hZ.2 hB hD (fun hh => hBD (Subtype.ext hh)) hinter
        have hlB := ((G.mem_inducedEdges _ _).mp (mem_filter.mp B.property).2).1
        have hlD := ((G.mem_inducedEdges _ _).mp (mem_filter.mp D.property).2).1
        have hmB : {G.left e} ∈ B.val.conflict H := H.singleton_domain_iff.mpr hlB
        have hmD : {G.left e} ∈ D.val.conflict H := H.singleton_domain_iff.mpr hlD
        exact Finset.disjoint_left.mp hdis hmB hmD

end
end StrongThinTree.MultiGraph.Hierarchy

namespace StrongThinTree.MultiGraph.Hierarchy
noncomputable section
open Finset StrongThinTree.Geometry
variable {n m h : ℕ} (H : Hierarchy n) (G : MultiGraph n m)
  (X : Fin n → Fin h → ℝ)

def parentBoundary (A : Finset (Fin n)) : Finset (Fin m) :=
  G.cut (G.inducedEdges (H.parent A)) A

def LocallyConnectedReal (q : ℝ) : Prop := ∀A ∈ H.nodes, G.EdgeConnectedReal A q

lemma parent_boundary_lower {q : ℝ} (hconn : H.LocallyConnectedReal G q)
    {A : Finset (Fin n)} (hA : A ∈ H.nodes) (hne : A ≠ univ) :
    q ≤ (H.parentBoundary G A).card :=
  hconn (H.parent A) (H.parent_mem A hA hne) A (H.nonempty A hA)
    (H.parent_strict A hA hne)

structure AssignedBag (δ η : ℝ) where
  owner : Finset (Fin n)
  owner_mem : owner ∈ H.nodes
  nonroot : owner ≠ univ
  centers : Finset (Fin n)
  nonempty : centers.Nonempty
  radius_pos : 0 < δ
  disjoint : (centers : Set (Fin n)).Pairwise (fun u v =>
    Disjoint ((RadialShell.ball u δ).support X) ((RadialShell.ball v δ).support X))
  assignment : η*(H.parentBoundary G owner).card ≤ (centers.card : ℝ)
  endpoint : ∀u ∈ centers, u ∈ owner ∧ ∃e ∈ H.parentBoundary G owner,
    (G.left e = u ∨ G.right e = u) ∧ l1dist (X (G.left e)) (X (G.right e)) < δ

namespace AssignedBag
variable {H G X} {δ η : ℝ} (A : H.AssignedBag G X δ η)

def input (P : Finset (Finset (Fin n))) (u : Fin n) : Record n :=
  ⟨RadialShell.ball u δ,A.owner,P,none⟩

lemma input_leaf {P : Finset (Finset (Fin n))} (hP : ∀S ∈ P, S ⊂ A.owner)
    {u : Fin n} (hu : u ∈ A.centers) (hins : (A.input P u).Protected G X) :
    u ∈ (A.input P u).leafSet H := by
  apply (Record.mem_leafSet H).mpr
  refine ⟨(A.endpoint u hu).1,?_⟩
  intro S hS huS
  have hSP : S ∈ P := by simpa [Record.excluded,input] using hS
  obtain ⟨e,he,heu,hlen⟩ := (A.endpoint u hu).2
  have he' := (mem_filter.mp he).2
  have hcut : e ∈ G.cut univ S := by
    apply mem_filter.mpr
    refine ⟨mem_univ _,?_⟩
    rcases he' with hh | hh
    · have hright : G.right e ∉ S := fun hs => hh.2 ((hP S hSP).subset hs)
      rcases heu with heu | heu
      · exact Or.inl ⟨heu.symm ▸ huS,hright⟩
      · exact (hright (heu.symm ▸ huS)).elim
    · have hleft : G.left e ∉ S := fun hs => hh.2 ((hP S hSP).subset hs)
      rcases heu with heu | heu
      · exact (hleft (heu.symm ▸ huS)).elim
      · exact Or.inr ⟨heu.symm ▸ huS,hleft⟩
  have hp := hins S hSP e hcut
  rcases heu with heu | heu
  · have hp := hp.1
    change δ ≤ l1dist (X (G.left e)) (X u) at hp
    rw [heu,l1dist_self] at hp
    linarith [A.radius_pos]
  · have hp := hp.2
    change δ ≤ l1dist (X (G.right e)) (X u) at hp
    rw [heu,l1dist_self] at hp
    linarith [A.radius_pos]

lemma input_valid (hX : ∀v, binary (X v)) {q : ℝ} (_hq : 0 ≤ q)
    (hconn : H.LocallyConnectedReal G q) (hsize : 1 < A.centers.card)
    {P : Finset (Finset (Fin n))} (hP : ∀S ∈ P, S ∈ H.nodes ∧ S ⊂ A.owner)
    {u : Fin n} (hu : u ∈ A.centers) (hins : (A.input P u).Protected G X) :
    (A.input P u).Valid H G X (q/4) := by
  obtain ⟨v,hv,hvu⟩ := Finset.exists_mem_ne hsize u
  have hdist := RadialShell.disjoint_balls_distance hX u v (A.disjoint hu hv hvu.symm)
  have houter : δ ≤ l1dist (X v) (X u) := by
    rw [l1dist_comm]
    linarith [A.radius_pos]
  refine ⟨?_,hins,?_,?_⟩
  · refine ⟨A.owner_mem,?_⟩
    intro S hS
    exact hP S (by simpa [input,Record.excluded] using hS)
  · exact ⟨le_refl 0,A.radius_pos,by simp [input,RadialShell.ball],
      ⟨u,by simp [input,RadialShell.ball,l1dist_self]⟩,⟨v,houter⟩⟩
  · refine ⟨A.owner,?_,?_,⟨u,(A.endpoint u hu).1,A.input_leaf (fun S hS => (hP S hS).2) hu hins,?_⟩,
      ⟨v,(A.endpoint v hv).1,houter⟩⟩
    · simp [input,Record.routing]
    · intro S hS hSA
      have hh := hconn A.owner A.owner_mem S hS hSA
      linarith
    · simp [input,RadialShell.ball,l1dist_self]

end AssignedBag
end
end StrongThinTree.MultiGraph.Hierarchy

end

end OAI
