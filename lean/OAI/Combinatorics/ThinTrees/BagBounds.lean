import OAI.Combinatorics.ThinTrees.Assignment

namespace OAI

section
open scoped Classical
open Matrix

namespace StrongThinTree.MultiGraph.Hierarchy
noncomputable section
open Finset StrongThinTree.Geometry
variable {n m h : ℕ} {H : Hierarchy n} {G : MultiGraph n m}
  {X : Fin n → Fin h → ℝ} {δ η : ℝ}

namespace AssignedBag

lemma neighbor_exists (A : H.AssignedBag G X δ η) {u : Fin n} (hu : u ∈ A.centers) :
    ∃v ∈ H.parent A.owner\A.owner, l1dist (X u) (X v) < δ ∧
      ∃e : Fin m, (G.left e = u ∧ G.right e = v) ∨
        (G.left e = v ∧ G.right e = u) := by
  obtain ⟨huT,e,he,heu,hlen⟩ := A.endpoint u hu
  obtain ⟨heP,heT⟩ := mem_filter.mp he
  obtain ⟨hlP,hrP⟩ := (G.mem_inducedEdges _ _).mp heP
  rcases heu with heu | heu
  · have hrT : G.right e ∉ A.owner := by
      rcases heT with hh | hh
      · exact hh.2
      · exact (hh.2 (heu.symm ▸ huT)).elim
    refine ⟨G.right e,mem_sdiff.mpr ⟨hrP,hrT⟩,?_,e,Or.inl ⟨heu,rfl⟩⟩
    simpa only [heu] using hlen
  · have hlT : G.left e ∉ A.owner := by
      rcases heT with hh | hh
      · exact (hh.2 (heu.symm ▸ huT)).elim
      · exact hh.2
    refine ⟨G.left e,mem_sdiff.mpr ⟨hlP,hlT⟩,?_,e,Or.inr ⟨rfl,heu⟩⟩
    simpa only [heu,l1dist_comm] using hlen

def neighbor (A : H.AssignedBag G X δ η) (u : Fin n) : Fin n :=
  if hu : u ∈ A.centers then (A.neighbor_exists hu).choose else u

lemma neighbor_spec (A : H.AssignedBag G X δ η) {u : Fin n} (hu : u ∈ A.centers) :
    A.neighbor u ∈ H.parent A.owner\A.owner ∧
      l1dist (X u) (X (A.neighbor u)) < δ ∧
      ∃e : Fin m, (G.left e = u ∧ G.right e = A.neighbor u) ∨
        (G.left e = A.neighbor u ∧ G.right e = u) := by
  simpa only [neighbor,dite_eq_left hu] using (A.neighbor_exists hu).choose_spec

lemma input_injective (A : H.AssignedBag G X δ η) (P : Finset (Finset (Fin n))) :
    Function.Injective (A.input P) := by
  intro u v hh
  exact congrArg (fun B : Record n => B.shell.center) hh

lemma input_arrangement (A : H.AssignedBag G X δ η) {q : ℝ}
    {P : Finset (Finset (Fin n))} {U : Finset (Fin n)} (hU : U ⊆ A.centers)
    (hvalid : ∀u ∈ U, (A.input P u).Valid H G X q) :
    H.LabeledArrangement G X q (U.image (A.input P)) := by
  constructor
  · intro B hB
    obtain ⟨u,hu,rfl⟩ := mem_image.mp hB
    exact hvalid u hu
  · intro B hB D hD hne hgeo
    obtain ⟨u,hu,rfl⟩ := mem_image.mp hB
    obtain ⟨v,hv,rfl⟩ := mem_image.mp hD
    exact (hgeo (A.disjoint (hU hu) (hU hv) (fun hh => hne (congrArg (A.input P) hh)))).elim

end AssignedBag

namespace Record

lemma unique_interior (_hX : ∀v, binary (X v)) {q : ℝ}
    {Z : Finset (Record n)} (hZ : H.LabeledArrangement G X q Z)
    {A B D : Record n} (hA : A.Shape H) (hB : B ∈ Z) (hD : D ∈ Z)
    (horder : ∀E ∈ Z, E.owner ⊂ A.owner → E.owner ∈ A.excluded)
    (hAB : (A.conflict H ∩ B.conflict H).Nonempty)
    (hAD : (A.conflict H ∩ D.conflict H).Nonempty)
    (hsub : A.shell.support X ⊆ D.shell.support X)
    (hmeet : ¬Disjoint (A.shell.support X) (B.shell.support X)) : B = D := by
  by_contra hne
  have hba := candidate_ancestor H hA (hZ.1 B hB).1 (horder B hB) hAB
  have hda := candidate_ancestor H hA (hZ.1 D hD).1 (horder D hD) hAD
  rcases H.labeled_pair G X hZ hB hD hne with hh | hh
  · exact hmeet ((hh.symm).mono_left hsub)
  · exact Finset.disjoint_left.mp hh hba hda

lemma strict_owner_of_interior (hX : ∀v, binary (X v))
    {A B : Record n} (hA : A.Shape H) (hB : B.Shape H)
    (hAv : A.shell.Valid X) (hδ : 0 ≤ δ)
    (hball : A.shell = RadialShell.ball A.shell.center δ)
    (horder : B.owner ⊂ A.owner → B.owner ∈ A.excluded)
    (hsep : B.owner = A.owner → Disjoint (A.shell.support X) (B.shell.support X))
    (hinter : A.Interior H X 256 δ B) : A.owner ⊂ B.owner := by
  have hanc := candidate_ancestor H hA hB horder hinter.1
  have hsub := (H.mem_domain.mp hanc).2.1
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨hsub,?_⟩
  intro hh
  obtain ⟨z,hz⟩ := RadialShell.valid_support_nonempty hX hAv
  exact Set.disjoint_left.mp (hsep hh.symm) hz
    (interior_ball_subset H X hδ hball hinter hz)

end Record
end
end StrongThinTree.MultiGraph.Hierarchy

namespace StrongThinTree.MultiGraph.Hierarchy
noncomputable section
open Finset StrongThinTree.Geometry
variable {n m h : ℕ} {H : Hierarchy n} {G : MultiGraph n m}
  {X : Fin n → Fin h → ℝ} {δ η : ℝ}
namespace AssignedBag

lemma large_component (A : H.AssignedBag G X δ η) {q : ℝ}
    (hq : 0 < q) (hconn : H.LocallyConnectedReal G q) (hη : 3072/q ≤ η)
    {U : Finset (Fin n)} (hU : U ⊆ A.centers) (hhalf : A.centers.card ≤ 2*U.card) :
    ∃R : Finset (Fin n), R ⊆ H.parent A.owner\A.owner ∧
      G.EdgeConnectedReal R (q/4) ∧ 768 ≤ (U.filter (fun u => A.neighbor u ∈ R)).card := by
  obtain ⟨J,hJ,hJc,hcount⟩ := G.outside_connected_partition hq
    (hconn (H.parent A.owner) (H.parent_mem A.owner A.owner_mem A.nonroot))
    (H.nonempty A.owner A.owner_mem) (H.parent_strict A.owner A.owner_mem A.nonroot)
  have hJn : J.Nonempty := by
    have hout : (H.parent A.owner\A.owner).Nonempty :=
      sdiff_nonempty.mpr (H.parent_strict A.owner A.owner_mem A.nonroot).not_subset
    rw [← hJ.2.2] at hout
    obtain ⟨R,hR,_⟩ := biUnion_nonempty.mp hout
    exact ⟨R,hR⟩
  have hcover : ∀u ∈ U, ∃R ∈ J, A.neighbor u ∈ R := by
    intro u hu
    have hh := (A.neighbor_spec (hU hu)).1
    rw [← hJ.2.2] at hh
    simpa only [mem_biUnion,id_eq] using hh
  have hb := H.parent_boundary_lower G hconn A.owner_mem A.nonroot
  have hηq : 3072 ≤ η*q := (div_le_iff₀ hq).mp hη
  have hsum := mul_le_mul_of_nonneg_right A.assignment hq.le
  have hmass := mul_le_mul_of_nonneg_right hηq
    (Nat.cast_nonneg (H.parentBoundary G A.owner).card : (0:ℝ) ≤ _)
  have hhalf' : (A.centers.card : ℝ) ≤ 2*(U.card : ℝ) := by exact_mod_cast hhalf
  have hmul := mul_le_mul_of_nonneg_left hhalf' hq.le
  obtain ⟨R,hR,hlarge⟩ := AssignedSelection.large_neighbor_class U J
    (fun u R => A.neighbor u ∈ R) hJn hcover hq (lt_of_lt_of_le hq hb)
    (by simpa [mul_comm,Hierarchy.parentBoundary] using hcount)
    (by nlinarith)
  exact ⟨R,(hJ.1 R hR).2,hJc R hR,hlarge⟩

lemma selected_interior (A : H.AssignedBag G X δ η) (hX : ∀v, binary (X v))
    {q : ℝ} {P : Finset (Finset (Fin n))} {U : Finset (Fin n)}
    {Z : Finset (Record n)} (hZ : H.LabeledArrangement G X q Z)
    (hshape : ∀u ∈ U, (A.input P u).Shape H)
    (horder : ∀D ∈ Z, D.owner ⊂ A.owner → D.owner ∈ P)
    (hinter : ∀u ∈ U, ∃D ∈ Z, (A.input P u).Interior H X 256 δ D)
    {B : Record n} (hB : B ∈ Z) {u₀ : Fin n}
    (hint₀ : (A.input P u₀).Interior H X 256 δ B)
    {a b : ℝ} (ha : B.shell.inner ≤ a) (hb : b ≤ B.shell.outer)
    {u : Fin n} (hu : u ∈ U)
    (hr : a-δ < l1dist (X u) (X B.shell.center) ∧
      l1dist (X u) (X B.shell.center) < b+δ) :
    (A.input P u).Interior H X 256 δ B := by
  obtain ⟨D,hD,hintD⟩ := hinter u hu
  have hconf : ((A.input P u).conflict H ∩ B.conflict H).Nonempty := hint₀.1
  have hmeet : ¬Disjoint ((A.input P u).shell.support X) (B.shell.support X) :=
    RadialShell.ball_meets_radial hX (hZ.1 B hB).2.2.1 u A.radius_pos
      (by linarith [hr.1]) (by linarith [hr.2])
  have heq : B = D := Record.unique_interior hX hZ (hshape u hu) hB hD
    (fun E hE hsub => by simpa [input,Record.excluded] using horder E hE hsub)
    hconf hintD.1 (Record.interior_ball_subset H X A.radius_pos.le rfl hintD) hmeet
  exact heq.symm ▸ hintD

end AssignedBag
end
end StrongThinTree.MultiGraph.Hierarchy

namespace StrongThinTree.MultiGraph.Hierarchy
noncomputable section
open Finset StrongThinTree.Geometry
variable {n m h : ℕ} {H : Hierarchy n} {G : MultiGraph n m}
  {X : Fin n → Fin h → ℝ} {δ η : ℝ}
namespace AssignedBag

lemma radial_group (A : H.AssignedBag G X δ η) (hX : ∀v, binary (X v))
    {q : ℝ} {P : Finset (Finset (Fin n))} {U : Finset (Fin n)}
    (hU : U ⊆ A.centers) {Z : Finset (Record n)}
    (hZ : H.LabeledArrangement G X q Z)
    (hshape : ∀u ∈ U, (A.input P u).Shape H)
    (horder : ∀D ∈ Z, D.owner ⊂ A.owner → D.owner ∈ P)
    (hinter : ∀u ∈ U, ∃D ∈ Z, (A.input P u).Interior H X 256 δ D)
    (hno : ∀u ∈ U, ∀D ∈ Z, (A.input P u).Interior H X 256 δ D → D.avoided = none)
    {R : Finset (Fin n)} (hlarge : 768 ≤ (U.filter (fun u => A.neighbor u ∈ R)).card) :
    ∃(B : Record n) (a b : ℝ) (M : Finset (Fin n)) (u₁ u₂ : Fin n),
      B ∈ Z ∧ B.avoided = none ∧ B.shell.inner ≤ a ∧ b ≤ B.shell.outer ∧ a ≤ b ∧
      M.Nonempty ∧ M = U.filter (fun u => a-δ < l1dist (X u) (X B.shell.center) ∧
        l1dist (X u) (X B.shell.center) < b+δ) ∧
      (∀u ∈ M, (A.input P u).Interior H X 256 δ B) ∧
      (768 ≤ M.card ∨ 255*δ ≤ b-a) ∧
      u₁ ∈ U ∧ u₂ ∈ U ∧ A.neighbor u₁ ∈ R ∧ A.neighbor u₂ ∈ R ∧
      l1dist (X (A.neighbor u₁)) (X B.shell.center) ≤ a ∧
      b ≤ l1dist (X (A.neighbor u₂)) (X B.shell.center) ∧
      l1dist (X u₁) (X B.shell.center) ≤ a+δ ∧
      b-δ ≤ l1dist (X u₂) (X B.shell.center) := by
  let K := U.filter (fun u => A.neighbor u ∈ R)
  have hKn : K.Nonempty := card_pos.mp (lt_of_lt_of_le (by norm_num : 0<768) hlarge)
  obtain ⟨u₀,hu₀⟩ := hKn
  obtain ⟨B,hB,hint₀⟩ := hinter u₀ (mem_filter.mp hu₀).1
  let ρ := fun u => l1dist (X u) (X B.shell.center)
  obtain ⟨u₁,hu₁,hmin⟩ := K.exists_min_image (fun u => ρ (A.neighbor u)) ⟨u₀,hu₀⟩
  obtain ⟨u₂,hu₂,hmax⟩ := K.exists_max_image (fun u => ρ (A.neighbor u)) ⟨u₀,hu₀⟩
  let a := max B.shell.inner (ρ (A.neighbor u₁))
  let b := min B.shell.outer (ρ (A.neighbor u₂))
  let M := U.filter (fun u => a-δ < ρ u ∧ ρ u < b+δ)
  have hnear (u : Fin n) (hu : u ∈ U) : |ρ u - ρ (A.neighbor u)| < δ :=
    (l1dist_reverse _ _ _).trans_lt (A.neighbor_spec (hU hu)).2.1
  have hr₀ := AssignedSelection.interior_neighbor_in_range A.radius_pos (hmin u₀ hu₀) (hmax u₀ hu₀)
    hint₀.2.1 hint₀.2.2 (hnear u₀ (mem_filter.mp hu₀).1)
  have hMn : M.Nonempty := ⟨u₀,mem_filter.mpr ⟨(mem_filter.mp hu₀).1,hr₀.2⟩⟩
  have hMinter : ∀u ∈ M, (A.input P u).Interior H X 256 δ B := by
    intro u hu
    obtain ⟨hu,hr⟩ := mem_filter.mp hu
    exact A.selected_interior hX hZ hshape horder hinter hB hint₀
      (le_max_left _ _) (min_le_left _ _) hu hr
  have hdich : 768 ≤ M.card ∨ 255*δ ≤ b-a := by
    by_cases hs : K ⊆ M
    · exact Or.inl (hlarge.trans (card_le_card hs))
    · obtain ⟨u,hu,huM⟩ := Finset.not_subset.mp hs
      have hr : ¬(a-δ < ρ u ∧ ρ u < b+δ) :=
        fun hh => huM (mem_filter.mpr ⟨(mem_filter.mp hu).1,hh⟩)
      exact Or.inr (AssignedSelection.radial_range A.radius_pos (hmin u₀ hu₀) (hmax u₀ hu₀)
        hint₀.2.1 hint₀.2.2 (hnear u₀ (mem_filter.mp hu₀).1)
        (hmin u hu) (hmax u hu) (hnear u (mem_filter.mp hu).1) hr)
  have hnear₁ := (abs_lt.mp (hnear u₁ (mem_filter.mp hu₁).1)).2
  have hnear₂ := (abs_lt.mp (hnear u₂ (mem_filter.mp hu₂).1)).1
  refine ⟨B,a,b,M,u₁,u₂,hB,hno u₀ (mem_filter.mp hu₀).1 B hB hint₀,
    le_max_left _ _,min_le_left _ _,hr₀.1,hMn,rfl,hMinter,hdich,
    (mem_filter.mp hu₁).1,(mem_filter.mp hu₂).1,(mem_filter.mp hu₁).2,(mem_filter.mp hu₂).2,
    le_max_right _ _,min_le_right _ _,?_,?_⟩
  · change ρ u₁ ≤ a+δ
    have hh : ρ (A.neighbor u₁) ≤ a := le_max_right _ _
    linarith
  · change b-δ ≤ ρ u₂
    have hh : b ≤ ρ (A.neighbor u₂) := min_le_right _ _
    linarith

end AssignedBag
end
end StrongThinTree.MultiGraph.Hierarchy

namespace StrongThinTree.MultiGraph.Hierarchy
noncomputable section
open Finset StrongThinTree.Geometry
variable {n m h : ℕ} {H : Hierarchy n} {G : MultiGraph n m}
  {X : Fin n → Fin h → ℝ}

namespace Record

def RadialRefines (D B : Record n) : Prop :=
  D.shell.center = B.shell.center ∧ B.shell.inner ≤ D.shell.inner ∧
    D.shell.outer ≤ B.shell.outer ∧ D.conflict H ⊆ B.conflict H

lemma radialRefines_refl (B : Record n) : B.RadialRefines (H := H) B :=
  ⟨rfl,le_refl _,le_refl _,Subset.refl _⟩

lemma restriction_radialRefines (B : Record n) {a b : ℝ}
    (ha : B.shell.inner ≤ a) (hb : b ≤ B.shell.outer) :
    (B.restriction a b).RadialRefines (H := H) B := ⟨rfl,ha,hb,Subset.refl _⟩

lemma central_radialRefines {B : Record n} (hB : B.Shape H) (hno : B.avoided = none)
    {t : Finset (Fin n)} (ht : t ∈ B.conflict H) {a b c d : ℝ}
    (ha : B.shell.inner ≤ a) (hb : b ≤ B.shell.outer)
    (hc : B.shell.inner ≤ c) (hd : d ≤ B.shell.outer) :
    (B.innerRecord t a b).RadialRefines (H := H) B ∧
      (B.outsideRecord t c d).RadialRefines (H := H) B := by
  obtain ⟨h1,h2⟩ := central_conflict H hB hno ht a b c d
  refine ⟨⟨rfl,ha,hb,?_⟩,⟨rfl,hc,hd,?_⟩⟩
  · rw [h1]; exact filter_subset _ _
  · rw [h2]; exact filter_subset _ _

def InteriorTo (δ : ℝ) (Z : Finset (Record n)) (A : Record n) : Prop :=
  ∃B ∈ Z, A.Interior H X 256 δ B

end Record

def Evolution (F Z Z' : Finset (Record n)) : Prop :=
  ∀D ∈ Z', D ∈ F ∨ ∃B ∈ Z, D.RadialRefines (H := H) B

def OwnerEvolution (t : Finset (Fin n)) (Z Z' : Finset (Record n)) : Prop :=
  ∀D ∈ Z', D.owner = t ∨ ∃B ∈ Z, D.owner = B.owner

lemma evolution_interior {δ : ℝ} (hδ : 0 ≤ δ)
    {F Z Z' : Finset (Record n)} (hF : ∀D ∈ F, D.shell.width = δ)
    (hevol : Evolution (H := H) F Z Z') {A : Record n}
    (hh : A.InteriorTo (H := H) (X := X) δ Z') : A.InteriorTo (H := H) (X := X) δ Z := by
  obtain ⟨D,hD,hint⟩ := hh
  rcases hevol D hD with hD | ⟨B,hB,href⟩
  · exact (Record.not_interior_ball H X (by norm_num : (1:ℝ) ≤ 256) hδ A D
      (hF D hD).le hint).elim
  · exact ⟨B,hB,Record.interior_restriction H X href.1 href.2.1 href.2.2.1 href.2.2.2 hint⟩

lemma ownerEvolution_order {t : Finset (Fin n)} {P : Finset (Finset (Fin n))}
    {Z Z' : Finset (Record n)} (hold : ∀B ∈ Z, B.owner ⊂ t → B.owner ∈ P)
    (hevol : OwnerEvolution t Z Z') : ∀B ∈ Z', B.owner ⊂ t → B.owner ∈ P := by
  intro B hB hs
  rcases hevol B hB with hh | ⟨D,hD,hh⟩
  · exact (hs.ne hh).elim
  · rw [hh] at hs ⊢
    exact hold D hD hs

namespace AssignedBag
variable {δ η : ℝ} (A : H.AssignedBag G X δ η)

def SameOwnerSeparated (P : Finset (Finset (Fin n))) (U : Finset (Fin n))
    (Z : Finset (Record n)) : Prop :=
  ∀u ∈ U, (A.input P u).InteriorTo (H := H) (X := X) δ Z →
    ∀B ∈ Z, B.owner = A.owner →
      Disjoint ((RadialShell.ball u δ).support X) (B.shell.support X)

lemma metadata_evolution {F Z Z' Q : Finset (Record n)}
    (hQ : ∀D ∈ Q, D ∈ F ∨ ∃B ∈ Z, D.RadialRefines (H := H) B)
    (hmeta : ∀D ∈ Z', D ∈ Z ∨ D ∈ Q ∨ ∃B ∈ Z, ∃a b,
      D = B.restriction a b ∧ B.shell.inner ≤ a ∧ b ≤ B.shell.outer) :
    Evolution (H := H) F Z Z' := by
  intro D hD
  rcases hmeta D hD with hD | hD | ⟨B,hB,a,b,rfl,ha,hb⟩
  · exact Or.inr ⟨D,hD,D.radialRefines_refl⟩
  · exact hQ D hD
  · exact Or.inr ⟨B,hB,B.restriction_radialRefines ha hb⟩

lemma metadata_owners {Z Z' Q : Finset (Record n)}
    (hQ : ∀D ∈ Q, D.owner = A.owner ∨ ∃B ∈ Z, D.owner = B.owner)
    (hmeta : ∀D ∈ Z', D ∈ Z ∨ D ∈ Q ∨ ∃B ∈ Z, ∃a b,
      D = B.restriction a b ∧ B.shell.inner ≤ a ∧ b ≤ B.shell.outer) :
    OwnerEvolution A.owner Z Z' := by
  intro D hD
  rcases hmeta D hD with hD | hD | ⟨B,hB,a,b,rfl,_⟩
  · exact Or.inr ⟨D,hD,rfl⟩
  · exact hQ D hD
  · exact Or.inr ⟨B,hB,rfl⟩

lemma metadata_separation {P : Finset (Finset (Fin n))} {U V : Finset (Fin n)}
    (hVU : V ⊆ U) {Z Z' Q F : Finset (Record n)}
    (hF : ∀D ∈ F, D.shell.width = δ) (hevol : Evolution (H := H) F Z Z')
    (hsep : A.SameOwnerSeparated P U Z)
    (hQ : ∀D ∈ Q, D.owner = A.owner → ∀u ∈ V,
      (A.input P u).InteriorTo (H := H) (X := X) δ Z →
      Disjoint ((RadialShell.ball u δ).support X) (D.shell.support X))
    (hmeta : ∀D ∈ Z', D ∈ Z ∨ D ∈ Q ∨ ∃B ∈ Z, ∃a b,
      D = B.restriction a b ∧ B.shell.inner ≤ a ∧ b ≤ B.shell.outer) :
    A.SameOwnerSeparated P V Z' := by
  intro u hu hint D hD hown
  have hintold := evolution_interior A.radius_pos.le hF hevol hint
  rcases hmeta D hD with hD | hD | ⟨B,hB,a,b,rfl,ha,hb⟩
  · exact hsep u (hVU hu) hintold D hD hown
  · exact hQ D hD hown u hu hintold
  · exact (hsep u (hVU hu) hintold B hB hown).mono_right
      (RadialShell.restriction_subset X B.shell ha hb)

end AssignedBag
end
end StrongThinTree.MultiGraph.Hierarchy

namespace StrongThinTree.MultiGraph.Hierarchy
noncomputable section
open Finset StrongThinTree.Geometry
variable {n m h : ℕ} {H : Hierarchy n} {G : MultiGraph n m}
  {X : Fin n → Fin h → ℝ} {δ η : ℝ}
namespace AssignedBag

lemma metadata_fresh (A : H.AssignedBag G X δ η) {P : Finset (Finset (Fin n))}
    {F Z Z' Q : Finset (Record n)} {M : Finset (Fin n)}
    (hF : ∀D ∈ F, D.shell.ordinary = true)
    (hQ : ∀D ∈ Q, D ∈ F → ∃u ∈ M, D = A.input P u)
    (hmeta : ∀D ∈ Z', D ∈ Z ∨ D ∈ Q ∨ ∃B ∈ Z, ∃a b,
      D = B.restriction a b ∧ B.shell.inner ≤ a ∧ b ≤ B.shell.outer) :
    ∀D ∈ Z', D ∈ F → D ∈ Z ∨ ∃u ∈ M, D = A.input P u := by
  intro D hD hDF
  rcases hmeta D hD with hD | hD | ⟨B,hB,a,b,rfl,_⟩
  · exact Or.inl hD
  · exact Or.inr (hQ D hD hDF)
  · exact (Record.restriction_not_fresh hF B a b hDF).elim

structure InteriorMove (A : H.AssignedBag G X δ η)
    (q ε : ℝ) (P : Finset (Finset (Fin n)))
    (F Z : Finset (Record n)) (U : Finset (Fin n)) where
  treated : Finset (Fin n)
  next : Finset (Record n)
  nonempty : treated.Nonempty
  treated_interior : ∀u ∈ treated, u ∈ U ∧
    (A.input P u).InteriorTo (H := H) (X := X) δ Z
  valid : H.LabeledArrangement G X (q/4) next
  credit : (∑D ∈ Z, Record.phaseToken F δ ε D)+
      AssignedAccounting.theta*(treated.card : ℝ)*δ ≤
      ∑D ∈ next, Record.phaseToken F δ ε D
  evolution : Evolution (H := H) F Z next
  owners : OwnerEvolution A.owner Z next
  fresh : ∀D ∈ next, D ∈ F → D ∈ Z ∨ ∃u ∈ treated, D = A.input P u
  separation : A.SameOwnerSeparated P (U\treated) next

lemma avoiding_move (A : H.AssignedBag G X δ η) (hX : ∀v, binary (X v))
    {q ε : ℝ} (hε : ε ≤ δ/1536) {P : Finset (Finset (Fin n))}
    {F Z : Finset (Record n)} {U : Finset (Fin n)} (hU : U ⊆ A.centers)
    (hF : ∀D ∈ F, D.shell.ordinary = true ∧ D.shell.width = δ ∧ D.avoided = none)
    (hAF : ∀u ∈ A.centers, A.input P u ∈ F)
    (hvalid : ∀u ∈ A.centers, (A.input P u).Valid H G X (q/4))
    (hZ : H.LabeledArrangement G X (q/4) Z)
    (horder : ∀D ∈ Z, D.owner ⊂ A.owner → D.owner ∈ P)
    (hsep : A.SameOwnerSeparated P U Z)
    {u : Fin n} (hu : u ∈ U) {B : Record n} (hB : B ∈ Z)
    (havoid : B.avoided.isSome = true) (hinter : (A.input P u).Interior H X 256 δ B) :
    Nonempty (InteriorMove A q ε P F Z U) := by
  obtain ⟨Z',hZ',hcredit,hmeta₀⟩ := H.avoiding_operation G X hX A.radius_pos hε
    (fun D hD => ⟨(hF D hD).1,(hF D hD).2.2⟩) hZ (hvalid u (hU hu))
    (hAF u (hU hu)) rfl hB havoid
    (fun D hD hs => by simpa [input,Record.excluded] using horder D hD hs) hinter
  let Q : Finset (Record n) := {A.input P u}
  have hmeta : ∀D ∈ Z', D ∈ Z ∨ D ∈ Q ∨ ∃E ∈ Z, ∃a b,
      D = E.restriction a b ∧ E.shell.inner ≤ a ∧ b ≤ E.shell.outer := by
    intro D hD
    rcases hmeta₀ D hD with hD | rfl | ⟨a,b,heq,ha,hb,_⟩
    · exact Or.inl hD
    · exact Or.inr (Or.inl (mem_singleton_self _))
    · exact Or.inr (Or.inr ⟨B,hB,a,b,heq,ha,hb⟩)
  have hevol : Evolution (H := H) F Z Z' := metadata_evolution
    (fun D hD => Or.inl ((mem_singleton.mp hD).symm ▸ hAF u (hU hu))) hmeta
  have howner : OwnerEvolution A.owner Z Z' := A.metadata_owners
    (fun D hD => Or.inl (by rw [mem_singleton.mp hD]; rfl)) hmeta
  have hfresh := A.metadata_fresh (fun D hD => (hF D hD).1)
    (M := {u}) (by
      intro D hD _
      exact ⟨u,mem_singleton_self _,mem_singleton.mp hD⟩) hmeta
  have hsep' : A.SameOwnerSeparated P (U\{u}) Z' := by
    apply A.metadata_separation sdiff_subset (fun D hD => (hF D hD).2.1) hevol hsep _ hmeta
    intro D hD _ v hv _
    rw [mem_singleton.mp hD]
    obtain ⟨hv,hvu⟩ := mem_sdiff.mp hv
    exact A.disjoint (hU hv) (hU hu) (by simpa only [mem_singleton] using hvu)
  refine ⟨⟨{u},Z',singleton_nonempty _,?_,hZ',?_,hevol,howner,hfresh,hsep'⟩⟩
  · intro v hv
    rw [mem_singleton.mp hv]
    exact ⟨hu,⟨B,hB,hinter⟩⟩
  · simpa only [card_singleton,Nat.cast_one,mul_one] using hcredit

end AssignedBag
end
end StrongThinTree.MultiGraph.Hierarchy

end

end OAI
