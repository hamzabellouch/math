import OAI.Combinatorics.ThinTrees.AssignedFamilies

namespace OAI

section
open scoped Classical
open Matrix

namespace StrongThinTree.MultiGraph.Hierarchy
noncomputable section
open Finset StrongThinTree.Geometry
variable {n m h : ℕ} {H : Hierarchy n} {G : MultiGraph n m}
  {X : Fin n → Fin h → ℝ}

namespace AssignedFamily
variable {q : ℝ} (F : AssignedFamily H G X (6144/q))

def BoundaryRatio (ρ : ℝ) : Prop := ∀i,
  (q*ρ)*((G.cut univ (F.bag i).owner).card : ℝ) ≤ (H.parentBoundary G (F.bag i).owner).card

lemma boundary_mass {ρ : ℝ} (hq : 0 < q) (hR : F.BoundaryRatio ρ) :
    6144*ρ*(boundaryCount G F.owners : ℝ)*F.radius ≤ F.mass := by
  have he : (boundaryCount G F.owners : ℝ) =
      ∑i, ((G.cut univ (F.bag i).owner).card : ℝ) := by
    simp only [boundaryCount,owners,Nat.cast_sum]
    exact sum_image F.owner_injective.injOn
  have hi : ∀i, (6144*ρ)*((G.cut univ (F.bag i).owner).card : ℝ) ≤ ((F.bag i).centers.card : ℝ) := by
    intro i
    have hh := mul_le_mul_of_nonneg_left (hR i) (show 0 ≤ (6144:ℝ)/q by positivity)
    have hx : (6144:ℝ)/q*((q*ρ)*((G.cut univ (F.bag i).owner).card : ℝ)) =
        (6144*ρ)*((G.cut univ (F.bag i).owner).card : ℝ)  := by field_simp
    rw [hx] at hh
    exact hh.trans (F.bag i).assignment
  rw [he]
  dsimp [mass]
  apply mul_le_mul_of_nonneg_right _ F.positive.le
  rw [mul_sum]
  exact sum_le_sum (fun i _ => hi i)
end AssignedFamily

namespace AssignedSequence
open AssignedFamily
variable {q : ℝ}

def Fresh (E : Finset (Finset (Fin n))) : List (AssignedFamily H G X (6144/q)) → Prop
  | [] => True
  | F::L => Disjoint E F.owners ∧ Fresh (E∪F.owners) L

def Ratios (ρ : ℝ) : List (AssignedFamily H G X (6144/q)) → Prop
  | [] => True
  | F::L => F.BoundaryRatio ρ ∧ Ratios ρ L

def GeometricAt {η : ℝ} (ρ : ℝ) : List (AssignedFamily H G X η) → Prop
  | [] => True
  | F::L => initialRadius L ≤ ρ*F.radius ∧ GeometricAt ρ L

lemma geometric_of {η ρ : ℝ} (hρ : ρ ≤ 1/1536)
    (L : List (AssignedFamily H G X η)) (hL : GeometricAt ρ L) : Geometric L := by
  induction L with
  | nil => trivial
  | cons F L ih =>
    refine ⟨?_,ih hL.2⟩
    have hh := mul_le_mul_of_nonneg_right hρ F.positive.le
    linarith [hL.1]

lemma prune_sequence (hX : ∀v, binary (X v)) (hq : 0 < q)
    {ρ : ℝ} (hρ : 0 < ρ) (hρsmall : ρ ≤ 1/1536)
    (L : List (AssignedFamily H G X (6144/q)))
    (hgeo : GeometricAt ρ L) (hR : Ratios ρ L)
    (E E' : Finset (Finset (Fin n))) (hE : E ⊆ H.nodes) (hE' : E' ⊆ E)
    (hfresh : Fresh E L) :
    ∃L' : List (AssignedFamily H G X (3072/q)), initialRadius L' = initialRadius L ∧
      GeometricAt ρ L' ∧ Ready E' L' ∧
      mass L/2-8*(initialRadius L)*(boundaryCount G E : ℝ) ≤ mass L' := by
  induction L generalizing E E' with
  | nil => exact ⟨[],rfl,True.intro,True.intro,by simp [mass,initialRadius]⟩
  | cons F L ih =>
    obtain ⟨F',hrad,howners,hprot,hgain⟩ := F.prune E (η' := 3072/q) (by field_simp; ring_nf; rfl)
    have hE₁ : E∪F.owners ⊆ H.nodes := union_subset hE F.owners_nodes
    obtain ⟨L',headEq,hgeo',hready',hgain'⟩ := ih hgeo.2 hR.2
      (E∪F.owners) (E'∪F'.owners) hE₁ (union_subset_union hE' howners) hfresh.2
    have hdis : Disjoint E' F'.owners := hfresh.1.mono hE' howners
    have hBC : (boundaryCount G (E∪F.owners) : ℝ) =
        (boundaryCount G E : ℝ)+(boundaryCount G F.owners : ℝ) := by
      simp only [boundaryCount,sum_union hfresh.1,Nat.cast_add]
    have hb := F.badCount_le hX E
    have hb' : (F.badCount E : ℝ) ≤ 2*(boundaryCount G E : ℝ) := by exact_mod_cast hb
    have hpf : F.mass-4*F.radius*(boundaryCount G E : ℝ) ≤ F'.mass := by
      have hh := mul_le_mul_of_nonneg_right hb' F.positive.le
      nlinarith
    have hr := F.boundary_mass hq hR.1
    have heps := radius_nonneg L
    have hsc := hgeo.1
    have hsmall := mul_le_mul_of_nonneg_right hρsmall F.positive.le
    have hcoal : 4*F.radius+8*initialRadius L ≤ 8*F.radius := by linarith
    have hB0 : (0:ℝ) ≤ boundaryCount G E := Nat.cast_nonneg _
    have hBF0 : (0:ℝ) ≤ boundaryCount G F.owners := Nat.cast_nonneg _
    have hc := mul_le_mul_of_nonneg_right hsc hBF0
    have hcost : 8*initialRadius L*(boundaryCount G F.owners : ℝ) ≤ F.mass/2 := by
      have hpos : 0 ≤ ρ*F.radius*(boundaryCount G F.owners : ℝ) :=
        mul_nonneg (mul_nonneg hρ.le F.positive.le) hBF0
      nlinarith
    have hprev := mul_le_mul_of_nonneg_right hcoal hB0
    refine ⟨F'::L',hrad,⟨?_,hgeo'⟩,⟨hdis,hprot E' hE',hready'⟩,?_⟩
    · simpa only [headEq,hrad] using hsc
    · rw [hBC] at hgain'
      dsimp [mass,initialRadius]
      nlinarith

lemma assigned_bound (hX : ∀v, binary (X v)) {q : ℝ} (hq : 0 < q)
    (hconn : H.LocallyConnectedReal G q)
    {ρ : ℝ} (hρ : 0 < ρ) (hρsmall : ρ ≤ 1/1536)
    (L : List (AssignedFamily H G X (6144/q)))
    (hgeo : GeometricAt ρ L) (hR : Ratios ρ L) (hfresh : Fresh ∅ L) :
    (q/8192)*mass L ≤ ∑e : Fin m, l1dist (X (G.left e)) (X (G.right e)) := by
  obtain ⟨L',hrad,hgeo',hready',hmass⟩ := prune_sequence hX hq hρ hρsmall L hgeo hR ∅ ∅
    (empty_subset _) (Subset.refl _) hfresh
  have hcharge := insertable_bound hX hq hconn (le_refl (3072/q)) L' (geometric_of hρsmall L' hgeo') hready'
  have hmass' : mass L/2 ≤ mass L' := by simpa [boundaryCount] using hmass
  have hh := mul_le_mul_of_nonneg_left hmass' (show 0 ≤ q/4096 by positivity)
  nlinarith

end AssignedSequence
end
end StrongThinTree.MultiGraph.Hierarchy

namespace StrongThinTree.MultiGraph.Hierarchy
noncomputable section
open Finset StrongThinTree.Geometry StrongThinTree.Geometry.RadialShell
open scoped Classical
variable {n m h : ℕ} {H : Hierarchy n} {G : MultiGraph n m}
  {X : Fin n → Fin h → ℝ}

lemma assigned_from_net (T : Finset (Finset (Fin n))) (W : Finset (Fin n))
    (hW : W.Nonempty) (hT : T ⊆ H.nodes) (hroot : ∀t ∈ T, t ≠ univ)
    (hboundary : ∀t ∈ T, 0 < (H.parentBoundary G t).card)
    {D η : ℝ} (hD : 0 < D)
    (hsep : (W : Set (Fin n)).Pairwise (fun u v =>
      Disjoint ((ball u D).support X) ((ball v D).support X)))
    (hcenter : ∀u ∈ W, ∃t ∈ T, u ∈ t ∧ ∃e ∈ H.parentBoundary G t,
      (G.left e = u ∨ G.right e = u) ∧ l1dist (X (G.left e)) (X (G.right e)) < D)
    (hη : η ≤ (W.card : ℝ)/(2*(∑t ∈ T, ((H.parentBoundary G t).card : ℝ)))) :
    ∃F : AssignedFamily H G X η, F.radius = D ∧ F.owners ⊆ T ∧
      D*(W.card : ℝ)/2 ≤ F.mass := by
  obtain ⟨u0,hu0⟩ := hW
  obtain ⟨t0,ht0,ht0c⟩ := hcenter u0 hu0
  have hex : ∀u : Fin n, ∃t ∈ T, u ∈ W → u ∈ t ∧ ∃e ∈ H.parentBoundary G t,
      (G.left e = u ∨ G.right e = u) ∧ l1dist (X (G.left e)) (X (G.right e)) < D := by
    intro u
    by_cases hu : u ∈ W
    · obtain ⟨t,ht,hc⟩ := hcenter u hu
      exact ⟨t,ht,fun _ => hc⟩
    · exact ⟨t0,ht0,fun hh => (hu hh).elim⟩
  choose f hfT hf using hex
  let N : ℝ := ∑t ∈ T, ((H.parentBoundary G t).card : ℝ)
  have hN : 0 < N := sum_pos (fun t ht => by exact_mod_cast hboundary t ht) ⟨t0,ht0⟩
  have hW0 : (0:ℝ) < W.card := by exact_mod_cast card_pos.mpr ⟨u0,hu0⟩
  let c : ℝ := W.card/(2*N)
  have hc : 0 < c := div_pos hW0 (mul_pos (by norm_num) hN)
  obtain ⟨J,hJT,hJ,hgain⟩ := retain_fibers W T f (fun u _ => hfT u)
    (fun t => ((H.parentBoundary G t).card : ℝ))
    (fun t ht => by exact_mod_cast hboundary t ht) hc
  let fiber := fun t => W.filter (fun u => f u=t)
  let e : Fin (Fintype.card J) ≃ J := (Fintype.equivFin J).symm
  let a (t : J) : H.AssignedBag G X D η := {
    owner := t.val
    owner_mem := hT (hJT t.property)
    nonroot := hroot t.val (hJT t.property)
    centers := fiber t.val
    nonempty := (hJ t.val t.property).1
    radius_pos := hD
    disjoint := hsep.mono (filter_subset _ _)
    assignment := (mul_le_mul_of_nonneg_right hη (Nat.cast_nonneg _)).trans (hJ t.val t.property).2
    endpoint := by
      intro u hu
      obtain ⟨hu,hfu⟩ := mem_filter.mp hu
      simpa only [hfu] using hf u hu }
  let F : AssignedFamily H G X η := {
    radius := D
    positive := hD
    count := Fintype.card J
    bag := fun i => a (e i)
    owner_injective := by
      intro i j hij
      exact e.injective (Subtype.ext hij)
    separated := by
      intro i u hu j v hv hne
      apply hsep (mem_filter.mp hu).1 (mem_filter.mp hv).1
      intro huv
      subst v
      have hh : (e i).val = (e j).val :=
        (mem_filter.mp hu).2.symm.trans (mem_filter.mp hv).2
      rcases hne with hne | hne
      · exact hne (e.injective (Subtype.ext hh))
      · exact hne rfl }
  have hsum : (∑i : Fin F.count, ((F.bag i).centers.card : ℝ)) =
      ∑t ∈ J, ((fiber t).card : ℝ) := by
    change (∑i : Fin (Fintype.card J), ((fiber (e i).val).card : ℝ)) = _
    rw [e.sum_comp (fun t : J => ((fiber t.val).card : ℝ))]
    exact sum_coe_sort J (fun t => ((fiber t).card : ℝ))
  refine ⟨F,rfl,?_,?_⟩
  · intro t ht
    obtain ⟨i,hi,rfl⟩ := mem_image.mp ht
    exact hJT (e i).property
  · have heq : c*N = (W.card : ℝ)/2 := by dsimp [c]; field_simp
    change (W.card : ℝ)-c*N ≤ _ at hgain
    rw [heq] at hgain
    change D*(W.card : ℝ)/2 ≤ (∑i : Fin F.count, ((F.bag i).centers.card : ℝ))*D
    rw [hsum]
    have hh := mul_le_mul_of_nonneg_left hgain hD.le
    nlinarith

end
end StrongThinTree.MultiGraph.Hierarchy

namespace StrongThinTree.MultiGraph.Hierarchy
noncomputable section
open Finset StrongThinTree.Geometry
open scoped Classical
variable {n m : ℕ} (H : Hierarchy n) (G : MultiGraph n m)

lemma boundary_owner_unique {A B : Finset (Fin n)} {u v : Fin n}
    (hA : A ∈ H.nodes) (hB : B ∈ H.nodes) (hAr : A ≠ univ) (hBr : B ≠ univ)
    (huA : u ∈ A) (huB : u ∈ B) (hvA : v ∉ A) (hvB : v ∉ B)
    (hvPA : v ∈ H.parent A) (hvPB : v ∈ H.parent B) : A = B := by
  rcases H.laminar A hA B hB with hAB | hBA | hdis
  · by_contra hne
    have hp := H.parent_minimal A hA hAr B hB (Finset.ssubset_iff_subset_ne.mpr ⟨hAB,hne⟩)
    exact hvB (hp hvPA)
  · by_contra hne
    have hp := H.parent_minimal B hB hBr A hA (Finset.ssubset_iff_subset_ne.mpr ⟨hBA,Ne.symm hne⟩)
    exact hvA (hp hvPB)
  · exact (Finset.disjoint_left.mp hdis huA huB).elim

lemma parentBoundary_multiplicity (T : Finset (Finset (Fin n)))
    (hT : T ⊆ H.nodes) (hroot : ∀t ∈ T, t ≠ univ) (e : Fin m) :
    (T.filter (fun t => e ∈ H.parentBoundary G t)).card ≤ 2 := by
  let S := T.filter (fun t => e ∈ H.parentBoundary G t)
  let L := S.filter (fun t => G.left e ∈ t)
  let R := S.filter (fun t => G.right e ∈ t)
  have hL : L.card ≤ 1 := by
    apply card_le_one.mpr
    intro A hA B hB
    obtain ⟨hA,hlA⟩ := mem_filter.mp hA
    obtain ⟨hB,hlB⟩ := mem_filter.mp hB
    obtain ⟨hAT,heA⟩ := mem_filter.mp hA
    obtain ⟨hBT,heB⟩ := mem_filter.mp hB
    obtain ⟨hePA,hcutA⟩ := mem_filter.mp heA
    obtain ⟨hePB,hcutB⟩ := mem_filter.mp heB
    have hrA : G.right e ∉ A := by rcases hcutA with hh | hh; exact hh.2; exact (hh.2 hlA).elim
    have hrB : G.right e ∉ B := by rcases hcutB with hh | hh; exact hh.2; exact (hh.2 hlB).elim
    exact H.boundary_owner_unique (hT hAT) (hT hBT) (hroot A hAT) (hroot B hBT)
      hlA hlB hrA hrB ((G.mem_inducedEdges _ _).mp hePA).2 ((G.mem_inducedEdges _ _).mp hePB).2
  have hR : R.card ≤ 1 := by
    apply card_le_one.mpr
    intro A hA B hB
    obtain ⟨hA,hrA⟩ := mem_filter.mp hA
    obtain ⟨hB,hrB⟩ := mem_filter.mp hB
    obtain ⟨hAT,heA⟩ := mem_filter.mp hA
    obtain ⟨hBT,heB⟩ := mem_filter.mp hB
    obtain ⟨hePA,hcutA⟩ := mem_filter.mp heA
    obtain ⟨hePB,hcutB⟩ := mem_filter.mp heB
    have hlA : G.left e ∉ A := by rcases hcutA with hh | hh; exact (hh.2 hrA).elim; exact hh.2
    have hlB : G.left e ∉ B := by rcases hcutB with hh | hh; exact (hh.2 hrB).elim; exact hh.2
    exact H.boundary_owner_unique (hT hAT) (hT hBT) (hroot A hAT) (hroot B hBT)
      hrA hrB hlA hlB ((G.mem_inducedEdges _ _).mp hePA).1 ((G.mem_inducedEdges _ _).mp hePB).1
  have hsub : S ⊆ L∪R := by
    intro A hA
    have hc := (mem_filter.mp (mem_filter.mp hA).2).2
    rcases hc with hh | hh
    · exact mem_union_left _ (mem_filter.mpr ⟨hA,hh.1⟩)
    · exact mem_union_right _ (mem_filter.mpr ⟨hA,hh.1⟩)
  exact (card_le_card hsub).trans ((card_union_le _ _).trans (by omega))

lemma subset_boundary_multiplicity (T : Finset (Finset (Fin n)))
    (hT : T ⊆ H.nodes) (hroot : ∀t ∈ T, t ≠ univ)
    (F : Finset (Fin n) → Finset (Fin m)) (hF : ∀t ∈ T, F t ⊆ H.parentBoundary G t) :
    (∑t ∈ T, (F t).card) ≤ 2*(T.biUnion F).card := by
  have hdouble : (∑t ∈ T, (F t).card) =
      ∑e ∈ T.biUnion F, (T.filter (fun t => e ∈ F t)).card := by
    simp only [card_eq_sum_ones,sum_filter]
    rw [sum_comm]
    apply sum_congr rfl
    intro t ht
    simp only [←sum_filter]
    congr 1
    ext e
    simp only [mem_filter,mem_biUnion]
    exact ⟨fun hh => ⟨⟨t,ht,hh⟩,hh⟩,fun hh => hh.2⟩
  rw [hdouble]
  have heq : 2*(T.biUnion F).card = ∑_e ∈ T.biUnion F, 2 := by simp [mul_comm]
  rw [heq]
  apply sum_le_sum
  intro e he
  apply le_trans (card_le_card (show T.filter (fun t => e ∈ F t) ⊆
      T.filter (fun t => e ∈ H.parentBoundary G t) from by
    intro t ht
    obtain ⟨ht,he⟩ := mem_filter.mp ht
    exact mem_filter.mpr ⟨ht,hF t ht he⟩))
  exact H.parentBoundary_multiplicity G T hT hroot e

end
end StrongThinTree.MultiGraph.Hierarchy

namespace StrongThinTree.MultiGraph.Hierarchy
noncomputable section
open Finset StrongThinTree.Geometry StrongThinTree.Geometry.RadialShell
open scoped Classical
variable {n m h : ℕ} {H : Hierarchy n} {G : MultiGraph n m}
  {X : Fin n → Fin h → ℝ}

lemma capture_small_balls (T : Finset (Finset (Fin n))) (S P : Finset (Fin n))
    (hS : S.Nonempty) (hT : T ⊆ H.nodes) (hroot : ∀t ∈ T, t ≠ univ)
    (hboundary : ∀t ∈ T, 0 < (H.parentBoundary G t).card)
    {δ c₂ η : ℝ} (hδ : 0 < δ) (hc : 0 < c₂) (_hη : 0 ≤ η)
    (hsep : (S : Set (Fin n)).Pairwise (fun u v =>
      Disjoint ((ball u δ).support X) ((ball v δ).support X)))
    (hcover : ∀u ∈ S, ∃v ∈ P, l1dist (X u) (X v) ≤ c₂)
    (hP : ∀u ∈ P, ∃t ∈ T, u ∈ t ∧ ∃e ∈ H.parentBoundary G t,
      (G.left e = u ∨ G.right e = u) ∧ l1dist (X (G.left e)) (X (G.right e)) ≤ c₂)
    (hηδ : 864*η*(∑t ∈ T, ((H.parentBoundary G t).card : ℝ)) ≤ S.card)
    (hηc : 1728*η*c₂*(∑t ∈ T, ((H.parentBoundary G t).card : ℝ)) ≤ δ*S.card) :
    (∃F : CompactFamily X δ (6*max δ (2*c₂)),
      δ*(S.card : ℝ)/864 ≤ δ*(∑B ∈ F.bags, (B.card : ℝ))) ∨
    (∃F : AssignedFamily H G X η, F.radius = max δ (2*c₂) ∧ F.owners ⊆ T ∧
      δ*(S.card : ℝ)/864 ≤ F.mass) := by
  let D := max δ (2*c₂)
  have hD : 0 < D := hδ.trans_le (le_max_left _ _)
  have hcD : c₂ < D := lt_of_lt_of_le (by linarith) (le_max_right _ _)
  obtain ⟨u0,hu0⟩ := hS
  obtain ⟨v0,hv0,hv0d⟩ := hcover u0 hu0
  have hPne : P.Nonempty := ⟨v0,hv0⟩
  obtain ⟨W,hWP,hW,hWsep,hWcover⟩ := l1_separated_net X P hPne (show 0 ≤ 2*D by positivity)
  have hballs : (W : Set (Fin n)).Pairwise (fun u v =>
      Disjoint ((ball u D).support X) ((ball v D).support X)) := by
    intro u hu v hv huv
    exact distance_balls_disjoint X u v (hWsep u hu v hv huv).le
  have hcover' : ∀u ∈ S, ∃v ∈ W, l1dist (X u) (X v) ≤ 3*D := by
    intro u hu
    obtain ⟨p,hp,hup⟩ := hcover u hu
    obtain ⟨v,hv,hpv⟩ := hWcover p hp
    exact ⟨v,hv,(l1dist_triangle (X u) (X p) (X v)).trans (by linarith)⟩
  by_cases hsmall : 432*D*(W.card : ℝ) ≤ δ*(S.card : ℝ)
  · obtain ⟨F,hF⟩ := compact_from_net S W ⟨u0,hu0⟩ hW hδ (le_max_left _ _) hsep hcover' hsmall
    exact Or.inl ⟨F,(by nlinarith [show (0:ℝ) ≤ S.card from Nat.cast_nonneg _] : δ*(S.card : ℝ)/864 ≤ δ*(S.card : ℝ)/2).trans hF⟩
  · have hlarge : δ*(S.card : ℝ) < 432*D*(W.card : ℝ) := lt_of_not_ge hsmall
    have hcenter : ∀u ∈ W, ∃t ∈ T, u ∈ t ∧ ∃e ∈ H.parentBoundary G t,
        (G.left e = u ∨ G.right e = u) ∧ l1dist (X (G.left e)) (X (G.right e)) < D := by
      intro u hu
      obtain ⟨t,ht,hut,e,he,heu,hlen⟩ := hP u (hWP hu)
      exact ⟨t,ht,hut,e,he,heu,hlen.trans_lt hcD⟩
    let N : ℝ := ∑t ∈ T, ((H.parentBoundary G t).card : ℝ)
    obtain ⟨t0,ht0,ht0c⟩ := hP v0 hv0
    have hN : 0 < N := sum_pos (fun t ht => by exact_mod_cast hboundary t ht) ⟨t0,ht0⟩
    have hnumer : 864*η*N*D ≤ δ*(S.card : ℝ) := by
      rcases le_total δ (2*c₂) with hh | hh
      · dsimp [D]
        rw [max_eq_right hh]
        change 1728*η*c₂*N ≤ δ*(S.card : ℝ) at hηc
        nlinarith
      · dsimp [D]
        rw [max_eq_left hh]
        change 864*η*N ≤ (S.card : ℝ) at hηδ
        simpa [mul_comm δ] using mul_le_mul_of_nonneg_right hηδ hδ.le
    have hassign : η ≤ (W.card : ℝ)/(2*N) := by
      apply (le_div_iff₀ (mul_pos (by norm_num) hN)).mpr
      nlinarith
    obtain ⟨F,hFD,hFT,hgain⟩ := assigned_from_net T W hW hT hroot hboundary hD hballs hcenter hassign
    exact Or.inr ⟨F,hFD,hFT,(by nlinarith : δ*(S.card : ℝ)/864 ≤ D*(W.card : ℝ)/2).trans hgain⟩

end
end StrongThinTree.MultiGraph.Hierarchy

end

end OAI
