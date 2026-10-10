import OAI.Combinatorics.CycleDecomposition.Templates

namespace OAI

section
open Filter Asymptotics Real
open scoped Topology
noncomputable section
open MeasureTheory ProbabilityTheory Finset
section
namespace ErdosGallai.Batch
noncomputable section
open Finset SimpleGraph
attribute [local instance] Classical.propDecidable

theorem cycle_template_of_representatives_bounded {V W : Type} [Fintype W]
    {G : SimpleGraph V} {Q : SimpleGraph W} (projMap : V → W)
    (S : Set (Sym2 V)) (hSG : S ⊆ G.edgeSet)
    (hrep : ∀ e ∈ Q.edgeSet, ∃! f, f ∈ S ∧ Sym2.map projMap f = e)
    {a : W} (p : Q.Walk a a) (hp : p.IsCycle)
    (M : ℕ) (hM : p.dropLast.support.toFinset.card ≤ M) :
    ∃ b : RoutingTemplate G,
      b.edges = {e | e ∈ S ∧ Sym2.map projMap e ∈ p.edgeSet} ∧
      Fintype.card b.Arity ≤ M ∧
      b.vertices.card ≤ 2*M ∧
      ∀ i, projMap (b.x i) = projMap (b.y i) := by
  classical
  obtain ⟨R,hR⟩ := orient_edge_representatives projMap S hSG (fun e he =>
    (hrep e he).exists)
  let v₀ := (R ⟨(a,p.snd),p.adj_snd hp.not_nil⟩).fst
  obtain ⟨s,t,hports,hproj⟩ := choose_cycle_ports projMap R (fun d => (hR d).2) p hp v₀
  have hfst (d : Q.Dart) (hd : d ∈ p.darts) : d.fst ∈ p.dropLast.support := by
    rw [p.support_dropLast hp.not_nil,← Walk.map_fst_darts]
    exact List.mem_map.mpr ⟨d,hd,rfl⟩
  have hsnd (d : Q.Dart) (hd : d ∈ p.darts) : d.snd ∈ p.dropLast.support := by
    rw [p.support_dropLast hp.not_nil]
    apply p.tail_support_perm_dropLast_support.mem_iff.mp
    rw [← Walk.map_snd_darts]
    exact List.mem_map.mpr ⟨d,hd,rfl⟩
  let c : CycleOutline G := {
    W := W, finiteW := inferInstance, Q := Q, base := a, cycle := p, isCycle := hp,
    rep := R, start := fun z => if z ∈ p.dropLast.support then s z else v₀,
    finish := fun z => if z ∈ p.dropLast.support then t z else v₀,
    project := projMap,
    ports := by intro d hd; simpa only [ite_eq_left (hfst d hd),ite_eq_left (hsnd d hd)] using hports d hd,
    projects := by intro z hz; simpa only [ite_eq_left hz] using hproj z hz,
    outside := by intro z hz; simp only [ite_eq_right hz]
  }
  have hmap (d : Q.Dart) : Sym2.map projMap (R d).edge = d.edge := by
    change s(projMap (R d).fst,projMap (R d).snd) = s(d.fst,d.snd)
    rw [(hR d).2.1,(hR d).2.2]
  have he : c.edges = {e | e ∈ S ∧ Sym2.map projMap e ∈ p.edgeSet} := by
    ext e
    constructor
    · rintro ⟨d,hd,rfl⟩
      refine ⟨(hR d).1,?_⟩
      rw [hmap]
      change d.edge ∈ p.edges
      rw [Walk.edges_eq_map_darts]
      exact List.mem_map.mpr ⟨d,hd,rfl⟩
    · rintro ⟨hS,he⟩
      change Sym2.map projMap e ∈ p.edges at he
      rw [Walk.edges_eq_map_darts] at he
      obtain ⟨d,hd,hde⟩ := List.mem_map.mp he
      refine ⟨d,hd,?_⟩
      exact (hrep d.edge d.edge_mem).unique ⟨hS,hde.symm⟩ ⟨(hR d).1,hmap d⟩
  refine ⟨RoutingTemplate.ofCycle c,he,?_,?_,?_⟩
  · change Fintype.card c.Switch ≤ M
    apply le_trans _ hM
    apply Finset.card_le_card_of_injOn (fun i : c.Switch => i.val)
    · intro z hz; exact List.mem_toFinset.mpr z.property.1
    · intro z _ w _ h; exact Subtype.ext h
  · exact c.vertices_card_support.trans (Nat.mul_le_mul_left _ hM)
  · intro i
    change c.Switch at i
    exact (c.projects i i.property.1).1.trans (c.projects i i.property.1).2.symm

theorem cycle_template_of_representatives {V W : Type} [Fintype W]
    {G : SimpleGraph V} {Q : SimpleGraph W} (projMap : V → W)
    (S : Set (Sym2 V)) (hSG : S ⊆ G.edgeSet)
    (hrep : ∀ e ∈ Q.edgeSet, ∃! f, f ∈ S ∧ Sym2.map projMap f = e)
    {a : W} (p : Q.Walk a a) (hp : p.IsCycle) :
    ∃ b : RoutingTemplate G,
      b.edges = {e | e ∈ S ∧ Sym2.map projMap e ∈ p.edgeSet} ∧
      Fintype.card b.Arity ≤ Fintype.card W ∧
      b.vertices.card ≤ 2*Fintype.card W ∧
      ∀ i, projMap (b.x i) = projMap (b.y i) := by
  exact cycle_template_of_representatives_bounded projMap S hSG hrep p hp _ (Finset.card_le_univ _)

theorem quotient_part_template {V W : Type} [Fintype W]
    {G : SimpleGraph V} {Q : SimpleGraph W} (projMap : V → W)
    (S : Set (Sym2 V)) (hSG : S ⊆ G.edgeSet)
    (hrep : ∀ e ∈ Q.edgeSet, ∃! f, f ∈ S ∧ Sym2.map projMap f = e)
    (s : Set (Sym2 W)) (hs : CycleOrSingleEdge Q s) :
    ∃ b : RoutingTemplate G,
      b.edges = {e | e ∈ S ∧ Sym2.map projMap e ∈ s} ∧
      Fintype.card b.Arity ≤ Fintype.card W ∧
      b.vertices.card ≤ 2*Fintype.card W ∧
      ∀ i, projMap (b.x i) = projMap (b.y i) := by
  rcases hs with ⟨a,p,hp,rfl⟩ | ⟨e,he,rfl⟩
  · exact cycle_template_of_representatives projMap S hSG hrep p hp
  · obtain ⟨f,hf,huniq⟩ := hrep e he
    refine ⟨RoutingTemplate.ofSingle f (hSG hf.1),?_,by change Fintype.card Empty ≤ _; simp,by simp [RoutingTemplate.ofSingle],fun i => i.elim⟩
    ext g
    change g = f ↔ g ∈ S ∧ Sym2.map projMap g ∈ ({e} : Set (Sym2 W))
    constructor
    · intro h; subst g; exact ⟨hf.1,hf.2⟩
    · rintro ⟨hg,hge⟩; exact huniq g ⟨hg,hge⟩

theorem quotient_partition_templates {V W : Type} [Fintype W]
    {G : SimpleGraph V} {Q : SimpleGraph W} (projMap : V → W)
    (S : Set (Sym2 V)) (hSG : S ⊆ G.edgeSet)
    (himage : Sym2.map projMap '' S = Q.edgeSet)
    (hrep : ∀ e ∈ Q.edgeSet, ∃! f, f ∈ S ∧ Sym2.map projMap f = e)
    {k : ℕ} (hQ : EdgeDecomposition Q k) :
    ∃ b : Fin k → RoutingTemplate G,
      Pairwise (fun i j => Disjoint (b i).edges (b j).edges) ∧
      (⋃ i, (b i).edges) = S ∧
      (∀ i, Fintype.card (b i).Arity ≤ Fintype.card W ∧
        (b i).vertices.card ≤ 2*Fintype.card W ∧
        ∀ j, projMap ((b i).x j) = projMap ((b i).y j)) := by
  classical
  obtain ⟨parts,hp,hd,hcover⟩ := hQ
  choose b hb hnum hv hprojMap using fun i => quotient_part_template projMap S hSG hrep (parts i) (hp i)
  refine ⟨b,?_,?_,fun i => ⟨hnum i,hv i,hprojMap i⟩⟩
  · intro i j hij
    rw [hb i,hb j]
    exact Set.disjoint_left.mpr (fun _ hi hj => Set.disjoint_left.mp (hd hij) hi.2 hj.2)
  · ext e
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨i,hi⟩; rw [hb i] at hi; exact hi.1
    · intro he
      have hq : Sym2.map projMap e ∈ Q.edgeSet := by rw [← himage]; exact Set.mem_image_of_mem _ he
      rw [← hcover] at hq
      obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hq
      exact ⟨i,by rw [hb i]; exact ⟨he,hi⟩⟩

theorem quotient_part_template_on {V W : Type} [Fintype W]
    {G : SimpleGraph V} {Q : SimpleGraph W} (projMap : V → W)
    (S : Set (Sym2 V)) (hSG : S ⊆ G.edgeSet)
    (A : Finset W) (hA : ∀ ⦃x y⦄, Q.Adj x y → x ∈ A ∧ y ∈ A)
    (hrep : ∀ e ∈ Q.edgeSet, ∃! f, f ∈ S ∧ Sym2.map projMap f = e)
    (s : Set (Sym2 W)) (hs : CycleOrSingleEdge Q s) :
    ∃ b : RoutingTemplate G,
      b.edges = {e | e ∈ S ∧ Sym2.map projMap e ∈ s} ∧
      Fintype.card b.Arity ≤ A.card ∧
      b.vertices.card ≤ 2*A.card ∧
      ∀ i, projMap (b.x i) = projMap (b.y i) := by
  rcases hs with ⟨a,p,hp,rfl⟩ | ⟨e,he,rfl⟩
  · exact cycle_template_of_representatives_bounded projMap S hSG hrep p hp A.card (by
      apply Finset.card_le_card
      intro z hz
      rw [List.mem_toFinset,p.support_dropLast hp.not_nil,← Walk.map_fst_darts] at hz
      obtain ⟨d,hd,rfl⟩ := List.mem_map.mp hz
      exact (hA d.adj).1)
  · obtain ⟨f,hf,huniq⟩ := hrep e he
    refine ⟨RoutingTemplate.ofSingle f (hSG hf.1),?_,by change Fintype.card Empty ≤ _; simp,by simp [RoutingTemplate.ofSingle],fun i => i.elim⟩
    ext g
    change g = f ↔ g ∈ S ∧ Sym2.map projMap g ∈ ({e} : Set (Sym2 W))
    constructor
    · intro h; subst g; exact ⟨hf.1,hf.2⟩
    · rintro ⟨hg,hge⟩; exact huniq g ⟨hg,hge⟩

theorem quotient_partition_templates_on {V W : Type} [Fintype W]
    {G : SimpleGraph V} {Q : SimpleGraph W} (projMap : V → W)
    (S : Set (Sym2 V)) (hSG : S ⊆ G.edgeSet)
    (A : Finset W) (hA : ∀ ⦃x y⦄, Q.Adj x y → x ∈ A ∧ y ∈ A)
    (himage : Sym2.map projMap '' S = Q.edgeSet)
    (hrep : ∀ e ∈ Q.edgeSet, ∃! f, f ∈ S ∧ Sym2.map projMap f = e)
    {k : ℕ} (hQ : EdgeDecomposition Q k) :
    ∃ b : Fin k → RoutingTemplate G,
      Pairwise (fun i j => Disjoint (b i).edges (b j).edges) ∧
      (⋃ i, (b i).edges) = S ∧
      (∀ i, Fintype.card (b i).Arity ≤ A.card ∧
        (b i).vertices.card ≤ 2*A.card ∧
        ∀ j, projMap ((b i).x j) = projMap ((b i).y j)) := by
  classical
  obtain ⟨parts,hp,hd,hcover⟩ := hQ
  choose b hb hnum hv hprojMap using fun i => quotient_part_template_on projMap S hSG A hA hrep (parts i) (hp i)
  refine ⟨b,?_,?_,fun i => ⟨hnum i,hv i,hprojMap i⟩⟩
  · intro i j hij
    rw [hb i,hb j]
    exact Set.disjoint_left.mpr (fun _ hi hj => Set.disjoint_left.mp (hd hij) hi.2 hj.2)
  · ext e
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨i,hi⟩; rw [hb i] at hi; exact hi.1
    · intro he
      have hq : Sym2.map projMap e ∈ Q.edgeSet := by rw [← himage]; exact Set.mem_image_of_mem _ he
      rw [← hcover] at hq
      obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hq
      exact ⟨i,by rw [hb i]; exact ⟨he,hi⟩⟩

end
end ErdosGallai.Batch

namespace ErdosGallai.Batch
noncomputable section
open Finset SimpleGraph
attribute [local instance] Classical.propDecidable

lemma walk_support_on {V : Type} {G : SimpleGraph V} (W : Finset V)
    (hW : ∀ ⦃x y⦄, G.Adj x y → x ∈ W ∧ y ∈ W)
    {x y : V} (p : G.Walk x y) (hp : 0 < p.length) : p.support.toFinset ⊆ W := by
  classical
  intro v hv
  obtain ⟨e,he,hv⟩ := Walk.mem_support_iff_exists_mem_edges_of_not_nil
    (p := p) (by simpa only [Walk.length_eq_zero_iff.symm] using (Nat.ne_of_gt hp)) |>.mp (List.mem_toFinset.mp hv)
  induction e using Sym2.ind with
  | _ a b =>
    have hab : G.Adj a b := p.edges_subset_edgeSet he
    rcases Sym2.mem_iff.mp hv with rfl | rfl
    · exact (hW hab).1
    · exact (hW hab).2

structure BatchTemplateFamily {V I : Type} [Fintype I]
    (G J : SimpleGraph V) (X : I → Finset V) (W : Finset V) (bad : Finset (Sym2 V)) (k : ℕ) where
  Index : Type
  finiteIndex : Fintype Index
  block : Index → RoutingTemplate G
  count : Fintype.card Index ≤ k + 2 * ∑ i, (X i).card
  disjoint : Pairwise fun i j => Disjoint (block i).edges (block j).edges
  bad_disjoint : ∀ i, Disjoint (bad : Set (Sym2 V)) (block i).edges
  cover : (bad : Set (Sym2 V)) ∪ (⋃ i, (block i).edges) = J.edgeSet
  arity : ∀ i, Fintype.card (block i).Arity ≤ W.card
  vertices : ∀ i, (block i).vertices.card ≤ 2*W.card
  owner : (i : Index) → (block i).Arity → I
  ends : ∀ i j, (block i).x j ∈ X (owner i j) ∧ (block i).y j ∈ X (owner i j)
attribute [instance] BatchTemplateFamily.finiteIndex

lemma BatchTemplateFamily.subset {V I : Type} [Fintype I]
    {G J : SimpleGraph V} {X : I → Finset V} {W bad k}
    (b : BatchTemplateFamily G J X W bad k) (i : b.Index) : (b.block i).edges ⊆ J.edgeSet := by
  rw [← b.cover]
  intro e he; exact Or.inr (Set.mem_iUnion.mpr ⟨i,he⟩)

theorem prepare_templates {V I : Type} [Fintype V] [Fintype I]
    (G J : SimpleGraph V) (hJG : J ≤ G) (W : Finset V)
    (hW : ∀ ⦃x y⦄, J.Adj x y → x ∈ W ∧ y ∈ W)
    (X : I → Finset V) (hd : Pairwise fun i j => Disjoint (X i) (X j))
    (hX : ∀ i, X i ⊆ W) (b : PreparedBatch J X hd)
    {k : ℕ} (hk : EdgeDecomposition b.quotient k) :
    Nonempty (BatchTemplateFamily G J X W b.bad k) := by
  classical
  let projMap := familyProject X hd b.pairing
  let A := W.image projMap
  have hAW : A.card ≤ W.card := Finset.card_image_le
  obtain ⟨q,hqd,hqu,hqn⟩ := quotient_partition_templates_on projMap (b.retained:Set (Sym2 V))
    (b.retained_subset.trans (SimpleGraph.edgeSet_mono hJG)) A (b.quotient_supported W hW)
    b.quotient_edges.symm (by simpa only [Finset.mem_coe] using b.representatives) hk
  have hqsub (j) : (q j).edges ⊆ (b.retained : Set (Sym2 V)) := by
    rw [← hqu]; intro e he; exact Set.mem_iUnion.mpr ⟨j,he⟩
  have hex (j) (i : (q j).Arity) : ∃ r, (q j).x i ∈ X r ∧ (q j).y i ∈ X r := by
    obtain he | ⟨r,hx,hy,_⟩ := (familyProject_eq_iff X hd b.pairing _ _).mp ((hqn j).2.2 i)
    · exact False.elim ((q j).ne i he)
    · exact ⟨r,hx,hy⟩
  choose own hown using hex
  let P := {z : Σ i, Fin (b.count i) // 0 < (b.path z.1 z.2).walk.length}
  let path : ∀ z : P, G.Walk (b.path z.1.1 z.1.2).start (b.path z.1.1 z.1.2).finish :=
    fun z => (b.path z.1.1 z.1.2).walk.map (SimpleGraph.Hom.ofLE hJG)
  have hpe (z : P) : (path z).edgeSet = (b.path z.1.1 z.1.2).walk.edgeSet := by
    simp [path,Walk.edgeSet_map,SimpleGraph.Hom.ofLE]
  have hps (z : P) : (path z).IsPath := (b.path z.1.1 z.1.2).simple.map Function.injective_id
  have hpl (z : P) : 2 ≤ (path z).length := by
    simpa only [path,Walk.length_map] using (b.ends z.1.1 z.1.2 z.property).2.2
  let t : P → RoutingTemplate G := fun z => RoutingTemplate.ofPath (path z) (hps z) (hpl z)
  have hte (z : P) : (t z).edges = (b.path z.1.1 z.1.2).walk.edgeSet := hpe z
  have htv (z : P) : (t z).vertices.card ≤ W.card := by
    apply Finset.card_le_card
    change (path z).support.toFinset ⊆ W
    simpa [path,Walk.support_map,SimpleGraph.Hom.ofLE] using
      walk_support_on W hW (b.path z.1.1 z.1.2).walk z.property
  have hta (z : P) : Fintype.card (t z).Arity ≤ W.card := by
    change Fintype.card Unit ≤ W.card
    simpa using Finset.card_pos.mpr ⟨(b.path z.1.1 z.1.2).start,
      hX z.1.1 (b.ends z.1.1 z.1.2 z.property).1⟩
  have htu : (⋃ z, (t z).edges) = ⋃ i, ⋃ j, (b.path i j).walk.edgeSet := by
    ext e; simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨z,hz⟩; exact ⟨z.1.1,z.1.2,(hte z) ▸ hz⟩
    · rintro ⟨i,j,hj⟩
      have hp : 0 < (b.path i j).walk.length := by
        by_contra h
        have hn := Walk.length_eq_zero_iff.mp (Nat.eq_zero_of_not_pos h)
        have he := Walk.edges_eq_nil.mpr hn
        change e ∈ (b.path i j).walk.edges at hj
        rw [he] at hj; contradiction
      exact ⟨⟨⟨i,j⟩,hp⟩,by rw [hte]; exact hj⟩
  refine ⟨{
    Index := Fin k ⊕ P,
    finiteIndex := inferInstance,
    block := Sum.elim q t,
    count := ?_,
    disjoint := ?_,
    bad_disjoint := ?_,
    cover := ?_,
    arity := ?_,
    vertices := ?_,
    owner := fun j => match j with | Sum.inl j => own j | Sum.inr z => fun _ => z.1.1,
    ends := ?_
  }⟩
  · have hp : Fintype.card P ≤ 2 * ∑ i, (X i).card := by
      calc
        _ ≤ Fintype.card (Σ i, Fin (b.count i)) := Fintype.card_subtype_le _
        _ = ∑ i, b.count i := by simp
        _ ≤ ∑ i, 2*(X i).card := Finset.sum_le_sum (fun i _ => b.count_le i)
        _ = _ := by rw [← Finset.mul_sum]
    simpa only [Fintype.card_sum,Fintype.card_fin] using Nat.add_le_add_left hp k
  · intro j l hne
    rcases j with j | j <;> rcases l with l | l <;> dsimp only [Sum.elim_inl,Sum.elim_inr]
    · exact hqd (fun h => hne (congrArg Sum.inl h))
    · exact (b.retained_paths l.1.1 l.1.2).mono (hqsub j) (by rw [hte])
    · exact ((b.retained_paths j.1.1 j.1.2).mono (hqsub l) (by rw [hte])).symm
    · rw [hte,hte]
      exact b.paths_disjoint (fun h => hne (congrArg Sum.inr (Subtype.ext h)))
  · rintro (j | z) <;> dsimp only [Sum.elim_inl,Sum.elim_inr]
    · exact b.bad_retained.mono_right (hqsub j)
    · rw [hte]; exact b.bad_paths _ _
  ·
    simp only [Set.iUnion_sum,Sum.elim_inl,Sum.elim_inr]
    rw [hqu,htu,← Set.union_assoc]
    exact b.cover
  · rintro (j | z)
    · exact (hqn j).1.trans hAW
    · exact hta z
  · rintro (j | z)
    · exact (hqn j).2.1.trans (Nat.mul_le_mul_left _ hAW)
    · exact (htv z).trans (by omega)
  · rintro (j | z) i
    · exact hown j i
    · exact ⟨(b.ends z.1.1 z.1.2 z.property).2.1,(b.ends z.1.1 z.1.2 z.property).1⟩

end
end ErdosGallai.Batch

namespace ErdosGallai.Batch
noncomputable section
open Finset SimpleGraph
attribute [local instance] Classical.propDecidable

theorem uniform_batch_resolution :
    ∃ D₀ : ℝ, 1 < D₀ ∧ ∀ D ≥ D₀,
      ∀ (V R B : Type) [Fintype V] [Fintype R] [Fintype B],
      ∀ (G F : SimpleGraph V) (P : R → SimpleGraph V) (U : R → Finset V),
      F ≤ G → (∀ r, P r ≤ G) →
      Pairwise (fun r s => Disjoint (P r).edgeSet (P s).edgeSet) →
      Pairwise (fun r s => Disjoint (U r) (U s)) →
      (∀ r, Disjoint F.edgeSet (P r).edgeSet) →
      (∀ r, CutExpansionOn (P r) (U r) (D^(9/10:ℝ)/4)) →
      (∀ r, D^(9/10:ℝ) ≤ ((U r).card:ℝ) ∧ ((U r).card:ℝ) ≤ D^(51/50:ℝ)) →
      ∀ (J : B → SimpleGraph V) (W : B → Finset V),
      (∀ b, J b ≤ F) → Pairwise (fun b c => Disjoint (J b).edgeSet (J c).edgeSet) →
      (⋃ b, (J b).edgeSet) = F.edgeSet →
      (∀ b, ∀ ⦃x y⦄, (J b).Adj x y → x ∈ W b ∧ y ∈ W b) →
      (∀ b, ((W b).card:ℝ) ≤ D^(3/10:ℝ)) →
      ∀ (I : B → Type) [∀ b, Fintype (I b)] (X : ∀ b, I b → Finset V)
        (hXd : ∀ b, Pairwise fun i j => Disjoint (X b i) (X b j)),
      (∀ b i, X b i ⊆ W b) →
      ∀ rX : ∀ b, I b → R,
      (∀ b i, X b i ⊆ U (rX b i)) →
      (∀ b i v, v ∈ X b i → (F.degree v:ℝ) ≤ D^(1/100:ℝ)) →
      ∀ (prep : ∀ b, PreparedBatch (J b) (X b) (hXd b)) (k : B → ℕ),
      (∀ b, EdgeDecomposition (prep b).quotient (k b)) →
      ∃ (K : Type) (_ : Fintype K) (parts : K → Set (Sym2 V)) (used : Set (Sym2 V)),
        Fintype.card K ≤ (∑ b, k b) + 8 * ∑ b, ∑ i, (X b i).card ∧
        (∀ j, CycleOrSingleEdge G (parts j)) ∧
        Pairwise (fun j l => Disjoint (parts j) (parts l)) ∧
        used ⊆ ⋃ r, (P r).edgeSet ∧ Disjoint F.edgeSet used ∧
        (⋃ j, parts j) = F.edgeSet ∪ used := by
  classical
  obtain ⟨D₀,hD₀,hresolve⟩ := uniform_resolve_templates
  refine ⟨D₀,hD₀,?_⟩
  intro D hD V R B _ _ _ G F P U hFG hPG hPP hUU hFP he hr J W hJF hJJ hJu hW hWnum I _ X hXd hXW rX hXU hdeg prep k hk
  have hT (b : B) := prepare_templates G (J b) ((hJF b).trans hFG) (W b) (hW b)
    (X b) (hXd b) (hXW b) (prep b) (hk b)
  let T : ∀ b, BatchTemplateFamily G (J b) (X b) (W b) (prep b).bad (k b) :=
    fun b => Classical.choice (hT b)
  let Q := Σ b, (T b).Index
  let q : Q → RoutingTemplate G := fun z => (T z.1).block z.2
  have hqsub (z : Q) : (q z).edges ⊆ F.edgeSet :=
    ((T z.1).subset z.2).trans (SimpleGraph.edgeSet_mono (hJF z.1))
  have hqd : Pairwise fun z w : Q => Disjoint (q z).edges (q w).edges := by
    rintro ⟨b,i⟩ ⟨c,j⟩ hne
    by_cases hh : b = c
    · subst c; exact (T b).disjoint (fun h => hne (by cases h; rfl))
    · exact (hJJ hh).mono ((T b).subset i) ((T c).subset j)
  let owner : (z : Q) → (q z).Arity → R := fun z i => rX z.1 ((T z.1).owner z.2 i)
  obtain ⟨parts,used,hparts,hpartsd,hused,hFu,hcover⟩ :=
    hresolve D hD V R Q G F P U hFG hPG hPP hUU hFP he hr q hqsub hqd owner
      (fun z i => ⟨hXU _ _ ((T z.1).ends z.2 i).1,hXU _ _ ((T z.1).ends z.2 i).2⟩)
      (fun z i => ⟨hdeg _ _ _ ((T z.1).ends z.2 i).1,hdeg _ _ _ ((T z.1).ends z.2 i).2⟩)
      (fun z => (Nat.cast_le.mpr ((T z.1).arity z.2)).trans (hWnum z.1))
      (fun z => (Nat.cast_le.mpr ((T z.1).vertices z.2)).trans (by
        push_cast; exact mul_le_mul_of_nonneg_left (hWnum z.1) (by norm_num)))
  let S := Σ b, (prep b).bad
  let e : S → Sym2 V := fun z => z.2.val
  have hSsub (z : S) : e z ∈ (J z.1).edgeSet := (prep z.1).bad_subset z.2.property
  have hSF (z : S) : e z ∈ F.edgeSet := SimpleGraph.edgeSet_mono (hJF z.1) (hSsub z)
  have hinj : Function.Injective e := by
    rintro ⟨b,i⟩ ⟨c,j⟩ h
    by_cases hh : b = c
    · subst c; exact Sigma.ext rfl (heq_of_eq (Subtype.ext h))
    · exact False.elim (Set.disjoint_left.mp (hJJ hh) (hSsub ⟨b,i⟩) (h ▸ hSsub ⟨c,j⟩))
  have hbadq (z : S) (w : Q) : e z ∉ (q w).edges := by
    intro hw
    by_cases hh : z.1 = w.1
    · rcases z with ⟨b,z⟩; rcases w with ⟨c,w⟩
      dsimp only at hh; subst c
      exact Set.disjoint_left.mp ((T b).bad_disjoint w) z.property hw
    · exact Set.disjoint_left.mp (hJJ hh) (hSsub z) ((T w.1).subset w.2 hw)
  have hbadpart (z : S) (w : Q) : e z ∉ parts w := by
    intro hw
    have hu : e z ∈ ⋃ w, parts w := Set.mem_iUnion.mpr ⟨w,hw⟩
    rw [hcover] at hu
    rcases hu with hu | hu
    · obtain ⟨w,hw⟩ := Set.mem_iUnion.mp hu; exact hbadq z w hw
    · exact Set.disjoint_left.mp hFu (hSF z) hu
  have horiginal : (⋃ z : S, {e z}) ∪ (⋃ w : Q, (q w).edges) = F.edgeSet := by
    rw [← hJu]
    ext f
    simp only [Set.mem_union,Set.mem_iUnion,Set.mem_singleton_iff]
    constructor
    · rintro (⟨z,hz⟩ | ⟨w,hw⟩)
      · exact ⟨z.1,hz ▸ hSsub z⟩
      · exact ⟨w.1,(T w.1).subset w.2 hw⟩
    · rintro ⟨b,hb⟩
      rw [← (T b).cover] at hb
      rcases hb with hb | hb
      · exact Or.inl ⟨⟨b,⟨f,hb⟩⟩,rfl⟩
      · obtain ⟨j,hj⟩ := Set.mem_iUnion.mp hb
        exact Or.inr ⟨⟨b,j⟩,hj⟩
  refine ⟨Q ⊕ S,inferInstance,Sum.elim parts (fun z => {e z}),used,?_,?_,?_,hused,hFu,?_⟩
  · have hq : Fintype.card Q ≤ (∑ b, k b) + 2*∑ b, ∑ i, (X b i).card := by
      calc
        _ = ∑ b, Fintype.card (T b).Index := Fintype.card_sigma
        _ ≤ ∑ b, (k b + 2 * ∑ i, (X b i).card) := Finset.sum_le_sum (fun b _ => (T b).count)
        _ = _ := by rw [Finset.sum_add_distrib,← Finset.mul_sum]
    have hs : Fintype.card S ≤ 6*∑ b, ∑ i, (X b i).card := by
      calc
        _ = ∑ b, (prep b).bad.card := by simp [S,Fintype.card_sigma]
        _ ≤ ∑ b, 6*∑ i, (X b i).card := Finset.sum_le_sum (fun b _ => (prep b).bad_le)
        _ = _ := by rw [← Finset.mul_sum]
    rw [Fintype.card_sum]; omega
  · rintro (j | z)
    · exact hparts j
    · exact Or.inr ⟨e z,SimpleGraph.edgeSet_mono hFG (hSF z),rfl⟩
  · rintro (i | i) (j | j) hij <;> dsimp only [Sum.elim_inl,Sum.elim_inr]
    · exact hpartsd (fun h => hij (congrArg Sum.inl h))
    · exact (Set.disjoint_singleton_right).mpr (hbadpart j i)
    · exact (Set.disjoint_singleton_left).mpr (hbadpart i j)
    · exact Set.disjoint_singleton.mpr (fun h => hij (congrArg Sum.inr (hinj h)))
  · simp only [Set.iUnion_sum,Sum.elim_inl,Sum.elim_inr]
    rw [hcover]
    calc
      _ = ((⋃ z : S, {e z}) ∪ (⋃ w : Q, (q w).edges)) ∪ used := by
        rw [Set.union_comm ((⋃ w : Q, (q w).edges) ∪ used), Set.union_assoc]
      _ = _ := by rw [horiginal]

end
end ErdosGallai.Batch

end
end
end

end OAI
