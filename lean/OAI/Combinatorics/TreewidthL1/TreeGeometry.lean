import OAI.Combinatorics.TreewidthL1.ExpandedAnchor

namespace OAI

universe treewidthLevel1 treewidthLevel2

namespace BoundedTreewidthL1.RootedTree
attribute [local instance] Classical.decEq Classical.propDecidable
variable {I : Type*} (T : SimpleGraph I) (hT : T.IsTree) (root X : I)
lemma downPath_take (t : ℕ) :
    downPath T hT root ((downPath T hT root X).getVert t) =
      (downPath T hT root X).take t := by
  exact congrArg Subtype.val ((hT.isAcyclic.subsingleton_path _ _).elim
    ⟨_, downPath_isPath T hT root _⟩ ⟨_, (downPath_isPath T hT root X).take t⟩)
lemma depth_getVert (t : ℕ) (ht : t ≤ (forest T hT root).depth X) :
    (forest T hT root).depth ((downPath T hT root X).getVert t) = t := by
  rw [← downPath_length, downPath_take, SimpleGraph.Walk.take_length,downPath_length]
  exact min_eq_left ht
lemma downPath_getVert_getVert (t a : ℕ) (ha : a ≤ t) :
    (downPath T hT root ((downPath T hT root X).getVert t)).getVert a =
      (downPath T hT root X).getVert a := by
  rw [downPath_take,SimpleGraph.Walk.take_getVert,inf_eq_right.mpr ha]
lemma parent_getVert (t : ℕ) (ht : t < (forest T hT root).depth X) :
    (forest T hT root).parent ((downPath T hT root X).getVert (t+1)) =
      some ((downPath T hT root X).getVert t) := by
  have hadj : T.Adj ((downPath T hT root X).getVert t)
      ((downPath T hT root X).getVert (t+1)) :=
    (downPath T hT root X).adj_getVert_succ (by simpa [downPath_length] using ht)
  rcases edge_orientation T hT root hadj with h | h
  · have hdec := (forest T hT root).decreases _ _ h
    rw [depth_getVert T hT root X t (by omega),depth_getVert T hT root X (t+1) (by omega)] at hdec
    omega
  · exact h
end BoundedTreewidthL1.RootedTree

namespace BoundedTreewidthL1.TreeCache
open AnchorCache _root_.OAI.BoundedTreewidthL1.RootedTree
attribute [local instance] Classical.decEq Classical.propDecidable
variable {I V : Type*} (T : SimpleGraph I) (hT : T.IsTree) (root : I)
  (B : I → Finset V) (D : I → V → ℝ) (k : ℕ) (d : V → V → ℝ) (J : ℝ) (X : I)
lemma inclusive_getVert (t : ℕ) (ht : t ≤ (forest T hT root).depth X) :
    inclusive T hT root B D k d J ((downPath T hT root X).getVert t) =
    inclusiveCache k (bags T hT root B X) d (heights T hT root D X) J t := by
  unfold inclusive
  rw [depth_getVert T hT root X t ht]
  apply inclusiveCache_prefix (l := t+1)
  · intro a ha
    unfold bags
    rw [downPath_getVert_getVert T hT root X t a (by omega)]
  · intro a ha v b hb
    unfold heights
    rw [downPath_getVert_getVert T hT root X t b (by omega)]
  · omega
lemma active_getVert (t : ℕ) (ht : t ≤ (forest T hT root).depth X) :
    active T hT root B D k d J ((downPath T hT root X).getVert t) =
    (inclusiveCache k (bags T hT root B X) d (heights T hT root D X) J t).image
      (downPath T hT root X).getVert := by
  unfold active
  rw [inclusive_getVert T hT root B D k d J X t ht]
  apply Finset.image_congr
  intro a ha
  exact downPath_getVert_getVert T hT root X t a (inclusive_age _ _ _ _ _ t a ha)
end BoundedTreewidthL1.TreeCache

namespace BoundedTreewidthL1.RootedTree
attribute [local instance] Classical.decEq Classical.propDecidable
variable {I : Type*} (T : SimpleGraph I) (hT : T.IsTree) (Y Z : I)
noncomputable def pathIndex : Fin ((forest T hT Y).depth Z + 1) ↪ I where
  toFun t := (downPath T hT Y Z).getVert t.val
  inj' := by
    intro a b he
    apply Fin.ext
    have ha := depth_getVert T hT Y Z a.val (by omega)
    have hb := depth_getVert T hT Y Z b.val (by omega)
    dsimp only at he
    rw [he] at ha
    omega
lemma pathIndex_comap : T.comap (pathIndex T hT Y Z) =
    SimpleGraph.pathGraph ((forest T hT Y).depth Z + 1) := by
  ext i j
  rw [SimpleGraph.pathGraph_adj]
  constructor
  · intro hij
    have hd := hT.dist_eq_dist_add_one_of_adj Y hij
    have hi := depth_getVert T hT Y Z i.val (by omega)
    have hj := depth_getVert T hT Y Z j.val (by omega)
    change T.dist ((downPath T hT Y Z).getVert i.val) Y = i.val at hi
    change T.dist ((downPath T hT Y Z).getVert j.val) Y = j.val at hj
    change T.dist Y ((downPath T hT Y Z).getVert i.val) =
      T.dist Y ((downPath T hT Y Z).getVert j.val) + 1 ∨
      T.dist Y ((downPath T hT Y Z).getVert j.val) =
      T.dist Y ((downPath T hT Y Z).getVert i.val) + 1 at hd
    rw [SimpleGraph.dist_comm (u := Y),SimpleGraph.dist_comm (u := Y),hi,hj] at hd
    omega
  · rintro (h | h)
    · change T.Adj ((downPath T hT Y Z).getVert i.val) ((downPath T hT Y Z).getVert j.val)
      rw [← h]
      exact (downPath T hT Y Z).adj_getVert_succ (by rw [downPath_length]; omega)
    · change T.Adj ((downPath T hT Y Z).getVert i.val) ((downPath T hT Y Z).getVert j.val)
      rw [← h]
      exact ((downPath T hT Y Z).adj_getVert_succ (by rw [downPath_length]; omega)).symm
end BoundedTreewidthL1.RootedTree

namespace BoundedTreewidthL1.ExpandedTree
open ReservationCoupling
attribute [local instance] Classical.decEq Classical.propDecidable
variable {I A : Type*} [Fintype I] [Fintype A]
noncomputable def pathJoint (T : SimpleGraph I) (μ : I → A → ℝ)
    (J : I → I → A → A → ℝ) {Y Z : I} (p : T.Walk Y Z) (s : ℕ) (a b : A) : ℝ :=
  if s < p.length then J (p.getVert s) (p.getVert (s+1)) a b
  else if a = b then μ (p.getVert s) a else 0
lemma pathJoint_coupling
    {I : Type treewidthLevel1} {A : Type treewidthLevel2} [Fintype I] [Fintype A]
    (T : SimpleGraph I) (μ : I → A → ℝ)
    (J : I → I → A → A → ℝ) (hμ : ∀ i a, 0 ≤ μ i a)
    (hJ : ∀ i j, T.Adj i j → IsCoupling (μ i) (μ j) (J i j))
    {Y Z : I} (p : T.Walk Y Z) (s : ℕ) :
    IsCoupling (μ (p.getVert s)) (μ (p.getVert (s+1))) (pathJoint T μ J p s) := by
  by_cases hs : s < p.length
  · change IsCoupling _ _ (fun a b => if s < p.length then _ else _)
    simp only [ite_eq_left hs]
    exact hJ _ _ (p.adj_getVert_succ hs)
  · have he : p.getVert (s+1) = p.getVert s := by
      rw [p.getVert_of_length_le (by omega),p.getVert_of_length_le (by omega)]
    rw [he]
    refine ⟨?_,?_,?_⟩
    · intro a b; simp only [pathJoint,ite_eq_right hs]; split_ifs <;> first | exact hμ _ _ | exact le_rfl
    · intro a; simp [pathJoint,hs]
    · intro b; simp [pathJoint,hs]

/-- Restriction of an actual tree law to its unique endpoint path, in the
un-normalized coupling-product convention used by the reservation tests. -/
lemma endpoint_path_product (T : SimpleGraph I) (hT : T.IsTree) (M : ℝ) (hM : 0 < M)
    (μ : I → A → ℝ) (J : I → I → A → A → ℝ) (hs : TreeMarkov.Symmetric (fun _ : I => A) J)
    (hμ : ∀ i a, 0 ≤ μ i a) (hmass : ∀ i, (∑ a, μ i a) = M)
    (hJ : ∀ i j, T.Adj i j → IsCoupling (μ i) (μ j) (J i j))
    (Y Z : I) (f : A → A → ℝ) :
    (∑ x : I → A, law T M μ J hs x * f (x Y) (x Z)) =
      ∑ x : Fin ((RootedTree.forest T hT Y).depth Z + 1) → A,
        MarkovProduct.weight (fun _ => A) (μ Y)
          (MarkovProduct.couplingKernel (fun _ => A)
            (fun s => μ ((RootedTree.downPath T hT Y Z).getVert s))
            (pathJoint T μ J (RootedTree.downPath T hT Y Z)))
          ((RootedTree.forest T hT Y).depth Z) x *
          f (x 0) (x (Fin.last ((RootedTree.forest T hT Y).depth Z))) := by
  let p := RootedTree.downPath T hT Y Z
  let n := (RootedTree.forest T hT Y).depth Z
  let e := RootedTree.pathIndex T hT Y Z
  have he := RootedTree.pathIndex_comap T hT Y Z
  have hep : e 0 = Y := p.getVert_zero
  have hez : e (Fin.last n) = Z := by
    change p.getVert ((RootedTree.forest T hT Y).depth Z) = Z
    rw [← RootedTree.downPath_length T hT Y Z]
    exact p.getVert_length
  have hc : (T.comap e).Connected := he ▸ SimpleGraph.pathGraph_connected n
  have hpath := path_expectation T hT M hM μ J hs hμ hmass
    (fun i j hij => (hJ i j hij).nonneg) (fun i j hij => (hJ i j hij).row)
    e hc (fun x => f (x 0) (x (Fin.last n)))
  simp only [Function.comp_apply,hep,hez] at hpath
  rw [hpath]
  apply Finset.sum_congr (by ext x; simp)
  intro x _
  congr 1
  rw [he]
  have hq := pathJoint_coupling T μ J hμ hJ p
  have hp := law_path_product M hM (fun s => μ (p.getVert s)) (pathJoint T μ J p)
    (fun s => (hq s).nonneg) (fun s => (hq s).row) (fun s => (hq s).col) n
    (fun i j => J (e i) (e j)) (fun i j => hs (e i) (e j))
    (by
      intro i a b
      simp only [pathJoint]
      rw [ite_eq_left (show i.val < p.length by rw [RootedTree.downPath_length]; exact i.isLt)]
      rfl) x
  convert hp using 1
  · congr 1
  · simp only [p,SimpleGraph.Walk.getVert_zero]; congr 1
end BoundedTreewidthL1.ExpandedTree

namespace BoundedTreewidthL1.ExpandedConstruction
open ExpandedParticleLaw ReservationCoupling
attribute [local instance] Classical.decEq Classical.propDecidable
variable {I V ι : Type*} [Fintype I] [Fintype V] [Fintype ι]
lemma ensemble_endpoint (T : SimpleGraph I) (hT : T.IsTree) (parent : I → Option I)
    (horient : ∀ i j, T.Adj i j → parent i = some j ∨ parent j = some i)
    (hanti : ∀ i j, parent i = some j → parent j ≠ some i)
    (M : ℝ) (hM : 0 < M) (hι : 0 < Fintype.card ι)
    (F : I → ι → V → ℝ) (B : I → Finset V)
    (hcover : ∀ v, ∃ i, v ∈ B i) (hrun : ∀ v, (T.induce {i | v ∈ B i}).Preconnected)
    (fresh₁ fresh₂ : I → ι) (C : I → Finset ι)
    (hret : ∀ i j, parent j = some i → ∀ r ∈ C j, F i r = F j r)
    (htrace : ∀ i j, parent j = some i → particleTrace M (F i) (B j) = particleTrace M (F j) (B j))
    (Y Z : I) (y z : V) (hy : y ∈ B Y) (hz : z ∈ B Z) :
    cutDistance (ensemble T parent hanti M F B fresh₁ fresh₂ C)
      (ExpandedTree.assemble (fun i => (B i : Set V)) hcover label) y z =
      ExpandedPathTests.distance M (fun s => F ((RootedTree.downPath T hT Y Z).getVert s))
        (ExpandedTree.pathJoint T (fun i => weight M (F i))
          (joints parent M F B fresh₁ fresh₂ C) (RootedTree.downPath T hT Y Z))
        ((RootedTree.forest T hT Y).depth Z) y z := by
  have hm : 0 < (Fintype.card ι : ℝ)*(2*M) := mul_pos (by exact_mod_cast hι) (by positivity)
  have he : cutDistance (ensemble T parent hanti M F B fresh₁ fresh₂ C)
      (ExpandedTree.assemble (fun i => (B i : Set V)) hcover label) y z =
      ∑ x : I → State ι V, ensemble T parent hanti M F B fresh₁ fresh₂ C x *
        (if label (x Y) y = label (x Z) z then 0 else 1) := by
    unfold cutDistance
    apply Finset.sum_congr rfl
    intro x _
    by_cases hx : ensemble T parent hanti M F B fresh₁ fresh₂ C x = 0
    · simp [hx]
    · rw [ensemble_labels T parent horient hanti M F B hcover hrun fresh₁ fresh₂ C hret htrace x hx Y y hy,
        ensemble_labels T parent horient hanti M F B hcover hrun fresh₁ fresh₂ C hret htrace x hx Z z hz]
      split_ifs <;> simp
  rw [he]
  have hp := ExpandedTree.endpoint_path_product T hT _ hm (fun i => weight M (F i))
    (joints parent M F B fresh₁ fresh₂ C) (joints_symmetric parent hanti M F B fresh₁ fresh₂ C)
    (fun i => weight_nonneg M (F i)) (fun i => weight_total M hM.le (F i))
    (joints_coupling T parent horient hanti M F B fresh₁ fresh₂ C hret htrace) Y Z
    (fun a b => if label a y = label b z then 0 else 1)
  simpa only [ensemble,ExpandedPathTests.distance,SimpleGraph.Walk.getVert_zero] using hp
end BoundedTreewidthL1.ExpandedConstruction

namespace BoundedTreewidthL1.RootedTree
attribute [local instance] Classical.decEq Classical.propDecidable
variable {I : Type*} (T : SimpleGraph I) (hT : T.IsTree) (root X Y : I)
lemma append_path {u v w : I} (p : T.Walk u v) (q : T.Walk v w)
    (hp : p.IsPath) (hq : q.IsPath)
    (hcommon : ∀ z, z ∈ p.support → z ∈ q.support → z = v) : (p.append q).IsPath := by
  rw [SimpleGraph.Walk.isPath_def,SimpleGraph.Walk.support_append,List.nodup_append]
  refine ⟨hp.support_nodup,hq.support_nodup.tail,?_⟩
  intro z hz w hzq heq
  subst w
  have he := hcommon z hz (List.mem_of_mem_tail hzq)
  subst z
  have hn := hq.support_nodup
  rw [← q.cons_tail_support,List.nodup_cons] at hn
  exact hn.1 hzq

/-- The common root prefixes terminate at one finite, deterministic index. -/
lemma exists_join_index : ∃ s : ℕ,
    s ≤ (forest T hT root).depth X ∧ s ≤ (forest T hT root).depth Y ∧
    (downPath T hT root X).getVert s = (downPath T hT root Y).getVert s ∧
    ∀ a b, a ≤ (forest T hT root).depth X → b ≤ (forest T hT root).depth Y →
      (downPath T hT root X).getVert a = (downPath T hT root Y).getVert b → a = b ∧ a ≤ s := by
  let C := (Finset.range ((forest T hT root).depth X+1)).filter (fun a =>
    a ≤ (forest T hT root).depth Y ∧
    (downPath T hT root X).getVert a = (downPath T hT root Y).getVert a)
  have h0 : 0 ∈ C := by simp [C]
  let s := C.max' ⟨0,h0⟩
  have hs : s ∈ C := Finset.max'_mem C ⟨0,h0⟩
  have hsm := Finset.mem_filter.mp hs
  refine ⟨s,by simpa only [Finset.mem_range,Nat.lt_succ_iff] using hsm.1,hsm.2.1,hsm.2.2,?_⟩
  intro a b ha hb he
  have hda := depth_getVert T hT root X a ha
  have hdb := depth_getVert T hT root Y b hb
  have hab : a = b := by rw [he] at hda; omega
  refine ⟨hab,?_⟩
  apply Finset.le_max'
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_range.mpr (by omega),?_⟩
  subst b
  exact ⟨hb,he⟩

/-- At the meet, the two descending arms form exactly the unique Y--X path. -/
lemma path_at_join (s : ℕ)
    (hsx : s ≤ (forest T hT root).depth X) (hsy : s ≤ (forest T hT root).depth Y)
    (hs : (downPath T hT root X).getVert s = (downPath T hT root Y).getVert s)
    (hmax : ∀ a b, a ≤ (forest T hT root).depth X → b ≤ (forest T hT root).depth Y →
      (downPath T hT root X).getVert a = (downPath T hT root Y).getVert b → a = b ∧ a ≤ s) :
    downPath T hT Y X =
      (((downPath T hT root Y).drop s).reverse.copy rfl hs.symm).append
        ((downPath T hT root X).drop s) := by
  apply congrArg Subtype.val ((hT.isAcyclic.subsingleton_path Y X).elim
    ⟨_,downPath_isPath T hT Y X⟩ ⟨_,?_⟩)
  apply append_path
  · simpa only [SimpleGraph.Walk.isPath_copy] using ((downPath_isPath T hT root Y).drop s).reverse
  · exact (downPath_isPath T hT root X).drop s
  · intro z hzy hzx
    simp only [SimpleGraph.Walk.support_copy,SimpleGraph.Walk.support_reverse,List.mem_reverse] at hzy
    obtain ⟨a,hae,hal⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hzx
    obtain ⟨b,hbe,hbl⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hzy
    rw [SimpleGraph.Walk.drop_getVert] at hae hbe
    have ha : s+a ≤ (forest T hT root).depth X := by
      rw [SimpleGraph.Walk.drop_length,downPath_length] at hal; omega
    have hb : s+b ≤ (forest T hT root).depth Y := by
      rw [SimpleGraph.Walk.drop_length,downPath_length] at hbl; omega
    have hab := hmax (s+a) (s+b) ha hb (hae.trans hbe.symm)
    have haz : a = 0 := by omega
    subst a
    simpa only [Nat.add_zero] using hae.symm

lemma join_suffix (s : ℕ)
    (hsx : s ≤ (forest T hT root).depth X) (hsy : s ≤ (forest T hT root).depth Y)
    (hs : (downPath T hT root X).getVert s = (downPath T hT root Y).getVert s)
    (hmax : ∀ a b, a ≤ (forest T hT root).depth X → b ≤ (forest T hT root).depth Y →
      (downPath T hT root X).getVert a = (downPath T hT root Y).getVert b → a = b ∧ a ≤ s)
    (a : ℕ) :
    (downPath T hT Y X).getVert ((forest T hT root).depth Y-s+a) =
      (downPath T hT root X).getVert (s+a) := by
  rw [path_at_join T hT root X Y s hsx hsy hs hmax,
    SimpleGraph.Walk.getVert_append,SimpleGraph.Walk.length_copy,
    SimpleGraph.Walk.length_reverse,SimpleGraph.Walk.drop_length,downPath_length]
  rw [ite_eq_right (by omega),Nat.add_sub_cancel_left,SimpleGraph.Walk.drop_getVert]

lemma join_length (s : ℕ)
    (hsx : s ≤ (forest T hT root).depth X) (hsy : s ≤ (forest T hT root).depth Y)
    (hs : (downPath T hT root X).getVert s = (downPath T hT root Y).getVert s)
    (hmax : ∀ a b, a ≤ (forest T hT root).depth X → b ≤ (forest T hT root).depth Y →
      (downPath T hT root X).getVert a = (downPath T hT root Y).getVert b → a = b ∧ a ≤ s) :
    (forest T hT Y).depth X = (forest T hT root).depth Y-s + ((forest T hT root).depth X-s) := by
  rw [← downPath_length,path_at_join T hT root X Y s hsx hsy hs hmax]
  simp only [SimpleGraph.Walk.length_append,SimpleGraph.Walk.length_copy,
    SimpleGraph.Walk.length_reverse,SimpleGraph.Walk.drop_length,downPath_length]
end BoundedTreewidthL1.RootedTree

namespace BoundedTreewidthL1.ExpandedConstruction
open ExpandedParticleLaw ReservationCoupling ReservedSuffix
attribute [local instance] Classical.decEq Classical.propDecidable
variable {I V ι : Type*} [Fintype I] [Fintype V] [Fintype ι]
/-- Data of the actual constructed ensemble. Retention and trace identities
are verified by the particle recursion, not axioms about its endpoint map. -/
structure TreeData (T : SimpleGraph I) (M : ℝ) where
  parent : I → Option I
  orient : ∀ i j, T.Adj i j → parent i = some j ∨ parent j = some i
  anti : ∀ i j, parent i = some j → parent j ≠ some i
  F : I → ι → V → ℝ
  B : I → Finset V
  cover : ∀ v, ∃ i, v ∈ B i
  run : ∀ v, (T.induce {i | v ∈ B i}).Preconnected
  fresh₁ : I → ι
  fresh₂ : I → ι
  C : I → Finset ι
  retained : ∀ i j, parent j = some i → ∀ r ∈ C j, F i r = F j r
  trace : ∀ i j, parent j = some i → particleTrace M (F i) (B j) = particleTrace M (F j) (B j)
namespace TreeData
variable {T : SimpleGraph I} {M : ℝ} (D : TreeData (V := V) (ι := ι) T M)
noncomputable def dist (y z : V) : ℝ :=
  cutDistance (ensemble T D.parent D.anti M D.F D.B D.fresh₁ D.fresh₂ D.C)
    (ExpandedTree.assemble (fun i => (D.B i : Set V)) D.cover label) y z
noncomputable def chain (hT : T.IsTree) (Y Z : I) :=
  ExpandedTree.pathJoint T (fun i => weight M (D.F i))
    (joints D.parent M D.F D.B D.fresh₁ D.fresh₂ D.C) (RootedTree.downPath T hT Y Z)
lemma chain_coupling (hT : T.IsTree) (Y Z : I) (s : ℕ) :
    IsCoupling (weight M (D.F ((RootedTree.downPath T hT Y Z).getVert s)))
      (weight M (D.F ((RootedTree.downPath T hT Y Z).getVert (s+1)))) (D.chain hT Y Z s) :=
  ExpandedTree.pathJoint_coupling T _ _ (fun i => weight_nonneg M (D.F i))
    (joints_coupling T D.parent D.orient D.anti M D.F D.B D.fresh₁ D.fresh₂ D.C D.retained D.trace) _ s
lemma chain_eq (hT : T.IsTree) (Y Z : I) (s : ℕ)
    (hs : s < (RootedTree.forest T hT Y).depth Z)
    (hp : D.parent ((RootedTree.downPath T hT Y Z).getVert (s+1)) =
      some ((RootedTree.downPath T hT Y Z).getVert s)) :
    D.chain hT Y Z s = kernels M
      (fun s => D.F ((RootedTree.downPath T hT Y Z).getVert s))
      (fun s => D.B ((RootedTree.downPath T hT Y Z).getVert s))
      (fun s => D.fresh₁ ((RootedTree.downPath T hT Y Z).getVert s))
      (fun s => D.fresh₂ ((RootedTree.downPath T hT Y Z).getVert s))
      (fun s => D.C ((RootedTree.downPath T hT Y Z).getVert (s+1))) s := by
  funext a b
  simp only [chain, ExpandedTree.pathJoint, RootedTree.downPath_length, ite_eq_left hs, kernels]
  exact congrFun (congrFun (joints_eq D.parent M D.F D.B D.fresh₁ D.fresh₂ D.C _ _ hp) a) b
lemma height_test (hT : T.IsTree) (hM : 0 < M) (hι : 0 < Fintype.card ι)
    (Y Z : I) (y z : V) (hy : y ∈ D.B Y) (hz : z ∈ D.B Z)
    (t : ℕ) (ht : t < (RootedTree.forest T hT Y).depth Z) (r : ι)
    (hdown : ∀ s, t ≤ s → s < (RootedTree.forest T hT Y).depth Z →
      D.parent ((RootedTree.downPath T hT Y Z).getVert (s+1)) =
        some ((RootedTree.downPath T hT Y Z).getVert s))
    (hfixed : ∀ s, t ≤ s → s ≤ (RootedTree.forest T hT Y).depth Z →
      D.F ((RootedTree.downPath T hT Y Z).getVert s) r = D.F ((RootedTree.downPath T hT Y Z).getVert t) r)
    (hkeep : ∀ s, t ≤ s → s < (RootedTree.forest T hT Y).depth Z →
      r ∈ D.C ((RootedTree.downPath T hT Y Z).getVert (s+1)) ∧
      r ≠ D.fresh₁ ((RootedTree.downPath T hT Y Z).getVert s) ∧
      r ≠ D.fresh₂ ((RootedTree.downPath T hT Y Z).getVert s))
    (hF : ∀ v, -M ≤ D.F ((RootedTree.downPath T hT Y Z).getVert t) r v ∧
      D.F ((RootedTree.downPath T hT Y Z).getVert t) r v ≤ M)
    (ε : ℝ) (hlo : ε ≤ D.F ((RootedTree.downPath T hT Y Z).getVert t) r z+M)
    (hhi : ε ≤ M-D.F ((RootedTree.downPath T hT Y Z).getVert t) r z)
    (hgap : ∀ v ∈ D.B ((RootedTree.downPath T hT Y Z).getVert t),
      ε ≤ |D.F ((RootedTree.downPath T hT Y Z).getVert t) r z-
        D.F ((RootedTree.downPath T hT Y Z).getVert t) r v|) : ε/2 ≤ D.dist y z := by
  rw [dist, ensemble_endpoint T hT D.parent D.orient D.anti M hM hι D.F D.B D.cover D.run
    D.fresh₁ D.fresh₂ D.C D.retained D.trace Y Z y z hy hz]
  let N := (RootedTree.forest T hT Y).depth Z
  have he : N = t+((N-t-1)+1) := by omega
  nth_rw 1 [show (RootedTree.forest T hT Y).depth Z = t+((N-t-1)+1) from he]
  apply ExpandedPathTests.height_test M hM.le _ _ _ _ _ _ (D.chain_coupling hT Y Z)
    t (N-t-1) r
  · intro s hs hs'; exact D.chain_eq hT Y Z s (by omega) (hdown s hs (by omega))
  · intro s hs hs'; exact D.retained _ _ (hdown s hs (by omega))
  · intro s hs hs'; exact D.trace _ _ (hdown s hs (by omega))
  · intro s hs hs'; exact hfixed s hs (by omega)
  · intro s hs hs'; exact hkeep s hs (by omega)
  · exact hF
  · exact hlo
  · exact hhi
  · exact hgap
lemma launch_test (hT : T.IsTree) (hM : 0 < M) (hι : 0 < Fintype.card ι)
    (Y Z : I) (y z : V) (hy : y ∈ D.B Y) (hz : z ∈ D.B Z)
    (t : ℕ) (ht : t < (RootedTree.forest T hT Y).depth Z)
    (hdown : ∀ s, t ≤ s → s < (RootedTree.forest T hT Y).depth Z →
      D.parent ((RootedTree.downPath T hT Y Z).getVert (s+1)) =
        some ((RootedTree.downPath T hT Y Z).getVert s))
    (hij : D.fresh₁ ((RootedTree.downPath T hT Y Z).getVert t) ≠ D.fresh₂ ((RootedTree.downPath T hT Y Z).getVert t))
    (hbag : ∀ v ∈ D.B ((RootedTree.downPath T hT Y Z).getVert t),
      D.F ((RootedTree.downPath T hT Y Z).getVert t) (D.fresh₁ ((RootedTree.downPath T hT Y Z).getVert t)) v =
      D.F ((RootedTree.downPath T hT Y Z).getVert t) (D.fresh₂ ((RootedTree.downPath T hT Y Z).getVert t)) v)
    (hfixed : ∀ r ∈ ({D.fresh₁ ((RootedTree.downPath T hT Y Z).getVert t),
        D.fresh₂ ((RootedTree.downPath T hT Y Z).getVert t)} : Finset ι),
      ∀ s, t ≤ s → s ≤ (RootedTree.forest T hT Y).depth Z →
      D.F ((RootedTree.downPath T hT Y Z).getVert s) r = D.F ((RootedTree.downPath T hT Y Z).getVert t) r)
    (hinit : D.fresh₁ ((RootedTree.downPath T hT Y Z).getVert t) ∈ D.C ((RootedTree.downPath T hT Y Z).getVert (t+1)) ∧
      D.fresh₂ ((RootedTree.downPath T hT Y Z).getVert t) ∈ D.C ((RootedTree.downPath T hT Y Z).getVert (t+1)))
    (hkeep : ∀ r ∈ ({D.fresh₁ ((RootedTree.downPath T hT Y Z).getVert t),
        D.fresh₂ ((RootedTree.downPath T hT Y Z).getVert t)} : Finset ι),
      ∀ s, t+1 ≤ s → s < (RootedTree.forest T hT Y).depth Z →
      r ∈ D.C ((RootedTree.downPath T hT Y Z).getVert (s+1)) ∧
      r ≠ D.fresh₁ ((RootedTree.downPath T hT Y Z).getVert s) ∧
      r ≠ D.fresh₂ ((RootedTree.downPath T hT Y Z).getVert s))
    (hF : ∀ r ∈ ({D.fresh₁ ((RootedTree.downPath T hT Y Z).getVert t),
        D.fresh₂ ((RootedTree.downPath T hT Y Z).getVert t)} : Finset ι), ∀ v,
      -M ≤ D.F ((RootedTree.downPath T hT Y Z).getVert t) r v ∧ D.F ((RootedTree.downPath T hT Y Z).getVert t) r v ≤ M) :
    |D.F ((RootedTree.downPath T hT Y Z).getVert t) (D.fresh₁ ((RootedTree.downPath T hT Y Z).getVert t)) z -
      D.F ((RootedTree.downPath T hT Y Z).getVert t) (D.fresh₂ ((RootedTree.downPath T hT Y Z).getVert t)) z|/2 ≤ D.dist y z := by
  rw [dist, ensemble_endpoint T hT D.parent D.orient D.anti M hM hι D.F D.B D.cover D.run
    D.fresh₁ D.fresh₂ D.C D.retained D.trace Y Z y z hy hz]
  let N := (RootedTree.forest T hT Y).depth Z
  have he : N = t+((N-t-1)+1) := by omega
  nth_rw 1 [show (RootedTree.forest T hT Y).depth Z = t+((N-t-1)+1) from he]
  apply ExpandedPathTests.launch_test M hM.le _
    (fun s => D.B ((RootedTree.downPath T hT Y Z).getVert s)) _ _
    (fun s => D.C ((RootedTree.downPath T hT Y Z).getVert (s+1))) _ (D.chain_coupling hT Y Z)
    t (N-t-1) hij hbag
  · intro s hs hs'; exact D.chain_eq hT Y Z s (by omega) (hdown s hs (by omega))
  · intro s hs hs'; exact D.retained _ _ (hdown s hs (by omega))
  · intro s hs hs'; exact D.trace _ _ (hdown s hs (by omega))
  · intro r hr s hs hs'; exact hfixed r hr s hs (by omega)
  · exact hinit
  · intro r hr s hs hs'; exact hkeep r hr s hs (by omega)
  · exact hF
end TreeData
end BoundedTreewidthL1.ExpandedConstruction

namespace BoundedTreewidthL1.TreeCache
open _root_.OAI.BoundedTreewidthL1.RootedTree AnchorCache ParticleBatch
attribute [local instance] Classical.decEq Classical.propDecidable
variable {I V ι : Type*} (T : SimpleGraph I) (hT : T.IsTree) (root : I)
  (B : I → Finset V) (D : I → V → ℝ) (k : ℕ) (d : V → V → ℝ) (J : ℝ) (X : I)
lemma active_on_path (e a t : ℕ) (he : e ≤ (forest T hT root).depth X)
    (ha : a ∈ inclusiveCache k (bags T hT root B X) d (heights T hT root D X) J e)
    (hat : a ≤ t) (hte : t ≤ e) :
    (downPath T hT root X).getVert a ∈
      active T hT root B D k d J ((downPath T hT root X).getVert t) := by
  rw [active_getVert T hT root B D k d J X t (hte.trans he)]
  exact Finset.mem_image.mpr ⟨a, inclusive_backwards k _ d _ J hat hte ha, rfl⟩
lemma active_self (i : I) : i ∈ active T hT root B D k d J i := by
  unfold active
  apply Finset.mem_image.mpr
  refine ⟨(forest T hT root).depth i, inclusive_self k _ d _ J _, ?_⟩
  rw [← downPath_length]
  exact SimpleGraph.Walk.getVert_length _
lemma path_ne (a t : ℕ) (ha : a ≤ (forest T hT root).depth X)
    (ht : t ≤ (forest T hT root).depth X) (hat : a ≠ t) :
    (downPath T hT root X).getVert a ≠ (downPath T hT root X).getVert t := by
  intro h
  have hd := congrArg (forest T hT root).depth h
  rw [depth_getVert T hT root X a ha,depth_getVert T hT root X t ht] at hd
  exact hat hd
/-- The actual inclusive tree cache transports an anchor's entire function and
its indices throughout every interval up to its last active bag. -/
lemma pair_transport (S : I → (ι → V → ℝ) × (I → ι × ι))
    (hpairs : ∀ i p, (forest T hT root).parent i = some p →
      ∀ a ∈ active T hT root B D k d J i ∩ active T hT root B D k d J p,
      (S i).2 a = (S p).2 a ∧
      (S i).1 ((S i).2 a).1 = (S p).1 ((S p).2 a).1 ∧
      (S i).1 ((S i).2 a).2 = (S p).1 ((S p).2 a).2)
    (e a t : ℕ) (he : e ≤ (forest T hT root).depth X)
    (ha : a ∈ inclusiveCache k (bags T hT root B X) d (heights T hT root D X) J e)
    (hat : a ≤ t) (hte : t ≤ e) :
    let v := (downPath T hT root X).getVert
    (S (v t)).2 (v a) = (S (v a)).2 (v a) ∧
      (S (v t)).1 ((S (v t)).2 (v a)).1 = (S (v a)).1 ((S (v a)).2 (v a)).1 ∧
      (S (v t)).1 ((S (v t)).2 (v a)).2 = (S (v a)).1 ((S (v a)).2 (v a)).2 := by
  dsimp only
  induction t,hat using Nat.le_induction with
  | base => exact ⟨rfl,rfl,rfl⟩
  | succ t hat ih =>
    have htp : t < (forest T hT root).depth X := by omega
    have hact (b : ℕ) (hab : a ≤ b) (hbe : b ≤ e) :=
      active_on_path T hT root B D k d J X e a b he ha hab hbe
    have hp := hpairs _ _ (parent_getVert T hT root X t htp) _
      (Finset.mem_inter.mpr ⟨hact (t+1) (by omega) hte,hact t hat (by omega)⟩)
    obtain ⟨h₁,h₂,h₃⟩ := ih (by omega)
    exact ⟨hp.1.trans h₁,hp.2.1.trans h₂,hp.2.2.trans h₃⟩
end BoundedTreewidthL1.TreeCache

namespace BoundedTreewidthL1.AnchorTreeParticles
open ParticleBatch ParticleSchedule
attribute [local instance] Classical.decEq Classical.propDecidable
variable {V I ι J : Type*} [Fintype V] [Fintype ι] [Nonempty ι]
lemma state_congr_depth (R : RootedForest I) (B : I → Finset V) (A : I → Finset J)
    (g g' : I → J → V → ℝ) (i : I)
    (heq : ∀ j, R.depth j ≤ R.depth i → g j = g' j) :
    state (ι := ι) R B A g i = state R B A g' i := by
  induction hn : R.depth i using Nat.strong_induction_on generalizing i with
  | h n ih =>
    rw [state_eq,state_eq]
    have hpre : (R.parent i).elim (seed (ι := ι) (V := V) (J := J)) (state R B A g) =
        (R.parent i).elim seed (state R B A g') := by
      cases hp : R.parent i with
      | none => rfl
      | some p =>
        simp only [Option.elim_some]
        exact ih (R.depth p) (by rw [← hn]; exact R.decreases _ _ hp) p
          (fun j hj => heq j (hj.trans (R.decreases _ _ hp).le)) rfl
    rw [hpre]
    unfold step
    rw [heq i le_rfl]

lemma predecessor_congr_depth (R : RootedForest I) (B : I → Finset V) (A : I → Finset J)
    (g g' : I → J → V → ℝ) (i : I)
    (heq : ∀ j, R.depth j < R.depth i → g j = g' j) :
    (R.parent i).elim (seed (ι := ι) (V := V) (J := J)) (state R B A g) =
      (R.parent i).elim seed (state R B A g') := by
  cases hp : R.parent i with
  | none => rfl
  | some p =>
    simp only [Option.elim_some]
    apply state_congr_depth
    intro j hj
    exact heq j (lt_of_le_of_lt hj (R.decreases _ _ hp))

lemma singleton_launch (R : RootedForest I) (B : I → Finset V) (A : I → Finset J)
    (g : I → J → V → ℝ) (i : I) (a : J) (hfresh : fresh R A i = {a}) :
    let pre := (R.parent i).elim (seed (ι := ι) (V := V) (J := J)) (state R B A g)
    let p := pickPair (B i) (usedPairs (retained R A i) pre.2) pre.1
    state (ι := ι) R B A g i = (functionPairUpdate pre.1 p.1 p.2 (g i a), Function.update pre.2 a p) := by
  rw [state_eq]
  unfold step
  rw [hfresh,Finset.toList_singleton]
  rfl

/-- The frozen positive particle is an affine function of its OWN fresh noise;
its baseline is computed entirely before that node is processed. -/
lemma singleton_positive (R : RootedForest I) (B : I → Finset V) (A : I → Finset J)
    (g : I → J → V → ℝ) (i : I) (a : J) (hfresh : fresh R A i = {a})
    (hdistinct : ((state (ι := ι) R B A g i).2 a).1 ≠ ((state R B A g i).2 a).2) :
    let pre := (R.parent i).elim (seed (ι := ι) (V := V) (J := J)) (state R B A g)
    let p := pickPair (B i) (usedPairs (retained R A i) pre.2) pre.1
    (state (ι := ι) R B A g i).1 ((state (ι := ι) R B A g i).2 a).1 = fun v => (pre.1 p.1 v + pre.1 p.2 v)/2 + g i a v := by
  have he := singleton_launch (ι := ι) R B A g i a hfresh
  dsimp only at he ⊢
  rw [he] at hdistinct ⊢
  simp only [Function.update_self] at hdistinct ⊢
  funext v
  exact functionPairUpdate_left _ _ _ hdistinct _ v
end BoundedTreewidthL1.AnchorTreeParticles

end OAI
