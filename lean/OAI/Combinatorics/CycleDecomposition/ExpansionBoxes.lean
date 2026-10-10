import OAI.Combinatorics.CycleDecomposition.DepthFirstSearch

namespace OAI

universe cycleUniverse1 cycleUniverse2 cycleUniverse3 cycleUniverse4 cycleUniverse5 cycleUniverse6 cycleUniverse7 cycleUniverse8 cycleUniverse9 cycleUniverse10 cycleUniverse11 cycleUniverse12 cycleUniverse13

section
open Filter Asymptotics Real
open scoped Topology
noncomputable section
open MeasureTheory ProbabilityTheory Finset
section
namespace ErdosGallai.Scale
open Finset SimpleGraph
variable {V : Type cycleUniverse1} [Fintype V] [DecidableEq V]
def avoidGraph (G : SimpleGraph V) (J : Finset V) : SimpleGraph V where
  Adj x y := G.Adj x y ∧ x ∉ J ∧ y ∉ J
  symm := ⟨fun _x _y h => ⟨h.1.symm,h.2.2,h.2.1⟩⟩
  loopless := ⟨fun _x h => G.irrefl h.1⟩

lemma chain_reachable {V : Type cycleUniverse2} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] {H : SimpleGraph V} {L : List V} (hL : L.IsChain H.Adj)
    {x y : V} (hx : x ∈ L) (hy : y ∈ L) : H.Reachable x y := by
  let : Trans H.Reachable H.Reachable H.Reachable := ⟨fun h₁ h₂ => h₁.trans h₂⟩
  cases L with
  | nil => simp at hx
  | cons a L =>
    have hC : (a::L).IsChain H.Reachable := hL.imp (fun _ _ h => h.reachable)
    have ha : ∀ b ∈ a::L, H.Reachable a b := by
      intro b hb
      rcases List.mem_cons.mp hb with rfl|hb
      · exact .refl _
      · exact hC.rel_cons hb
    exact (ha x hx).symm.trans (ha y hy)

theorem connector_exists (G : SimpleGraph V) [DecidableRel G.Adj]
    (α m : ℝ) (hα : 0 ≤ α) (hexp : VertexExpansion G α)
    (X Z J : Finset V) (hX : X.Nonempty) (hZ : Z.Nonempty)
    (hXJ : Disjoint X J) (hZJ : Disjoint Z J)
    (hconnX : ∀ x ∈ X, ∀ y ∈ X, (avoidGraph G J).Reachable x y)
    (_hconnZ : ∀ x ∈ Z, ∀ y ∈ Z, (avoidGraph G J).Reachable x y)
    (hmX : m ≤ (X.card : ℝ)) (hmZ : m ≤ (Z.card : ℝ))
    (hJ : (J.card : ℝ) < α*m) :
    ∃ x ∈ X, ∃ z ∈ Z, (avoidGraph G J).Reachable x z := by
  classical
  by_contra hn
  obtain ⟨x,hx⟩ := hX
  obtain ⟨z,hz⟩ := hZ
  let H := avoidGraph G J
  let A : Finset V := univ.filter (fun v => v ∉ J ∧ H.Reachable x v)
  let B : Finset V := univ \ (J ∪ A)
  have hXA : X ⊆ A := by
    intro y hy
    exact mem_filter.mpr ⟨mem_univ _,
      (Finset.disjoint_left.mp hXJ hy), hconnX x hx y hy⟩
  have hZA : ∀ y ∈ Z, ¬ H.Reachable x y := by
    intro y hy hr
    exact hn ⟨x,hx,y,hy,hr⟩
  have hZB : Z ⊆ B := by
    intro y hy
    simp only [B, Finset.mem_sdiff, mem_univ, true_and, mem_union, not_or]
    refine ⟨Finset.disjoint_left.mp hZJ hy, ?_⟩
    intro ha
    exact hZA y hy (mem_filter.mp ha).2.2
  have hAB : Disjoint A B := by
    apply Finset.disjoint_left.mpr
    intro y ha hb
    exact (mem_sdiff.mp hb).2 (mem_union_right J ha)
  have hc : A.card + B.card ≤ Fintype.card V := by
    rw [← card_union_of_disjoint hAB]
    exact card_le_univ _
  have hboundaryA : externalNeighbors G A ⊆ J := by
    intro v hv
    obtain ⟨_,hva,u,hu,hadj⟩ := mem_filter.mp hv
    by_contra hvj
    obtain ⟨_,huj,hru⟩ := mem_filter.mp hu
    have hadjH : H.Adj u v := ⟨hadj,huj,hvj⟩
    exact hva (mem_filter.mpr ⟨mem_univ _,hvj,hru.trans hadjH.reachable⟩)
  have hboundaryB : externalNeighbors G B ⊆ J := by
    intro v hv
    obtain ⟨_,hvb,u,hu,hadj⟩ := mem_filter.mp hv
    by_contra hvj
    have hva : v ∈ A := by
      by_contra hna
      exact hvb (mem_sdiff.mpr ⟨mem_univ _, by simpa using And.intro hvj hna⟩)
    obtain ⟨_,_,hrv⟩ := mem_filter.mp hva
    have huj : u ∉ J := fun h => (mem_sdiff.mp hu).2 (mem_union_left A h)
    have hadjH : H.Adj v u := ⟨hadj.symm,hvj,huj⟩
    have hua : u ∈ A := mem_filter.mpr ⟨mem_univ _,huj,hrv.trans hadjH.reachable⟩
    exact (mem_sdiff.mp hu).2 (mem_union_right J hua)
  have hcontr (Q : Finset V) (hne : Q.Nonempty) (hsmall : 2*Q.card ≤ Fintype.card V)
      (hm : m ≤ (Q.card : ℝ)) (hb : externalNeighbors G Q ⊆ J) : False := by
    have he := hexp Q hne hsmall
    have hc : ((externalNeighbors G Q).card : ℝ) ≤ J.card := by
      exact_mod_cast card_le_card hb
    have hh := mul_le_mul_of_nonneg_left hm hα
    linarith
  by_cases hsmall : 2*A.card ≤ Fintype.card V
  · exact hcontr A ⟨x,hXA hx⟩ hsmall
      (hmX.trans (by exact_mod_cast card_le_card hXA)) hboundaryA
  · exact hcontr B ⟨z,hZB hz⟩ (by omega)
      (hmZ.trans (by exact_mod_cast card_le_card hZB)) hboundaryB

lemma avoid_support {V : Type cycleUniverse3} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] (G : SimpleGraph V) (J : Finset V) {x z : V}
    (p : (avoidGraph G J).Walk x z) (hx : x ∉ J) :
    ∀ w ∈ p.support, w ∉ J := by
  induction p with
  | nil => simpa using hx
  | @cons u v z hadj p ih =>
    intro w hw
    rcases List.mem_cons.mp hw with rfl|hw
    · exact hx
    · exact ih hadj.2.2 w hw

theorem shortest_set_connector (G : SimpleGraph V) (X Z J : Finset V)
    (hXJ : Disjoint X J)
    (hr : ∃ x ∈ X, ∃ z ∈ Z, (avoidGraph G J).Reachable x z) :
    ∃ x ∈ X, ∃ z ∈ Z, ∃ p : G.Walk x z,
      p.IsPath ∧ ∀ w ∈ p.support, w ∉ J ∧ (w ∈ X → w = x) ∧ (w ∈ Z → w = z) := by
  classical
  let H := avoidGraph G J
  let P : ℕ → Prop := fun k => ∃ x ∈ X, ∃ z ∈ Z, ∃ p : H.Walk x z,
    p.IsPath ∧ p.length = k
  have hP : ∃ k, P k := by
    obtain ⟨x,hx,z,hz,hr⟩ := hr
    obtain ⟨p,hp⟩ := hr.exists_isPath
    exact ⟨p.length,x,hx,z,hz,p,hp,rfl⟩
  obtain ⟨x,hx,z,hz,p,hp,hplen⟩ := Nat.find_spec hP
  have hmin : ∀ a ∈ X, ∀ b ∈ Z, ∀ q : H.Walk a b, q.IsPath → p.length ≤ q.length := by
    intro a ha b hb q hq
    rw [hplen]
    exact Nat.find_min' hP ⟨a,ha,b,hb,q,hq,rfl⟩
  have hsub : H ≤ G := fun _ _ h => h.1
  refine ⟨x,hx,z,hz,p.mapLe hsub,(hp.mapLe hsub),?_⟩
  intro w hw
  rw [Walk.support_mapLe_eq_support] at hw
  refine ⟨avoid_support G J p (Finset.disjoint_left.mp hXJ hx) w hw,?_,?_⟩
  · intro hwX
    by_contra hne
    have hlt := Walk.length_dropUntil_lt_length hw hne
    have hle := hmin w hwX z hz (p.dropUntil w hw) (hp.dropUntil hw)
    omega
  · intro hwZ
    by_contra hne
    have hlt := Walk.length_takeUntil_lt_length hw hne
    have hle := hmin x hx w hwZ (p.takeUntil w hw) (hp.takeUntil hw)
    omega

lemma path_cons_append {V : Type cycleUniverse4} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] (G : SimpleGraph V) (x z : V) (B : List V)
    (hC : (x :: (B ++ [z])).IsChain G.Adj) :
    ∃ p : G.Walk x z, p.support = x :: (B ++ [z]) := by
  let L := x :: (B ++ [z])
  have hn : L ≠ [] := by simp [L]
  let p := Walk.ofSupport L hn hC
  have hx : L.head hn = x := rfl
  have hz : L.getLast hn = z := by simp [L]
  exact ⟨p.copy hx hz, by
    change ((Walk.ofSupport L hn hC).copy hx hz).support = L
    rw [Walk.support_copy, Walk.support_ofSupport]⟩

theorem cycle_across_middle (G : SimpleGraph V) (X J Z : List V)
    (hnd : (X ++ J ++ Z).Nodup) (hC : (X ++ J ++ Z).IsChain G.Adj)
    (hj : 1 ≤ J.length)
    (hc : ∃ x ∈ X, ∃ z ∈ Z, ∃ q : G.Walk x z,
      q.IsPath ∧ ∀ w ∈ q.support, w ∉ J ∧ (w ∈ X → w = x) ∧ (w ∈ Z → w = z)) :
    ∃ a : V, ∃ c : G.Walk a a, c.IsCycle ∧ J.length + 2 ≤ c.length := by
  obtain ⟨x,hx,z,hz,q,hq,havoid⟩ := hc
  obtain ⟨A,B,hX⟩ := List.mem_iff_append.mp hx
  obtain ⟨C,D,hZ⟩ := List.mem_iff_append.mp hz
  let M := x :: ((B ++ J ++ C) ++ [z])
  have heq : X ++ J ++ Z = A ++ (M ++ D) := by
    simp [hX,hZ,M,List.append_assoc]
  have hMC : M.IsChain G.Adj := by
    rw [heq] at hC
    exact hC.right_of_append.left_of_append
  have hMN : M.Nodup := by
    rw [heq] at hnd
    exact (List.nodup_append.mp (List.nodup_append.mp hnd).2.1).1
  obtain ⟨p,hpS⟩ := path_cons_append G x z (B ++ J ++ C) hMC
  have hp : p.IsPath := by
    rw [Walk.isPath_def,hpS]
    exact hMN
  have hlen : J.length + 1 ≤ p.length := by
    have ht := p.length_support
    rw [hpS] at ht
    simp only [List.length_cons,List.length_append] at ht
    omega
  have hxs : x ∉ p.support.tail := by
    have hn := hp.support_nodup
    rw [← p.cons_tail_support] at hn
    exact (List.nodup_cons.mp hn).1
  have hzs : z ∉ q.reverse.support.tail := by
    have hn := hq.reverse.support_nodup
    rw [← q.reverse.cons_tail_support] at hn
    exact (List.nodup_cons.mp hn).1
  have hdis : p.support.tail.Disjoint q.reverse.support.tail := by
    apply List.disjoint_left.mpr
    intro w hwP hwQ
    have hwq : w ∈ q.support := by
      simpa using List.mem_of_mem_tail hwQ
    obtain ⟨hwJ,hwX,hwZ⟩ := havoid w hwq
    have hwp : w ∈ X ++ J ++ Z := by
      rw [heq]
      have : w ∈ M := by
        change w ∈ x :: ((B ++ J ++ C) ++ [z])
        rw [← hpS]
        exact List.mem_of_mem_tail hwP
      simp only [List.mem_append]
      exact Or.inr (Or.inl this)
    simp only [List.mem_append] at hwp
    rcases hwp with (hw|hw)|hw
    · exact hxs (hwX hw ▸ hwP)
    · exact hwJ hw
    · exact hzs (hwZ hw ▸ hwQ)
  have hxz : x ≠ z := by
    intro he
    have hz : z ∈ p.support.tail := by simp [hpS]
    exact hxs (he ▸ hz)
  have hqlen : 1 ≤ q.length := by
    by_contra hh
    have : q.length = 0 := by omega
    exact hxz (Walk.eq_of_length_eq_zero this)
  refine ⟨x,p.append q.reverse,hp.isCycle_append hq.reverse hdis (Or.inl (by omega)),?_⟩
  simp only [Walk.length_append,Walk.length_reverse]
  omega

theorem long_cycle_of_vertex_expansion (G : SimpleGraph V) [DecidableRel G.Adj]
    (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (hexp : VertexExpansion G α)
    (hq : 1 ≤ α^2 * Fintype.card V / 100) :
    ∃ a : V, ∃ c : G.Walk a a, c.IsCycle ∧
      α^2 * Fintype.card V / 100 < (c.length : ℝ) := by
  classical
  obtain ⟨L,hnd,hchain,hL⟩ := exists_long_stack G α hα1 hexp
  let q := α^2 * Fintype.card V / 100
  let j := ⌊q⌋₊
  have hq0 : 0 ≤ q := by dsimp [q]; linarith
  have hjle : (j : ℝ) ≤ q := Nat.floor_le hq0
  have hjlt : q < (j : ℝ)+1 := Nat.lt_floor_add_one q
  have hj1 : 1 ≤ j := by exact (Nat.le_floor_iff hq0).mpr (by simpa [q] using hq)
  have hL0 : (0 : ℝ) ≤ L.length := Nat.cast_nonneg _
  have hu0 : (0 : ℝ) ≤ Fintype.card V := Nat.cast_nonneg _
  have haa : α^2 ≤ α := by nlinarith
  have hqq : 2*q ≤ α * Fintype.card V / 6 := by
    have hh := mul_le_mul_of_nonneg_right haa hu0
    dsimp [q]
    nlinarith [mul_nonneg (le_of_lt hα) hu0]
  have hround : 2*(j+1) ≤ L.length := by
    have hroundR : 2*((j:ℝ)+1) ≤ (L.length:ℝ) := by
      have hq1 : 1 ≤ q := hq
      linarith
    exact_mod_cast hroundR
  let k := (L.length-j)/2
  let X := L.take k
  let J := (L.drop k).take j
  let Z := (L.drop k).drop j
  have heq : L = X ++ J ++ Z := by
    dsimp [X,J,Z]
    rw [List.append_assoc,List.take_append_drop,List.take_append_drop]
  have hk : k ≤ L.length := by dsimp [k]; omega
  have hjdrop : j ≤ (L.drop k).length := by simp only [List.length_drop]; dsimp [k]; omega
  have hXlen : X.length = k := by simp [X,List.length_take, min_eq_left hk]
  have hJlen : J.length = j := by dsimp [J]; rw [List.length_take, min_eq_left hjdrop]
  have hZlen : Z.length = L.length-k-j := by simp only [Z,List.length_drop]
  have houterX : L.length ≤ 4*X.length := by rw [hXlen]; dsimp [k]; omega
  have houterZ : L.length ≤ 4*Z.length := by rw [hZlen]; dsimp [k]; omega
  rw [heq] at hnd hchain
  have hnX : X.Nodup := (List.nodup_append.mp (List.nodup_append.mp hnd).1).1
  have hnJ : J.Nodup := (List.nodup_append.mp (List.nodup_append.mp hnd).1).2.1
  have hnZ : Z.Nodup := (List.nodup_append.mp hnd).2.1
  have hXJ : X.Disjoint J := (List.nodup_append.mp hnd).1.disjoint
  have hZJ : Z.Disjoint J := by
    have hd := hnd.disjoint
    exact List.disjoint_left.mpr (fun w hwz hwj =>
      List.disjoint_left.mp hd (List.mem_append_right X hwj) hwz)
  have hXJf : Disjoint X.toFinset J.toFinset := by
    apply Finset.disjoint_left.mpr
    intro w hw hJw
    exact List.disjoint_left.mp hXJ (List.mem_toFinset.mp hw) (List.mem_toFinset.mp hJw)
  have hZJf : Disjoint Z.toFinset J.toFinset := by
    apply Finset.disjoint_left.mpr
    intro w hw hJw
    exact List.disjoint_left.mp hZJ (List.mem_toFinset.mp hw) (List.mem_toFinset.mp hJw)
  have hconnX : ∀ x ∈ X.toFinset, ∀ y ∈ X.toFinset,
      (avoidGraph G J.toFinset).Reachable x y := by
    intro x hx y hy
    apply chain_reachable (L := X) _ (List.mem_toFinset.mp hx) (List.mem_toFinset.mp hy)
    apply hchain.left_of_append.left_of_append.imp_of_mem_imp
    intro a b ha hb hab
    exact ⟨hab,fun hj => List.disjoint_left.mp hXJ ha (List.mem_toFinset.mp hj),
      fun hj => List.disjoint_left.mp hXJ hb (List.mem_toFinset.mp hj)⟩
  have hconnZ : ∀ x ∈ Z.toFinset, ∀ y ∈ Z.toFinset,
      (avoidGraph G J.toFinset).Reachable x y := by
    intro x hx y hy
    apply chain_reachable (L := Z) _ (List.mem_toFinset.mp hx) (List.mem_toFinset.mp hy)
    apply hchain.right_of_append.imp_of_mem_imp
    intro a b ha hb hab
    exact ⟨hab,fun hj => List.disjoint_left.mp hZJ ha (List.mem_toFinset.mp hj),
      fun hj => List.disjoint_left.mp hZJ hb (List.mem_toFinset.mp hj)⟩
  have hXne : X.toFinset.Nonempty := by
    rw [← Finset.card_pos,List.toFinset_card_of_nodup hnX]
    omega
  have hZne : Z.toFinset.Nonempty := by
    rw [← Finset.card_pos,List.toFinset_card_of_nodup hnZ]
    omega
  have hmX : (L.length : ℝ)/4 ≤ X.toFinset.card := by
    rw [List.toFinset_card_of_nodup hnX]
    have : (L.length : ℝ) ≤ 4*(X.length:ℝ) := by exact_mod_cast houterX
    linarith
  have hmZ : (L.length : ℝ)/4 ≤ Z.toFinset.card := by
    rw [List.toFinset_card_of_nodup hnZ]
    have : (L.length : ℝ) ≤ 4*(Z.length:ℝ) := by exact_mod_cast houterZ
    linarith
  have hsmallJ : (J.toFinset.card : ℝ) < α*((L.length:ℝ)/4) := by
    rw [List.toFinset_card_of_nodup hnJ,hJlen]
    have hmul := mul_le_mul_of_nonneg_left hL (le_of_lt hα)
    dsimp [q] at hjle
    nlinarith
  obtain ⟨x,hx,z,hz,p,hp,hpavoid⟩ := shortest_set_connector G X.toFinset Z.toFinset J.toFinset hXJf
    (connector_exists G α ((L.length:ℝ)/4) (le_of_lt hα) hexp
      X.toFinset Z.toFinset J.toFinset hXne hZne hXJf hZJf hconnX hconnZ hmX hmZ hsmallJ)
  obtain ⟨a,c,hc,hlen⟩ := cycle_across_middle G X J Z hnd hchain (by omega)
    ⟨x,List.mem_toFinset.mp hx,z,List.mem_toFinset.mp hz,p,hp,by simpa using hpavoid⟩
  refine ⟨a,c,hc,?_⟩
  rw [hJlen] at hlen
  have hlR : (j:ℝ)+2 ≤ c.length := by exact_mod_cast hlen
  change q < (c.length:ℝ)
  linarith

end ErdosGallai.Scale

namespace ErdosGallai.Scale
open Classical
end ErdosGallai.Scale
namespace ErdosGallai.Scale
open Finset SimpleGraph Classical
variable {V : Type cycleUniverse5} [Fintype V] [DecidableEq V]

def SupportedOn (G : SimpleGraph V) (A : Finset V) : Prop :=
  ∀ ⦃x y⦄, G.Adj x y → x ∈ A ∧ y ∈ A

structure AssignedPiece (V : Type cycleUniverse6) [DecidableEq V] where
  vertices : Finset V
  graph : SimpleGraph V
  supported : SupportedOn graph vertices

noncomputable def restrictGraph (G : SimpleGraph V) (A : Finset V) : SimpleGraph V where
  Adj x y := G.Adj x y ∧ x ∈ A ∧ y ∈ A
  symm := ⟨fun _ _ h => ⟨h.1.symm,h.2.2,h.2.1⟩⟩
  loopless := ⟨fun _ h => G.irrefl h.1⟩

noncomputable def crossingGraph (G : SimpleGraph V) (A B : Finset V) : SimpleGraph V where
  Adj x y := G.Adj x y ∧ ((x ∈ A ∧ y ∈ B) ∨ (x ∈ B ∧ y ∈ A))
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.elim (fun h => Or.inr ⟨h.2,h.1⟩)
    (fun h => Or.inl ⟨h.2,h.1⟩)⟩⟩
  loopless := ⟨fun _ h => G.irrefl h.1⟩

noncomputable def edgeOccurrences (L : List (SimpleGraph V)) (x y : V) : ℕ := by
  classical
  exact L.countP (fun H => H.Adj x y)

def GraphPartition (G : SimpleGraph V) (L : List (SimpleGraph V)) : Prop :=
  ∀ x y, edgeOccurrences L x y = if G.Adj x y then 1 else 0

noncomputable def edgeCount (G : SimpleGraph V) : ℕ := by
  classical
  exact G.edgeFinset.card

noncomputable def cutCount (G : SimpleGraph V) (A B : Finset V) : ℕ := by
  classical
  exact (G.interedges A B).card

def CutExpansionOn (G : SimpleGraph V) (A : Finset V) (h : ℝ) : Prop :=
  ∀ U ⊆ A, h * min (U.card : ℝ) ((A \ U).card : ℝ) ≤ cutCount G U (A \ U)

@[simp] lemma edgeOccurrences_nil {V : Type cycleUniverse7} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] (x y : V) : edgeOccurrences [] x y = 0 := by
  classical
  simp [edgeOccurrences]
@[simp] lemma edgeOccurrences_cons {V : Type cycleUniverse8} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] (H : SimpleGraph V) (L) (x y : V) :
    edgeOccurrences (H::L) x y = (if H.Adj x y then 1 else 0) + edgeOccurrences L x y := by
  classical
  simp [edgeOccurrences, List.countP_cons, Nat.add_comm]
@[simp] lemma edgeOccurrences_append {V : Type cycleUniverse9} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] (L M : List (SimpleGraph V)) (x y : V) :
    edgeOccurrences (L++M) x y = edgeOccurrences L x y + edgeOccurrences M x y := by
  classical
  simp [edgeOccurrences]

lemma restrictGraph_le {V : Type cycleUniverse10} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] (G : SimpleGraph V) (A : Finset V) : restrictGraph G A ≤ G :=
  fun _ _ h => h.1
lemma restrictGraph_supported {V : Type cycleUniverse11} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] (G : SimpleGraph V) (A : Finset V) :
    SupportedOn (restrictGraph G A) A := fun _ _ h => h.2

lemma partition_member_le {V : Type cycleUniverse12} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] {G : SimpleGraph V} {L : List (SimpleGraph V)}
    (h : GraphPartition G L) {H : SimpleGraph V} (hH : H ∈ L) : H ≤ G := by
  classical
  intro x y hxy
  by_contra hn
  have hc := h x y
  simp only [hn, ite_false] at hc
  have hp : 0 < edgeOccurrences L x y := by
    simpa [edgeOccurrences, List.countP_pos_iff] using (show ∃ K ∈ L, K.Adj x y from ⟨H,hH,hxy⟩)
  omega

@[simp] lemma edgeCount_bot {V : Type cycleUniverse13} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] : edgeCount (⊥ : SimpleGraph V) = 0 := by
  classical
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro e he
  simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.edgeSet_bot, Set.mem_empty_iff_false] at he

open Real

noncomputable def splitPotential (T x : ℝ) : ℝ :=
  1 + 1 / logb 2 (T/2) - 1 / logb 2 (max x (T/2))

lemma logb_four_thirds : (1/4:ℝ) ≤ logb 2 (4/3) := by
  have h := Real.logb_le_logb_of_le (b:=2) (x:=2) (y:=(4/3:ℝ)^4)
    (by norm_num) (by norm_num) (by norm_num)
  rw [Real.logb_pow] at h
  norm_num only [Real.logb_self_eq_one, Nat.cast_ofNat] at h
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  nlinarith

lemma splitPotential_bounds (T x : ℝ) (hT : 4 ≤ T) :
    1 ≤ splitPotential T x ∧ splitPotential T x ≤ 2 := by
  have hbase : 1 ≤ logb 2 (T/2) := by
    have hh := Real.logb_le_logb_of_le (b:=2) (x:=2) (y:=T/2)
      (by norm_num) (by norm_num) (by linarith)
    norm_num [Real.logb] at hh
    exact hh
  have hlog := Real.logb_le_logb_of_le (b:=2) (x:=T/2) (y:=max x (T/2))
    (by norm_num) (by linarith) (le_max_right _ _)
  have hsmall : 0 < logb 2 (T/2) := by linarith
  have hbig : 0 < logb 2 (max x (T/2)) := by linarith
  have hrecip : 1 / logb 2 (max x (T/2)) ≤ 1 / logb 2 (T/2) :=
    one_div_le_one_div_of_le hsmall hlog
  have hrecipone : 1/logb 2 (T/2) ≤ 1 := (div_le_one hsmall).mpr hbase
  dsimp [splitPotential]
  constructor
  · linarith
  · linarith [one_div_pos.mpr hbig]

lemma splitPotential_monotone (T : ℝ) (hT : 4 ≤ T) : Monotone (splitPotential T) := by
  intro x y hxy
  have hpos : 0 < T/2 := by linarith
  have hlogx : 0 < logb 2 (max x (T/2)) :=
    Real.logb_pos (by norm_num) (lt_of_lt_of_le (by linarith : 1 < T/2) (le_max_right _ _))
  have hlog := Real.logb_le_logb_of_le (b:=2) (by norm_num)
    (lt_of_lt_of_le hpos (le_max_right x (T/2))) (max_le_max hxy le_rfl)
  have hi := one_div_le_one_div_of_le hlogx hlog
  dsimp [splitPotential]
  linarith

lemma split_potential_decrement (T u u₁ : ℝ) (hT : 4 ≤ T) (hu : T < u)
    (h₁ : u₁ ≤ 3*u/4) :
    (1/4:ℝ)/(logb 2 u)^2 ≤ splitPotential T u - splitPotential T u₁ := by
  let M := max u₁ (T/2)
  have hu0 : 0 < u := by linarith
  have hM0 : 0 < M := lt_of_lt_of_le (by linarith : 0 < T/2) (le_max_right _ _)
  have hMu : M ≤ 3*u/4 := max_le h₁ (by linarith)
  have hMlt : M ≤ u := by linarith
  have hLu : 0 < logb 2 u := Real.logb_pos (by norm_num) (by linarith)
  have hLM : 0 < logb 2 M := Real.logb_pos (by norm_num)
    (lt_of_lt_of_le (by linarith : 1 < T/2) (le_max_right _ _))
  have hlle : logb 2 M ≤ logb 2 u :=
    Real.logb_le_logb_of_le (by norm_num) hM0 hMlt
  have hquot : (4/3:ℝ) ≤ u/M := (le_div_iff₀ hM0).mpr (by linarith)
  have hlogq := Real.logb_le_logb_of_le (b:=2) (x:=4/3) (y:=u/M)
    (by norm_num) (by norm_num) hquot
  rw [Real.logb_div hu0.ne' hM0.ne'] at hlogq
  have hgap : (1/4:ℝ) ≤ logb 2 u - logb 2 M := logb_four_thirds.trans hlogq
  have hmax : max u (T/2) = u := max_eq_left (by linarith)
  dsimp [splitPotential]
  rw [hmax]
  change (1/4:ℝ)/(logb 2 u)^2 ≤
    (1+1/logb 2 (T/2)-1/logb 2 u) - (1+1/logb 2 (T/2)-1/logb 2 M)
  have hid : (1+1/logb 2 (T/2)-1/logb 2 u) - (1+1/logb 2 (T/2)-1/logb 2 M) =
      (logb 2 u-logb 2 M)/(logb 2 M*logb 2 u) := by field_simp; ring
  rw [hid]
  apply (div_le_div_iff₀ (sq_pos_of_pos hLu) (mul_pos hLM hLu)).mpr
  have hm := mul_le_mul_of_nonneg_right hlle hLu.le
  nlinarith [sq_nonneg (logb 2 u)]

lemma split_potential_subadditive (T u u₁ u₂ : ℝ) (hT : 4 ≤ T) (hu : T < u)
    (hu₁ : 0 ≤ u₁) (hu₂ : 0 ≤ u₂) (h₁ : u₁ ≤ 3*u/4) (h₂ : u₂ ≤ u)
    (hsum : u₁+u₂ ≤ u+(1/32:ℝ)*u₁/(logb 2 u)^2) :
    u₁*splitPotential T u₁ + u₂*splitPotential T u₂ ≤ u*splitPotential T u := by
  have hdec := split_potential_decrement T u u₁ hT hu h₁
  have hmono := splitPotential_monotone T hT h₂
  obtain ⟨hfpos,hfhi⟩ := splitPotential_bounds T u hT
  have h₁cost := mul_le_mul_of_nonneg_left hdec hu₁
  have h₂cost := mul_le_mul_of_nonneg_left hmono hu₂
  have hLu : 0 < logb 2 u := Real.logb_pos (by norm_num) (by linarith)
  have hden : 0 < (logb 2 u)^2 := sq_pos_of_pos hLu
  have hsumcost := mul_le_mul_of_nonneg_right hsum (by linarith : 0 ≤ splitPotential T u)
  have hwt : 0 ≤ u₁/(logb 2 u)^2 := div_nonneg hu₁ hden.le
  have hratio : u₁*((1/4:ℝ)/(logb 2 u)^2) = (1/4:ℝ)*(u₁/(logb 2 u)^2) := by ring
  have hratio2 : ((1/32:ℝ)*u₁/(logb 2 u)^2)*splitPotential T u =
      (1/32:ℝ)*(u₁/(logb 2 u)^2)*splitPotential T u := by ring
  simp only [add_mul] at hsumcost
  rw [hratio2] at hsumcost
  rw [hratio] at h₁cost
  nlinarith

noncomputable def externalOn (G : SimpleGraph V) (U : Finset V) : Finset V :=
  univ.filter (fun v => v ∉ U ∧ ∃ u ∈ U, G.Adj u v)

lemma externalOn_subset {G : SimpleGraph V} {A U : Finset V} (hG : SupportedOn G A) :
    externalOn G U ⊆ A := by
  intro x hx
  obtain ⟨u,hu,hadj⟩ := (Finset.mem_filter.mp hx).2.2
  exact (hG hadj).2

lemma externalOn_disjoint (G : SimpleGraph V) (U : Finset V) :
    Disjoint U (externalOn G U) := by
  apply Finset.disjoint_left.mpr
  intro x hx hn
  exact (Finset.mem_filter.mp hn).2.1 hx

lemma overlap_child_supported {G : SimpleGraph V} {A U : Finset V}
    (hG : SupportedOn G A) (_hU : U ⊆ A) :
    SupportedOn (G \ restrictGraph G (U ∪ externalOn G U)) (A\U) := by
  intro x y hxy
  obtain ⟨hx,hy⟩ := hG hxy.1
  have hb (x y : V) (hxy : G.Adj x y) (hx : x ∈ U) : y ∈ U ∪ externalOn G U := by
    by_cases hy : y ∈ U
    · exact Finset.mem_union_left _ hy
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hy,x,hx,hxy⟩)
  constructor
  · refine Finset.mem_sdiff.mpr ⟨hx,fun hxU => ?_⟩
    exact hxy.2 ⟨hxy.1,Finset.mem_union_left _ hxU,hb x y hxy.1 hxU⟩
  · refine Finset.mem_sdiff.mpr ⟨hy,fun hyU => ?_⟩
    exact hxy.2 ⟨hxy.1,hb y x hxy.1.symm hyU,Finset.mem_union_left _ hyU⟩

lemma overlap_child_sizes {G : SimpleGraph V} {A U : Finset V} {T : ℝ}
    (hT : 4 ≤ T) (hlarge : T < (A.card : ℝ)) (hU : U ⊆ A)
    (hne : U.Nonempty) (hhalf : 2*U.card ≤ A.card)
    (hsparse : ((externalOn G U).card : ℝ) < (1/32:ℝ)*U.card/(logb 2 A.card)^2) :
    (U ∪ externalOn G U).Nonempty ∧ (A\U).Nonempty ∧
    ((U ∪ externalOn G U).card : ℝ) ≤ 3*A.card/4 ∧
    (A\U).card < A.card ∧
    ((U ∪ externalOn G U).card : ℝ) + (A\U).card ≤
      A.card+(1/32:ℝ)*(U ∪ externalOn G U).card/(logb 2 A.card)^2 := by
  have hu : 0 < U.card := hne.card_pos
  have hlog : 1 ≤ logb 2 (A.card : ℝ) := by
    have h := Real.logb_le_logb_of_le (b:=2) (x:=2) (y:=A.card)
      (by norm_num) (by norm_num) (by linarith)
    norm_num [Real.logb] at h
    exact h
  have hd : 0 < (logb 2 (A.card : ℝ))^2 := by positivity
  have hquot : (1/32:ℝ)/(logb 2 (A.card : ℝ))^2 ≤ 1/2 := by
    apply (div_le_iff₀ hd).mpr
    nlinarith [sq_nonneg (logb 2 (A.card : ℝ)-1)]
  have hsmall : ((externalOn G U).card : ℝ) < (U.card : ℝ)/2 := by
    have hm := mul_le_mul_of_nonneg_right hquot (Nat.cast_nonneg U.card)
    have hid : (1/32:ℝ)/(logb 2 (A.card : ℝ))^2 * U.card =
        (1/32:ℝ)*U.card/(logb 2 (A.card : ℝ))^2 := by ring
    rw [hid] at hm
    linarith
  have hcard₁ := Finset.card_union_of_disjoint (externalOn_disjoint G U)
  have hcard₂ := Finset.card_sdiff_add_card_eq_card hU
  have hcard₁R : ((U ∪ externalOn G U).card : ℝ) = U.card+(externalOn G U).card := by
    exact_mod_cast hcard₁
  have hcard₂R : ((A\U).card : ℝ) + U.card = A.card := by exact_mod_cast hcard₂
  have hhalfR : 2*(U.card : ℝ) ≤ A.card := by exact_mod_cast hhalf
  have hmon : (1/32:ℝ)*U.card/(logb 2 A.card)^2 ≤
      (1/32:ℝ)*(U ∪ externalOn G U).card/(logb 2 A.card)^2 := by
    gcongr
    exact Finset.subset_union_left
  refine ⟨hne.mono Finset.subset_union_left,?_,?_,?_,?_⟩
  · exact Finset.card_pos.mp (by omega)
  · linarith
  · omega
  · linarith

lemma partition_split_append {G K : SimpleGraph V} {L M : List (SimpleGraph V)}
    (hle : K ≤ G) (hL : GraphPartition K L) (hM : GraphPartition (G\K) M) :
    GraphPartition G (L++M) := by
  intro x y
  have h₁ := hL x y
  have h₂ := hM x y
  have hk := @hle x y
  simp only [edgeOccurrences_append,SimpleGraph.sdiff_adj] at h₂ ⊢
  by_cases hK : K.Adj x y <;> by_cases hG : G.Adj x y <;> simp_all

theorem box_recursion (G : SimpleGraph V) (A : Finset V) (T : ℝ)
    (hT : 4 ≤ T) (hA : A.Nonempty) (hG : SupportedOn G A)
    (hsplit : ∀ B ⊆ A, ∀ H : SimpleGraph V, H ≤ G → SupportedOn H B → T < (B.card : ℝ) →
      ∃ U ⊆ B, U.Nonempty ∧ 2*U.card ≤ B.card ∧
        ((externalOn H U).card : ℝ) < (1/32:ℝ)*U.card/(logb 2 B.card)^2) :
    ∃ L : List (AssignedPiece V),
      (∀ P ∈ L, P.vertices ⊆ A ∧ P.vertices.Nonempty ∧ (P.vertices.card : ℝ) ≤ T) ∧
      (∀ x ∈ A, ∃ P ∈ L, x ∈ P.vertices) ∧
      GraphPartition G (L.map AssignedPiece.graph) ∧
      (L.map (fun P => (P.vertices.card : ℝ)*splitPotential T P.vertices.card)).sum ≤
        (A.card : ℝ)*splitPotential T A.card := by
  classical
  induction hn : A.card using Nat.strong_induction_on generalizing A G with
  | h n ih =>
    by_cases hsmall : (A.card : ℝ) ≤ T
    · let P : AssignedPiece V := ⟨A,G,hG⟩
      refine ⟨[P],?_,?_,?_,?_⟩
      · intro Q hQ; simp only [List.mem_singleton] at hQ; subst Q
        exact ⟨Finset.Subset.refl _,hA,hsmall⟩
      · intro x hx; exact ⟨P,by simp,hx⟩
      · intro x y; simp [P]
      · simp [P,← hn]
    · have hlarge : T < (A.card : ℝ) := lt_of_not_ge hsmall
      obtain ⟨U,hU,hne,hhalf,hsparse⟩ := hsplit A (Finset.Subset.refl _) G le_rfl hG hlarge
      let B := externalOn G U
      let A₁ := U ∪ B
      let A₂ := A\U
      let G₁ := restrictGraph G A₁
      let G₂ := G\G₁
      have hA₁ : A₁ ⊆ A := Finset.union_subset hU (externalOn_subset hG)
      have hA₂ : A₂ ⊆ A := Finset.sdiff_subset
      have hG₁ : G₁ ≤ G := restrictGraph_le G A₁
      have hG₂ : G₂ ≤ G := sdiff_le
      have hs₁ : SupportedOn G₁ A₁ := restrictGraph_supported G A₁
      have hs₂ : SupportedOn G₂ A₂ := overlap_child_supported hG hU
      obtain ⟨hn₁,hn₂,hsize₁,hsize₂,hsum⟩ := overlap_child_sizes hT hlarge hU hne hhalf hsparse
      have hlt₁ : A₁.card < n := by
        have hn0 : (0 : ℝ) < A.card := by linarith
        have hlt : (A₁.card : ℝ) < A.card := lt_of_le_of_lt hsize₁ (by linarith)
        exact hn ▸ (Nat.cast_lt.mp hlt)
      have hlt₂ : A₂.card < n := hn ▸ hsize₂
      have subprem (D : Finset V) (hD : D ⊆ A) (K : SimpleGraph V) (hK : K ≤ G) :
          ∀ C ⊆ D, ∀ H : SimpleGraph V, H ≤ K → SupportedOn H C → T < (C.card : ℝ) →
            ∃ U ⊆ C, U.Nonempty ∧ 2*U.card ≤ C.card ∧
              ((externalOn H U).card : ℝ) < (1/32:ℝ)*U.card/(logb 2 C.card)^2 := by
        intro C hC H hH hs hlarge
        exact hsplit C (hC.trans hD) H (hH.trans hK) hs hlarge
      obtain ⟨L,hL,hcovL,hpartL,hcostL⟩ := ih _ hlt₁ G₁ A₁ hn₁ hs₁
        (subprem A₁ hA₁ G₁ hG₁) rfl
      obtain ⟨M,hM,hcovM,hpartM,hcostM⟩ := ih _ hlt₂ G₂ A₂ hn₂ hs₂
        (subprem A₂ hA₂ G₂ hG₂) rfl
      refine ⟨L++M,?_,?_,?_,?_⟩
      · intro P hP
        rcases List.mem_append.mp hP with hP | hP
        · obtain ⟨hsub,hne,hbound⟩ := hL P hP; exact ⟨hsub.trans hA₁,hne,hbound⟩
        · obtain ⟨hsub,hne,hbound⟩ := hM P hP; exact ⟨hsub.trans hA₂,hne,hbound⟩
      · intro x hx
        by_cases hxU : x ∈ U
        · obtain ⟨P,hP,hxP⟩ := hcovL x (Finset.mem_union_left _ hxU)
          exact ⟨P,List.mem_append_left _ hP,hxP⟩
        · obtain ⟨P,hP,hxP⟩ := hcovM x (Finset.mem_sdiff.mpr ⟨hx,hxU⟩)
          exact ⟨P,List.mem_append_right _ hP,hxP⟩
      · simpa only [List.map_append] using partition_split_append hG₁ hpartL hpartM
      · simp only [List.map_append,List.sum_append]
        have hsub := split_potential_subadditive T A.card A₁.card A₂.card hT hlarge
          (Nat.cast_nonneg _) (Nat.cast_nonneg _) hsize₁ (by exact_mod_cast hsize₂.le) hsum
        rw [← hn]
        linarith

end ErdosGallai.Scale
end
end
end

end OAI
