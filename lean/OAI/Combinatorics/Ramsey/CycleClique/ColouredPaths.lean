import Mathlib
import OAI.Combinatorics.Ramsey.CycleClique.Basic

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem exists_common_neighbor_different_colours {V : Type*} {H : SimpleGraph V}
    (hconn : H.Connected) (hnb : ¬ H.IsBipartite) (χ : V → Fin 2)
    (hnc : ∃ y z, χ y ≠ χ z) :
    ∃ x y z, H.Adj x y ∧ H.Adj x z ∧ χ y ≠ χ z := by
  classical
  by_contra h
  push Not at h
  have hcol : ¬ (∀ ⦃v w⦄, H.Adj v w → χ v ≠ χ w) := by
    intro hc
    exact hnb ⟨SimpleGraph.Coloring.mk χ (fun {v w} hvw => hc hvw)⟩
  push Not at hcol
  obtain ⟨a, b, hab, heq⟩ := hcol
  have propagate : ∀ {u v : V} (p : H.Walk u v),
      ∀ z, H.Adj u z → χ u = χ z → χ v = χ u := by
    intro u v p
    induction p with
    | nil => simp
    | @cons u w v huw p ih =>
      intro z huz heq
      have hwu : χ w = χ u := (h u z w huz huw).symm.trans heq.symm
      exact (ih u huw.symm hwu).trans hwu
  obtain ⟨y, z, hyz⟩ := hnc
  have hy : χ y = χ a := by
    obtain ⟨p⟩ := hconn.preconnected a y
    exact propagate p b hab heq
  have hz : χ z = χ a := by
    obtain ⟨p⟩ := hconn.preconnected a z
    exact propagate p b hab heq
  exact hyz (hy.trans hz.symm)

 
theorem exists_longest_path_from {V : Type*} [Fintype V]
    (G : SimpleGraph V) (x : V) :
    ∃ (v : V) (p : G.Walk x v), p.IsPath ∧
      ∀ (w : V) (q : G.Walk x w), q.IsPath → q.length ≤ p.length := by
  let S := {n : ℕ | ∃ (v : V) (p : G.Walk x v), p.IsPath ∧ p.length = n}
  have hS : S.Finite := (Set.finite_le_nat (Fintype.card V)).subset (by
    rintro n ⟨v, p, hp, rfl⟩
    exact hp.length_lt.le)
  obtain ⟨n, ⟨⟨v, p, hp, hn⟩, hmax⟩⟩ :=
    hS.exists_maximal ⟨0, ⟨x, .nil, by simp⟩⟩
  refine ⟨v, p, hp, fun w q hq => ?_⟩
  have := hmax (show q.length ∈ S from ⟨w, q, hq, rfl⟩)
  omega

 
theorem longest_path_endpoint_neighbors {V : Type*} {G : SimpleGraph V}
    {x v : V} (p : G.Walk x v) (hp : p.IsPath)
    (hmax : ∀ (w : V) (q : G.Walk x w), q.IsPath → q.length ≤ p.length) :
    ∀ w, G.Adj v w → w ∈ p.support := by
  intro w hvw
  by_contra hw
  have := hmax w (p.concat hvw) (hp.concat hw hvw)
  simp only [SimpleGraph.Walk.length_concat] at this
  omega

 

theorem different_colour_prefix {V : Type*} {G : SimpleGraph V}
    {x b y z : V} (χ : V → Fin 2) (hxy : G.Adj x y) (hxz : G.Adj x z)
    (hyz : χ y ≠ χ z) (p : G.Walk x b) (hp : p.IsPath)
    (hy : y ∉ p.support) (hz : z ∉ p.support)
    {ℓ : ℕ} (hℓ : 1 ≤ ℓ) (hlen : ℓ ≤ p.length + 1) :
    ∃ a b, χ a ≠ χ b ∧ ∃ q : G.Walk a b, q.IsPath ∧ q.length = ℓ := by
  let q := p.take (ℓ - 1)
  have hq : q.IsPath := hp.take _
  have hsub : ∀ v, v ∈ q.support → v ∈ p.support := by
    intro v hv
    rw [SimpleGraph.Walk.support_take] at hv
    exact List.mem_of_mem_take hv
  have hqlen : q.length = ℓ - 1 := by
    simp only [q, SimpleGraph.Walk.take_length]
    omega
  by_cases hcy : χ y = χ (p.getVert (ℓ - 1))
  · refine ⟨z, _, ?_, .cons hxz.symm q, ?_, ?_⟩
    · exact fun hcz => hyz (hcy.trans hcz.symm)
    · exact (SimpleGraph.Walk.cons_isPath_iff _ _).mpr ⟨hq, fun h => hz (hsub _ h)⟩
    · simp only [SimpleGraph.Walk.length_cons, hqlen]
      omega
  · refine ⟨y, _, hcy, .cons hxy.symm q, ?_, ?_⟩
    · exact (SimpleGraph.Walk.cons_isPath_iff _ _).mpr ⟨hq, fun h => hy (hsub _ h)⟩
    · simp only [SimpleGraph.Walk.length_cons, hqlen]
      omega

 
theorem path_rotation_prefix {V : Type*} {G : SimpleGraph V} {x v : V}
    (p : G.Walk x v) (hp : p.IsPath) (i : ℕ) (hi : i < p.length)
    (hiv : G.Adj (p.getVert i) v) :
    ∃ q : G.Walk x (p.getVert (i + 1)), q.IsPath ∧ q.support.Perm p.support ∧
      ∀ j, j ≤ i → q.getVert j = p.getVert j := by
  let q := (p.take i).append (.cons hiv (p.drop (i + 1)).reverse)
  have hsupport : q.support =
      p.support.take (i + 1) ++ (p.support.drop (i + 1)).reverse := by
    simp only [q, SimpleGraph.Walk.support_append, SimpleGraph.Walk.support_cons,
      List.tail_cons, SimpleGraph.Walk.support_take, SimpleGraph.Walk.support_reverse,
      SimpleGraph.Walk.drop_support_eq_support_drop_min, Nat.min_eq_left (by omega :
        i + 1 ≤ p.length)]
  have hperm : q.support.Perm p.support := by
    rw [hsupport]
    simpa only [List.take_append_drop] using
      (List.reverse_perm (p.support.drop (i + 1))).append_left (p.support.take (i + 1))
  refine ⟨q, (q.isPath_def).mpr (hperm.nodup_iff.mpr hp.support_nodup), hperm, ?_⟩
  intro j hj
  simp only [q, SimpleGraph.Walk.getVert_append', SimpleGraph.Walk.take_length,
    Nat.min_eq_left hi.le, ite_eq_left hj, SimpleGraph.Walk.take_getVert,
    Nat.min_eq_right hj]

theorem path_rotation {V : Type*} {G : SimpleGraph V} {x v : V}
    (p : G.Walk x v) (hp : p.IsPath) (i : ℕ) (hi : i < p.length)
    (hiv : G.Adj (p.getVert i) v) :
    ∃ q : G.Walk x (p.getVert (i + 1)), q.IsPath ∧ q.support.Perm p.support := by
  obtain ⟨q, hq, hperm, _⟩ := path_rotation_prefix p hp i hi hiv
  exact ⟨q, hq, hperm⟩

 
def pathEnds {V : Type*} (G : SimpleGraph V) (x : V) (W : List V) : Set V :=
  {v | ∃ p : G.Walk x v, p.IsPath ∧ p.support.Perm W}

theorem mem_pathEnds_support {V : Type*} {G : SimpleGraph V} {x v : V} {W : List V}
    (hv : v ∈ pathEnds G x W) : v ∈ W := by
  obtain ⟨p, _, hperm⟩ := hv
  exact hperm.mem_iff.mp p.end_mem_support

theorem pathEnds_no_start {V : Type*} {G : SimpleGraph V} {x : V} {W : List V}
    (hW : 1 < W.length) : x ∉ pathEnds G x W := by
  rintro ⟨p, hp, hperm⟩
  have hp0 := (SimpleGraph.Walk.isPath_iff_nil.mp hp).length_eq_zero
  have hlen := hperm.length_eq
  rw [SimpleGraph.Walk.length_support] at hlen
  omega

 
theorem successor_mem_pathEnds {V : Type*} {G : SimpleGraph V} {x e : V}
    {W : List V} (p : G.Walk x e) (hp : p.IsPath) (hperm : p.support.Perm W)
    (i : ℕ) (hi : i < p.length) (hie : G.Adj (p.getVert i) e) :
    p.getVert (i + 1) ∈ pathEnds G x W := by
  obtain ⟨q, hq, hqp⟩ := path_rotation p hp i hi hie
  exact ⟨q, hq, hqp.trans hperm⟩

 

theorem degree_le_card_pathEnds {V : Type*} [Fintype V] {G : SimpleGraph V}
    [DecidableRel G.Adj] {x e : V} {W : List V}
    (p : G.Walk x e) (hp : p.IsPath) (hperm : p.support.Perm W)
    (hnb : ∀ v, G.Adj e v → v ∈ p.support) :
    G.degree e ≤ (pathEnds G x W).ncard := by
  classical
  have hidx : ∀ v : G.neighborSet e,
      ∃ n, n < p.length ∧ p.getVert n = v.val := by
    intro v
    obtain ⟨n, hn, hle⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp
      (hnb v.val v.property)
    refine ⟨n, lt_of_le_of_ne hle ?_, hn⟩
    intro heq
    subst n
    have : e = v.val := by simpa using hn
    exact G.ne_of_adj v.property this
  choose idx hi heq using hidx
  let f : G.neighborSet e → pathEnds G x W := fun v =>
    ⟨p.getVert (idx v + 1), successor_mem_pathEnds p hp hperm (idx v) (hi v)
      (by rw [heq]; exact v.property.symm)⟩
  have hf : Function.Injective f := by
    intro a b hab
    have hget : p.getVert (idx a + 1) = p.getVert (idx b + 1) := congrArg Subtype.val hab
    have hia := hi a
    have hib := hi b
    have hindex := hp.getVert_injOn (by dsimp; omega) (by dsimp; omega) hget
    have : idx a = idx b := by omega
    apply Subtype.ext
    rw [← heq a, ← heq b, this]
  have hcard := Fintype.card_le_of_injective f hf
  rw [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card,
    ← SimpleGraph.card_neighborSet_eq_degree]
  exact hcard

 
theorem pathEnds_neighbors {V : Type*} {G : SimpleGraph V} {x v : V}
    (p : G.Walk x v)
    (hmax : ∀ (w : V) (q : G.Walk x w), q.IsPath → q.length ≤ p.length)
    {e : V} (he : e ∈ pathEnds G x p.support) :
    ∀ w, G.Adj e w → w ∈ p.support := by
  obtain ⟨q, hq, hqp⟩ := he
  have hlen : q.length = p.length := by
    have := hqp.length_eq
    simp only [SimpleGraph.Walk.length_support] at this
    omega
  intro w hew
  apply hqp.mem_iff.mp
  exact longest_path_endpoint_neighbors q hq (by simpa only [hlen] using hmax) w hew

 
theorem pathEnds_isClique {V : Type*} [Fintype V] {G : SimpleGraph V}
    {x v : V} (p : G.Walk x v) (hp : p.IsPath)
    (hmax : ∀ (w : V) (q : G.Walk x w), q.IsPath → q.length ≤ p.length)
    (hexpand : ∀ a ∈ pathEnds G x p.support, ∀ b ∈ pathEnds G x p.support,
      a ≠ b → ¬ G.Adj a b →
      p.length + 2 ≤ (closedNeighborhood G {a, b}).ncard) :
    G.IsClique (pathEnds G x p.support) := by
  classical
  intro a ha b hb hab
  by_contra hnab
  have hsub : closedNeighborhood G {a, b} ⊆ (p.support.toFinset : Set V) := by
    intro w hw
    rcases hw with hw | ⟨u, hu, huw⟩
    · rcases hw with rfl | hw
      · simpa using mem_pathEnds_support ha
      · have : w = b := by simpa using hw
        subst w
        simpa using mem_pathEnds_support hb
    · rcases hu with rfl | hu
      · simpa using pathEnds_neighbors p hmax ha w huw
      · have : u = b := by simpa using hu
        subst u
        simpa using pathEnds_neighbors p hmax hb w huw
  have hle := Set.ncard_le_ncard hsub
  have hcard : (p.support.toFinset : Set V).ncard = p.length + 1 := by
    simp only [Set.ncard_coe_finset, List.toFinset_card_of_nodup hp.support_nodup,
      SimpleGraph.Walk.length_support]
  have := hexpand a ha b hb hab hnab
  omega

 
theorem pathEnds_successor_closed {V : Type*} {G : SimpleGraph V} {x v : V}
    {W : List V} (p : G.Walk x v) (hp : p.IsPath) (hperm : p.support.Perm W)
    (hclique : G.IsClique (pathEnds G x W))
    (i : ℕ) (hi : i < p.length) (hEi : p.getVert i ∈ pathEnds G x W) :
    p.getVert (i + 1) ∈ pathEnds G x W := by
  apply successor_mem_pathEnds p hp hperm i hi
  apply hclique hEi (show v ∈ pathEnds G x W from ⟨p, hp, hperm⟩)
  intro heq
  have := (hp.getVert_eq_end_iff hi.le).mp heq
  omega

 
theorem pathEnds_final_segment {V : Type*} {G : SimpleGraph V} {x v : V}
    {W : List V} (p : G.Walk x v) (hp : p.IsPath) (hperm : p.support.Perm W)
    (hclique : G.IsClique (pathEnds G x W)) (hW : 1 < W.length) :
    ∃ k, 0 < k ∧ k ≤ p.length ∧ ∀ i, i ≤ p.length →
      (p.getVert i ∈ pathEnds G x W ↔ k ≤ i) := by
  classical
  have hex : ∃ i, i ≤ p.length ∧ p.getVert i ∈ pathEnds G x W := by
    refine ⟨p.length, le_rfl, ?_⟩
    simpa using (show v ∈ pathEnds G x W from ⟨p, hp, hperm⟩)
  let k := Nat.find hex
  have hk := Nat.find_spec hex
  have hkpos : 0 < k := by
    by_contra h
    have hk0 : k = 0 := by omega
    have hx : x ∈ pathEnds G x W := by simpa only [← show k = Nat.find hex from rfl,
      hk0, SimpleGraph.Walk.getVert_zero] using hk.2
    exact pathEnds_no_start hW hx
  refine ⟨k, hkpos, hk.1, fun i hi => ⟨?_, ?_⟩⟩
  · intro hEi
    exact Nat.find_min' hex ⟨hi, hEi⟩
  · intro hki
    induction i, hki using Nat.le_induction with
    | base => exact hk.2
    | succ i hki ih =>
      exact pathEnds_successor_closed p hp hperm hclique i (by omega) (ih (by omega))

 

theorem pathEnd_ordering_preserving_prefix {V : Type*} {G : SimpleGraph V} {x v : V}
    (p : G.Walk x v) (hp : p.IsPath)
    (hclique : G.IsClique (pathEnds G x p.support))
    {k : ℕ} (_ : k ≤ p.length)
    (hsegment : ∀ i, i ≤ p.length →
      (p.getVert i ∈ pathEnds G x p.support ↔ k ≤ i))
    {w : V} (hw : w ∈ pathEnds G x p.support) (hw0 : w ≠ p.getVert k) :
    ∃ q : G.Walk x w, q.IsPath ∧ q.support.Perm p.support ∧
      ∀ j, j ≤ k → q.getVert j = p.getVert j := by
  obtain ⟨i, hiw, hi⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp
    (mem_pathEnds_support hw)
  have hki : k < i := by
    have := (hsegment i hi).mp (hiw ▸ hw)
    by_contra hn
    have : k = i := by omega
    exact hw0 (hiw.symm.trans (congrArg p.getVert this.symm))
  have hpred : p.getVert (i - 1) ∈ pathEnds G x p.support :=
    (hsegment _ (by omega)).mpr (by omega)
  have hadj : G.Adj (p.getVert (i - 1)) v := by
    apply hclique hpred (show v ∈ pathEnds G x p.support from ⟨p, hp, .refl _⟩)
    intro heq
    have := (hp.getVert_eq_end_iff (by omega)).mp heq
    omega
  have hrot := path_rotation_prefix p hp (i - 1) (by omega) hadj
  rw [Nat.sub_add_cancel (by omega : 1 ≤ i), hiw] at hrot
  obtain ⟨q, hq, hperm, hpre⟩ := hrot
  exact ⟨q, hq, hperm, fun j hj => hpre j (by omega)⟩

 
theorem pathEnd_attachment_of_common_prefix {V : Type*} {G : SimpleGraph V} {x v : V}
    (p : G.Walk x v)
    (hmax : ∀ (w : V) (q : G.Walk x w), q.IsPath → q.length ≤ p.length)
    {k : ℕ} (hkpos : 0 < k) (hk : k ≤ p.length)
    (hsegment : ∀ i, i ≤ p.length →
      (p.getVert i ∈ pathEnds G x p.support ↔ k ≤ i))
    {w : V} (q : G.Walk x w) (hq : q.IsPath) (hperm : q.support.Perm p.support)
    (hpre : ∀ j, j < k → q.getVert j = p.getVert j) :
    ∀ a, G.Adj w a → a ∈ pathEnds G x p.support ∨ a = p.getVert (k - 1) := by
  have hlen : q.length = p.length := by
    have := hperm.length_eq
    simp only [SimpleGraph.Walk.length_support] at this
    omega
  intro a ha
  by_cases haE : a ∈ pathEnds G x p.support
  · exact Or.inl haE
  right
  obtain ⟨j, hja, hj⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp
    (pathEnds_neighbors p hmax ⟨q, hq, hperm⟩ a ha)
  have hjk : j < k := by
    by_contra hn
    exact haE (hja ▸ (hsegment j hj).mpr (by omega))
  have hjprec : j = k - 1 := by
    by_contra hn
    have hsucc : j + 1 < k := by omega
    have hadj : G.Adj (q.getVert j) w := by rw [hpre j hjk, hja]; exact ha.symm
    have he := successor_mem_pathEnds q hq hperm j (by omega) hadj
    rw [hpre (j + 1) hsucc] at he
    have := (hsegment (j + 1) (by omega)).mp he
    omega
  exact hja.symm.trans (congrArg p.getVert hjprec)

 
theorem pathEnds_partial_attachment {V : Type*} {G : SimpleGraph V} {x v : V}
    (p : G.Walk x v) (hp : p.IsPath)
    (hmax : ∀ (w : V) (q : G.Walk x w), q.IsPath → q.length ≤ p.length)
    (hclique : G.IsClique (pathEnds G x p.support))
    {k : ℕ} (hkpos : 0 < k) (hk : k ≤ p.length)
    (hsegment : ∀ i, i ≤ p.length →
      (p.getVert i ∈ pathEnds G x p.support ↔ k ≤ i))
    {w : V} (hw : w ∈ pathEnds G x p.support) (hw0 : w ≠ p.getVert k) :
    ∀ a, G.Adj w a → a ∈ pathEnds G x p.support ∨ a = p.getVert (k - 1) := by
  obtain ⟨q, hq, hperm, hpre⟩ := pathEnd_ordering_preserving_prefix p hp hclique hk
    hsegment hw hw0
  exact pathEnd_attachment_of_common_prefix p hmax hkpos hk hsegment q hq hperm
    (fun j hj => hpre j hj.le)

 

theorem pathEnds_attachment_of_two_entries {V : Type*} {G : SimpleGraph V} {x v : V}
    (p : G.Walk x v) (hp : p.IsPath)
    (hmax : ∀ (w : V) (q : G.Walk x w), q.IsPath → q.length ≤ p.length)
    (hclique : G.IsClique (pathEnds G x p.support))
    {k : ℕ} (hkpos : 0 < k) (hk : k ≤ p.length)
    (hsegment : ∀ i, i ≤ p.length →
      (p.getVert i ∈ pathEnds G x p.support ↔ k ≤ i))
    {w₁ : V} (hw₁ : w₁ ∈ pathEnds G x p.support) (hne : w₁ ≠ p.getVert k)
    (hentry : G.Adj (p.getVert (k - 1)) w₁) :
    ∀ w ∈ pathEnds G x p.support, ∀ a, G.Adj w a →
      a ∈ pathEnds G x p.support ∨ a = p.getVert (k - 1) := by
  intro w hw
  by_cases hww0 : w = p.getVert k
  · subst w
    obtain ⟨q, hq, hperm, hpre⟩ := pathEnd_ordering_preserving_prefix p hp hclique hk
      hsegment hw₁ hne
    have hlen : q.length = p.length := by
      have := hperm.length_eq
      simp only [SimpleGraph.Walk.length_support] at this
      omega
    have hadj : G.Adj (q.getVert (k - 1)) w₁ := by
      rw [hpre _ (by omega)]
      exact hentry
    have hrot := path_rotation_prefix q hq (k - 1) (by omega) hadj
    rw [Nat.sub_add_cancel hkpos, hpre k le_rfl] at hrot
    obtain ⟨r, hr, hrperm, hrpre⟩ := hrot
    exact pathEnd_attachment_of_common_prefix p hmax hkpos hk hsegment r hr
      (hrperm.trans hperm) (fun j hj => (hrpre j (by omega)).trans (hpre j (by omega)))
  · exact pathEnds_partial_attachment p hp hmax hclique hkpos hk hsegment hw hww0

 

def within {V : Type*} (G : SimpleGraph V) (S : Set V) : SimpleGraph V where
  Adj a b := G.Adj a b ∧ a ∈ S ∧ b ∈ S
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩
  loopless := ⟨fun _ h => h.1.ne rfl⟩

theorem within_le {V : Type*} (G : SimpleGraph V) (S : Set V) : within G S ≤ G :=
  fun _ _ h => h.1

theorem within_support {V : Type*} {G : SimpleGraph V} {S : Set V} {x v : V}
    (p : (within G S).Walk x v) (hx : x ∈ S) : ∀ w ∈ p.support, w ∈ S := by
  induction p with
  | nil => simpa using hx
  | @cons u v w huv p ih =>
    intro a ha
    simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at ha
    rcases ha with rfl | ha
    · exact huv.2.1
    · exact ih huv.2.2 a ha

 
def walkWithin {V : Type*} {G : SimpleGraph V} {S : Set V} {x v : V}
    (p : G.Walk x v) (hS : ∀ w ∈ p.support, w ∈ S) : (within G S).Walk x v :=
  match p with
  | .nil => .nil
  | .cons h p => .cons ⟨h, hS _ (by simp), hS _ (by simp)⟩
    (walkWithin p (fun w hw => hS w (by simp [hw])))

@[simp] theorem walkWithin_support {V : Type*} {G : SimpleGraph V} {S : Set V} {x v : V}
    (p : G.Walk x v) (hS : ∀ w ∈ p.support, w ∈ S) : (walkWithin p hS).support = p.support := by
  induction p with
  | nil => rfl
  | @cons a b c h p ih =>
    change a :: (walkWithin p _).support = a :: p.support
    rw [ih]

 
theorem deleted_component {V : Type*} {H : SimpleGraph V} {x y z : V}
    (hxy : x ≠ y) (hxz : x ≠ z) :
    ∃ S : Set V, x ∈ S ∧ y ∉ S ∧ z ∉ S ∧
      (∀ a ∈ S, ∀ b ∈ S, (within H S).Reachable a b) ∧
      (∀ a ∈ S, ∀ b, H.Adj a b → b ∈ S ∨ b = y ∨ b = z) := by
  let D := within H {v | v ≠ y ∧ v ≠ z}
  let S := {v | D.Reachable x v}
  have hx : x ∈ S := SimpleGraph.Reachable.rfl
  have havoid : ∀ v ∈ S, v ≠ y ∧ v ≠ z := by
    rintro v ⟨p⟩
    exact within_support p ⟨hxy, hxz⟩ v p.end_mem_support
  refine ⟨S, hx, fun hy => (havoid y hy).1 rfl, fun hz => (havoid z hz).2 rfl, ?_, ?_⟩
  · intro a ha b hb
    obtain ⟨p⟩ := (ha : D.Reachable x a).symm.trans hb
    have hS : ∀ w ∈ p.support, w ∈ S := by
      intro w hw
      obtain ⟨i, hi, _⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hw
      rw [← hi]
      exact (ha : D.Reachable x a).trans ⟨p.take i⟩
    exact ⟨walkWithin (p.mapLe (within_le H _)) (by simpa using hS)⟩
  · intro a ha b hab
    by_cases hby : b = y
    · exact Or.inr (Or.inl hby)
    by_cases hbz : b = z
    · exact Or.inr (Or.inr hbz)
    exact Or.inl ((ha : D.Reachable x a).trans (SimpleGraph.Adj.reachable
      (show D.Adj a b from ⟨hab, havoid a ha, hby, hbz⟩)))

theorem ncard_neighborSet {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (v : V) : (G.neighborSet v).ncard = G.degree v := by
  rw [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card, SimpleGraph.card_neighborSet_eq_degree]

 
theorem degree_add_one_le_of_neighbors_subset {V : Type*} [Fintype V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {v : V} {S : Set V}
    (hv : v ∈ S) (hS : ∀ w, G.Adj v w → w ∈ S) : G.degree v + 1 ≤ S.ncard := by
  have hsub : insert v (G.neighborSet v) ⊆ S := by
    intro w hw
    rcases hw with rfl | hw
    · exact hv
    · exact hS w hw
  have hc := Set.ncard_le_ncard hsub
  simpa only [Set.ncard_insert_of_notMem G.notMem_neighborSet_self,
    ncard_neighborSet] using hc

 
theorem adj_of_neighbors_subset_of_card {V : Type*} [Fintype V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {v : V} {S : Set V}
    (hv : v ∈ S) (hS : ∀ w, G.Adj v w → w ∈ S)
    (hcard : S.ncard ≤ G.degree v + 1) : ∀ w ∈ S, w ≠ v → G.Adj v w := by
  classical
  have hsub : insert v (G.neighborSet v) ⊆ S := by
    intro w hw
    rcases hw with rfl | hw
    · exact hv
    · exact hS w hw
  have heq : insert v (G.neighborSet v) = S := by
    apply Set.eq_of_subset_of_ncard_le hsub
    simpa only [Set.ncard_insert_of_notMem G.notMem_neighborSet_self,
      ncard_neighborSet] using hcard
  intro w hw hne
  rw [← heq] at hw
  exact hw.resolve_left hne

 
theorem clique_ncard_lt {V : Type*} [Fintype V] {H : SimpleGraph V} {s : ℕ}
    (hfree : ¬ (⊤ : SimpleGraph (Fin s)) ⊑ H) {E : Set V} (hE : H.IsClique E) :
    E.ncard < s := by
  classical
  have hf : H.CliqueFree s := by
    by_contra hn
    exact hfree ((SimpleGraph.not_cliqueFree_iff_top_isContained s).mp hn)
  by_contra hn
  have hle : s ≤ E.toFinset.card := by simpa only [← Set.ncard_eq_toFinset_card'] using
    (Nat.le_of_not_gt hn)
  apply hf.mono hle E.toFinset
  exact ⟨by simpa using hE, rfl⟩

 
theorem degree_le_add_two_of_boundary {V : Type*} [Fintype V]
    {H K : SimpleGraph V} [DecidableRel H.Adj] [DecidableRel K.Adj] {v y z : V}
    (hb : ∀ w, H.Adj v w → K.Adj v w ∨ w = y ∨ w = z) :
    H.degree v ≤ K.degree v + 2 := by
  have hsub : H.neighborSet v ⊆ insert y (insert z (K.neighborSet v)) := by
    intro w hw
    rcases hb w hw with hw | hw | hw
    · exact Or.inr (Or.inr hw)
    · exact Or.inl hw
    · exact Or.inr (Or.inl hw)
  have hle := Set.ncard_le_ncard hsub
  have hy := Set.ncard_insert_le y (insert z (K.neighborSet v))
  have hz := Set.ncard_insert_le z (K.neighborSet v)
  rw [ncard_neighborSet] at hle hz
  omega

 
theorem exists_mem_ne_of_ncard {V : Type*} [Finite V] {E : Set V} {w₀ : V}
    (hcard : 2 ≤ E.ncard) : ∃ w ∈ E, w ≠ w₀ := by
  by_contra hn
  push Not at hn
  have hsub : E ⊆ {w₀} := fun w hw => hn w hw
  have hle := Set.ncard_le_ncard hsub
  simp only [Set.ncard_singleton] at hle
  omega

 

theorem endpoint_clique_two_entries {V : Type*} [Fintype V]
    {H K : SimpleGraph V} [DecidableRel H.Adj] [DecidableRel K.Adj]
    {s : ℕ} (hs : 4 ≤ s) (hfree : ¬ (⊤ : SimpleGraph (Fin s)) ⊑ H)
    (hdegree : ∀ w, s ≤ H.degree w)
    {E : Set V} (hE : H.IsClique E) (hsize : s - 2 ≤ E.ncard)
    {u w₀ y z : V} (hw₀ : w₀ ∈ E) (hu : u ∉ E) (hy : y ∉ E) (hz : z ∉ E)
    (huy : u ≠ y) (huz : u ≠ z)
    (hboundary : ∀ w ∈ E, ∀ a, H.Adj w a → K.Adj w a ∨ a = y ∨ a = z)
    (hpartial : ∀ w ∈ E, w ≠ w₀ → ∀ a, K.Adj w a → a ∈ E ∨ a = u)
    (henddegree : ∀ w ∈ E, K.degree w ≤ E.ncard) :
    ∃ w ∈ E, w ≠ w₀ ∧ K.Adj u w := by
  classical
  have hupper := clique_ncard_lt hfree hE
  have hcases : E.ncard = s - 2 ∨ E.ncard = s - 1 := by omega
  by_contra hno
  push Not at hno
  rcases hcases with hsmall | hlarge
  · obtain ⟨w, hw, hww₀⟩ := exists_mem_ne_of_ncard (show 2 ≤ E.ncard by omega)
    have hnb : ∀ a, H.Adj w a → a ∈ insert u (insert y (insert z E)) := by
      intro a ha
      rcases hboundary w hw a ha with ha | rfl | rfl
      · rcases hpartial w hw hww₀ a ha with ha | rfl
        · exact Or.inr (Or.inr (Or.inr ha))
        · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inl rfl))
    have hcard : (insert u (insert y (insert z E))).ncard ≤ H.degree w + 1 := by
      have := Set.ncard_insert_le u (insert y (insert z E))
      have := Set.ncard_insert_le y (insert z E)
      have := Set.ncard_insert_le z E
      have := hdegree w
      omega
    have hwu : H.Adj w u := adj_of_neighbors_subset_of_card
      (by simp [hw]) hnb hcard u (by simp) (fun heq => hu (heq ▸ hw))
    rcases hboundary w hw u hwu with hwu | h | h
    · exact hno w hw hww₀ hwu.symm
    · exact huy h
    · exact huz h
  · have hboth : ∀ w ∈ E, w ≠ w₀ → H.Adj w y ∧ H.Adj w z := by
      intro w hw hww₀
      have hnb : ∀ a, H.Adj w a → a ∈ insert y (insert z E) := by
        intro a ha
        rcases hboundary w hw a ha with ha | rfl | rfl
        · rcases hpartial w hw hww₀ a ha with haE | rfl
          · exact Or.inr (Or.inr haE)
          · exact False.elim (hno w hw hww₀ ha.symm)
        · exact Or.inl rfl
        · exact Or.inr (Or.inl rfl)
      have hcard : (insert y (insert z E)).ncard ≤ H.degree w + 1 := by
        have := Set.ncard_insert_le y (insert z E)
        have := Set.ncard_insert_le z E
        have := hdegree w
        omega
      have hall := adj_of_neighbors_subset_of_card (G := H) (v := w)
        (by simp [hw]) hnb hcard
      exact ⟨hall y (by simp) (fun heq => hy (heq ▸ hw)),
        hall z (by simp) (fun heq => hz (heq ▸ hw))⟩
    have hw₀one : H.Adj w₀ y ∨ H.Adj w₀ z := by
      by_contra hn
      push Not at hn
      have hsub : H.neighborSet w₀ ⊆ K.neighborSet w₀ := by
        intro a ha
        rcases hboundary w₀ hw₀ a ha with haK | rfl | rfl
        · exact haK
        · exact False.elim (hn.1 ha)
        · exact False.elim (hn.2 ha)
      have hc := Set.ncard_le_ncard hsub
      rw [ncard_neighborSet, ncard_neighborSet] at hc
      have := henddegree w₀ hw₀
      have := hdegree w₀
      omega
    have hbad : ∀ t, t ∉ E → H.Adj w₀ t →
        (∀ w ∈ E, w ≠ w₀ → H.Adj w t) → False := by
      intro t ht hw₀t hall
      have hEt : H.IsClique (insert t E) := hE.insert (by
        intro w hw _
        by_cases heq : w = w₀
        · subst w; exact hw₀t.symm
        · exact (hall w hw heq).symm)
      have := clique_ncard_lt hfree hEt
      rw [Set.ncard_insert_of_notMem ht] at this
      omega
    rcases hw₀one with h | h
    · exact hbad y hy h (fun w hw hne => (hboth w hw hne).1)
    · exact hbad z hz h (fun w hw hne => (hboth w hw hne).2)

 
theorem endpoint_clique_common_neighbor {V : Type*} [Fintype V]
    {H K : SimpleGraph V} [DecidableRel H.Adj] [DecidableRel K.Adj]
    {s : ℕ} (hs : 4 ≤ s) (hfree : ¬ (⊤ : SimpleGraph (Fin s)) ⊑ H)
    (hdegree : ∀ w, s ≤ H.degree w)
    {E : Set V} (hE : H.IsClique E) (hsize : s - 2 ≤ E.ncard)
    {u y z : V} (hu : u ∉ E) (hy : y ∉ E) (hz : z ∉ E)
    (hboundary : ∀ w ∈ E, ∀ a, H.Adj w a → K.Adj w a ∨ a = y ∨ a = z)
    (hattach : ∀ w ∈ E, ∀ a, K.Adj w a → a ∈ E ∨ a = u)
    (hKH : K ≤ H) : ∃ w ∈ E, H.Adj w y ∧ H.Adj w z := by
  classical
  have hupper := clique_ncard_lt hfree hE
  have hcases : E.ncard = s - 2 ∨ E.ncard = s - 1 := by omega
  rcases hcases with hsmall | hlarge
  · obtain ⟨w, hw, _⟩ := exists_mem_ne_of_ncard (w₀ := u) (show 2 ≤ E.ncard by omega)
    have hnb : ∀ a, H.Adj w a → a ∈ insert u (insert y (insert z E)) := by
      intro a ha
      rcases hboundary w hw a ha with ha | rfl | rfl
      · rcases hattach w hw a ha with ha | rfl
        · exact Or.inr (Or.inr (Or.inr ha))
        · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inl rfl))
    have hcard : (insert u (insert y (insert z E))).ncard ≤ H.degree w + 1 := by
      have := Set.ncard_insert_le u (insert y (insert z E))
      have := Set.ncard_insert_le y (insert z E)
      have := Set.ncard_insert_le z E
      have := hdegree w
      omega
    have hall := adj_of_neighbors_subset_of_card (G := H) (v := w)
      (by simp [hw]) hnb hcard
    exact ⟨w, hw, hall y (by simp) (fun heq => hy (heq ▸ hw)),
      hall z (by simp) (fun heq => hz (heq ▸ hw))⟩
  · by_contra hno
    push Not at hno
    have hallu : ∀ w ∈ E, H.Adj w u := by
      intro w hw
      by_contra hnwu
      have heither : ¬ H.Adj w y ∨ ¬ H.Adj w z := by tauto
      have hcount : ∀ t, (∀ a, H.Adj w a → a ∈ insert t E) → False := by
        intro t hnb
        have hbound := degree_add_one_le_of_neighbors_subset
          (G := H) (v := w) (by simp [hw]) hnb
        have := Set.ncard_insert_le t E
        have := hdegree w
        omega
      rcases heither with hny | hnz
      · apply hcount z
        intro a ha
        rcases hboundary w hw a ha with haK | rfl | rfl
        · rcases hattach w hw a haK with haE | rfl
          · exact Or.inr haE
          · exact False.elim (hnwu (hKH haK))
        · exact False.elim (hny ha)
        · exact Or.inl rfl
      · apply hcount y
        intro a ha
        rcases hboundary w hw a ha with haK | rfl | rfl
        · rcases hattach w hw a haK with haE | rfl
          · exact Or.inr haE
          · exact False.elim (hnwu (hKH haK))
        · exact Or.inl rfl
        · exact False.elim (hnz ha)
    have hEu : H.IsClique (insert u E) := hE.insert (fun w hw _ => (hallu w hw).symm)
    have := clique_ncard_lt hfree hEu
    rw [Set.ncard_insert_of_notMem hu] at this
    omega

 

theorem path_avoids_attached_set {V : Type*} {K : SimpleGraph V} {E : Set V} {u b : V}
    (p : K.Walk u b) (hp : p.IsPath) (hb : b ∉ E)
    (hattach : ∀ w ∈ E, ∀ a, K.Adj w a → a ∈ E ∨ a = u) :
    ∀ w ∈ p.support, w ∉ E := by
  intro w hw hwE
  obtain ⟨i, hi, hilen⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hw
  have hiE : p.getVert i ∈ E := hi ▸ hwE
  obtain ⟨d, hd, hfst, hsnd⟩ := (p.drop i).exists_boundary_dart E hiE hb
  have hsndu : d.snd = u := (hattach d.fst hfst d.snd d.adj).resolve_left hsnd
  have hdp : d ∈ p.darts := by
    rw [SimpleGraph.Walk.darts_drop] at hd
    exact List.mem_of_mem_drop hd
  have humem : u ∈ p.support.tail := by
    rw [← SimpleGraph.Walk.map_snd_darts]
    exact List.mem_map.mpr ⟨d, hdp, hsndu⟩
  have hnd := hp.support_nodup
  rw [← p.cons_tail_support, List.nodup_cons] at hnd
  exact hnd.1 humem

 
theorem reachable_after_removing_attached_set {V : Type*} {H : SimpleGraph V}
    {S E : Set V} {u b : V} (hu : u ∈ S \ E) (hb : b ∈ S \ E)
    (hconn : (within H S).Reachable u b)
    (hattach : ∀ w ∈ E, ∀ a, (within H S).Adj w a → a ∈ E ∨ a = u) :
    (within H (S \ E)).Reachable u b := by
  obtain ⟨p, hp⟩ := hconn.exists_isPath
  have hS := within_support p hu.1
  have hE := path_avoids_attached_set p hp hb.2 hattach
  exact ⟨walkWithin (p.mapLe (within_le H S)) (by
    intro w hw
    have hw' : w ∈ p.support := by simpa using hw
    exact ⟨hS w hw', hE w hw'⟩)⟩

 
theorem deletion_component_card {V : Type*} [Fintype V] {H : SimpleGraph V}
    [DecidableRel H.Adj] {s : ℕ} (hs : 4 ≤ s)
    (hfree : ¬ (⊤ : SimpleGraph (Fin s)) ⊑ H) (hdegree : ∀ w, s ≤ H.degree w)
    (hexpand : ∀ a b, a ≠ b → ¬ H.Adj a b →
      2 * s ≤ (closedNeighborhood H {a, b}).ncard)
    {S : Set V} (hS : S.Nonempty) {y z : V} (hy : y ∉ S) (hz : z ∉ S)
    (hboundary : ∀ a ∈ S, ∀ b, H.Adj a b → b ∈ S ∨ b = y ∨ b = z) :
    2 * s - 2 ≤ S.ncard := by
  classical
  have hnotclique : ¬ H.IsClique S := by
    intro hcl
    have hsmall := clique_ncard_lt hfree hcl
    obtain ⟨v, hv⟩ := hS
    have hnb : ∀ w, H.Adj v w → w ∈ insert y (insert z S) := by
      intro w hw
      rcases hboundary v hv w hw with hw | rfl | rfl
      · exact Or.inr (Or.inr hw)
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
    have hc := degree_add_one_le_of_neighbors_subset (G := H) (v := v)
      (by simp [hv]) hnb
    have hc₁ := Set.ncard_insert_le y (insert z S)
    have hc₂ := Set.ncard_insert_le z S
    have hdegreev := hdegree v
    have hcard : S.ncard = s - 1 := by omega
    have hall : ∀ w ∈ S, H.Adj w y := by
      intro w hw
      have hnb' : ∀ a, H.Adj w a → a ∈ insert y (insert z S) := by
        intro a ha
        rcases hboundary w hw a ha with ha | rfl | rfl
        · exact Or.inr (Or.inr ha)
        · exact Or.inl rfl
        · exact Or.inr (Or.inl rfl)
      apply adj_of_neighbors_subset_of_card (G := H) (v := w) (by simp [hw]) hnb'
      · have := hdegree w
        omega
      · simp
      · exact fun heq => hy (heq ▸ hw)
    have hcl' : H.IsClique (insert y S) := hcl.insert (fun w hw _ => (hall w hw).symm)
    have hbad := clique_ncard_lt hfree hcl'
    rw [Set.ncard_insert_of_notMem hy] at hbad
    omega
  change ¬ Set.Pairwise S H.Adj at hnotclique
  simp only [Set.Pairwise] at hnotclique
  push Not at hnotclique
  obtain ⟨a, ha, b, hb, hab, hnab⟩ := hnotclique
  have hsub : closedNeighborhood H {a, b} ⊆ insert y (insert z S) := by
    intro w hw
    rcases hw with hw | ⟨v, hv, hvw⟩
    · have hwS : w ∈ S := by
        rcases hw with rfl | hw
        · exact ha
        · have : w = b := by simpa using hw
          simpa only [this] using hb
      exact Or.inr (Or.inr hwS)
    · have hvS : v ∈ S := by
        rcases hv with rfl | hv
        · exact ha
        · have : v = b := by simpa using hv
          simpa only [this] using hb
      rcases hboundary v hvS w hvw with hw | rfl | rfl
      · exact Or.inr (Or.inr hw)
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
  have hc := Set.ncard_le_ncard hsub
  have hc₁ := Set.ncard_insert_le y (insert z S)
  have hc₂ := Set.ncard_insert_le z S
  have he := hexpand a b hab hnab
  omega

 
theorem closedNeighborhood_within_boundary {V : Type*} {H : SimpleGraph V}
    {S I : Set V} {y z : V} (hI : I ⊆ S)
    (hboundary : ∀ a ∈ S, ∀ b, H.Adj a b → b ∈ S ∨ b = y ∨ b = z) :
    closedNeighborhood H I ⊆ insert y (insert z (closedNeighborhood (within H S) I)) := by
  intro w hw
  rcases hw with hw | ⟨a, ha, haw⟩
  · exact Or.inr (Or.inr (Or.inl hw))
  · rcases hboundary a (hI ha) w haw with hwS | rfl | rfl
    · exact Or.inr (Or.inr (Or.inr ⟨a, ha, haw, hI ha, hwS⟩))
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)

 

theorem clique_path_between {V : Type*} [Fintype V] {G : SimpleGraph V}
    {E : Set V} (hE : G.IsClique E) {a b : V} (ha : a ∈ E) (hb : b ∈ E)
    (hab : a ≠ b) : ∃ p : G.Walk a b, p.IsPath ∧
      (∀ v, v ∈ p.support ↔ v ∈ E) ∧ p.length + 1 = E.ncard := by
  classical
  let T := (E.toFinset.erase a).erase b
  let L := a :: (T.toList ++ [b])
  have hmem : ∀ v, v ∈ L ↔ v ∈ E := by
    intro v
    simp only [L, List.mem_cons, List.mem_append, Finset.mem_toList,
      List.not_mem_nil, or_false, T, Finset.mem_erase, Set.mem_toFinset]
    constructor
    · rintro (rfl | ⟨_, _, hv⟩ | rfl)
      · exact ha
      · exact hv
      · exact hb
    · intro hv
      by_cases hva : v = a
      · exact Or.inl hva
      by_cases hvb : v = b
      · exact Or.inr (Or.inr hvb)
      exact Or.inr (Or.inl ⟨hvb, hva, hv⟩)
  have hnd : L.Nodup := by
    simp only [L, List.nodup_cons, List.mem_append, Finset.mem_toList,
      List.mem_singleton, T, Finset.mem_erase, List.nodup_append]
    refine ⟨?_, Finset.nodup_toList _, by simp, ?_⟩
    · simp [hab]
    · intro c hc d hd
      have hdb : d = b := by simpa using hd
      subst d
      exact hc.1
  have hchain : L.IsChain G.Adj := by
    apply List.Pairwise.isChain
    rw [List.pairwise_iff_getElem]
    intro i j hi hj hij
    exact hE ((hmem _).mp (List.getElem_mem hi)) ((hmem _).mp (List.getElem_mem hj))
      (fun heq => (Nat.ne_of_lt hij) (hnd.getElem_inj_iff.mp heq))
  let p₀ := SimpleGraph.Walk.ofSupport L (by simp [L]) hchain
  have hfirst : L.head (by simp [L]) = a := rfl
  have hlast : L.getLast (by simp [L]) = b := by
    change ((a :: T.toList) ++ [b]).getLast _ = b
    exact List.getLast_concat
  let p := p₀.copy hfirst hlast
  have hsupport : p.support = L := by simp [p, p₀]
  have hp : p.IsPath := p.isPath_def.mpr (hsupport ▸ hnd)
  refine ⟨p, hp, fun v => by rw [hsupport]; exact hmem v, ?_⟩
  have hset : (p.support.toFinset : Set V) = E := by
    ext v
    simpa [hsupport] using hmem v
  rw [← hset, Set.ncard_coe_finset, List.toFinset_card_of_nodup hp.support_nodup,
    SimpleGraph.Walk.length_support]

 
theorem join_disjoint_paths {V : Type*} {G : SimpleGraph V} {a b u v : V}
    (p : G.Walk a b) (q : G.Walk u v) (hp : p.IsPath) (hq : q.IsPath)
    (hbu : G.Adj b u) (hdis : ∀ w ∈ p.support, w ∉ q.support) :
    (p.append (.cons hbu q)).IsPath := by
  rw [SimpleGraph.Walk.isPath_def, SimpleGraph.Walk.support_append,
    SimpleGraph.Walk.support_cons, List.tail_cons, List.nodup_append]
  refine ⟨hp.support_nodup, hq.support_nodup, ?_⟩
  intro c hc d hd hcd
  subst d
  exact hdis c hc hd

 

theorem attached_clique_long_path {V : Type*} [Fintype V] {H : SimpleGraph V}
    [DecidableRel H.Adj] {s : ℕ} (hs : 4 ≤ s)
    (hfree : ¬ (⊤ : SimpleGraph (Fin s)) ⊑ H) (hdegree : ∀ a, s ≤ H.degree a)
    (hexpand : ∀ a b, a ≠ b → ¬ H.Adj a b →
      2 * s ≤ (closedNeighborhood H {a, b}).ncard)
    {S E : Set V} {u y z w : V} (hu : u ∈ S \ E) (hw : w ∈ E)
    (hy : y ∉ S) (hz : z ∉ S) (hES : E ⊆ S) (hE : H.IsClique E)
    (hconn : ∀ a ∈ S, ∀ b ∈ S, (within H S).Reachable a b)
    (hboundary : ∀ a ∈ S, ∀ b, H.Adj a b → b ∈ S ∨ b = y ∨ b = z)
    (hattach : ∀ a ∈ E, ∀ b, (within H S).Adj a b → b ∈ E ∨ b = u)
    (hentry : ∃ e ∈ E, e ≠ w ∧ (within H S).Adj e u) :
    ∃ v, ∃ p : (within H S).Walk w v, p.IsPath ∧ 2 * s - 2 ≤ p.length + 1 := by
  classical
  let K := within H S
  let D := within H (S \ E)
  have hDK : D ≤ K := fun a b h => ⟨h.1, h.2.1.1, h.2.2.1⟩
  have hScard := deletion_component_card hs hfree hdegree hexpand ⟨u, hu.1⟩ hy hz hboundary
  have hEcard := clique_ncard_lt hfree hE
  have hDcard : 2 ≤ (S \ E).ncard := by
    have := Set.ncard_sdiff_add_ncard_of_subset hES
    omega
  obtain ⟨b, hb, hbu⟩ := exists_mem_ne_of_ncard (w₀ := u) hDcard
  have hreach := reachable_after_removing_attached_set hu hb
    (hconn u hu.1 b hb.1) hattach
  obtain ⟨r₀, hr₀⟩ := hreach.exists_isPath
  obtain ⟨v, r, hr, hmax⟩ := exists_longest_path_from D u
  have hpos : 0 < r.length := by
    have hle := hmax b r₀ hr₀
    have hne : r₀.length ≠ 0 := fun h => hbu (SimpleGraph.Walk.eq_of_length_eq_zero h).symm
    omega
  have hvu : v ≠ u := by
    intro heq
    subst v
    have := (SimpleGraph.Walk.isPath_iff_nil.mp hr).length_eq_zero
    omega
  have hrS := within_support r hu
  have hv : v ∈ S \ E := hrS v r.end_mem_support
  have hnbs : ∀ a, K.Adj v a → a ∈ r.support := by
    intro a ha
    have haE : a ∉ E := by
      intro haE
      rcases hattach a haE v ha.symm with hvE | hvu'
      · exact hv.2 hvE
      · exact hvu hvu'
    exact longest_path_endpoint_neighbors r hr hmax a ⟨ha.1, hv, ha.2.2, haE⟩
  have hvw : v ≠ w := fun heq => hv.2 (heq ▸ hw)
  have hnvw : ¬ H.Adj v w := by
    intro hvw'
    rcases hattach w hw v ⟨hvw'.symm, hES hw, hv.1⟩ with hvE | hvu'
    · exact hv.2 hvE
    · exact hvu hvu'
  let T : Set V := (r.support.toFinset : Set V)
  have hTcard : T.ncard = r.length + 1 := by
    simp only [T, Set.ncard_coe_finset, List.toFinset_card_of_nodup hr.support_nodup,
      SimpleGraph.Walk.length_support]
  have hsub : closedNeighborhood H {v, w} ⊆ insert y (insert z (E ∪ T)) := by
    intro a ha
    rcases ha with ha | ⟨c, hc, hca⟩
    · rcases Set.mem_insert_iff.mp ha with rfl | ha
      · exact Or.inr (Or.inr (Or.inr (by simp [T])))
      · have : a = w := Set.mem_singleton_iff.mp ha
        subst a
        exact Or.inr (Or.inr (Or.inl hw))
    · rcases Set.mem_insert_iff.mp hc with hc | hc
      · subst c
        rcases hboundary v hv.1 a hca with haS | rfl | rfl
        · exact Or.inr (Or.inr (Or.inr (by simpa [T] using hnbs a ⟨hca, hv.1, haS⟩)))
        · exact Or.inl rfl
        · exact Or.inr (Or.inl rfl)
      · have : c = w := Set.mem_singleton_iff.mp hc
        subst c
        rcases hboundary w (hES hw) a hca with haS | rfl | rfl
        · rcases hattach w hw a ⟨hca, hES hw, haS⟩ with haE | rfl
          · exact Or.inr (Or.inr (Or.inl haE))
          · exact Or.inr (Or.inr (Or.inr (by simp [T])))
        · exact Or.inl rfl
        · exact Or.inr (Or.inl rfl)
  have hsum : 2 * s - 2 ≤ E.ncard + (r.length + 1) := by
    have := hexpand v w hvw hnvw
    have := Set.ncard_le_ncard hsub
    have := Set.ncard_insert_le y (insert z (E ∪ T))
    have := Set.ncard_insert_le z (E ∪ T)
    have := Set.ncard_union_le E T
    omega
  obtain ⟨e, he, hew, heu⟩ := hentry
  have hEK : K.IsClique E := fun a ha b hb hab => ⟨hE ha hb hab, hES ha, hES hb⟩
  obtain ⟨q, hq, hqE, hqcard⟩ := clique_path_between hEK hw he hew.symm
  let rK := r.mapLe hDK
  have hrK : rK.IsPath := hr.mapLe hDK
  have hdis : ∀ a ∈ q.support, a ∉ rK.support := by
    intro a ha har
    have har' : a ∈ r.support := by simpa [rK] using har
    exact (hrS a har').2 ((hqE a).mp ha)
  refine ⟨v, q.append (.cons heu rK), join_disjoint_paths q rK hq hrK heu hdis, ?_⟩
  simp only [SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_cons,
    rK, SimpleGraph.Walk.length_mapLe]
  omega

 
theorem coloured_path {V : Type*} [Fintype V] (H : SimpleGraph V)
    [DecidableRel H.Adj] (s : ℕ) (hs : 4 ≤ s) (hconn : H.Connected)
    (hnb : ¬ H.IsBipartite) (hfree : ¬ (⊤ : SimpleGraph (Fin s)) ⊑ H)
    (hdegree : ∀ v, s ≤ H.degree v)
    (hexpand : ∀ a b, a ≠ b → ¬ H.Adj a b →
      2 * s ≤ (closedNeighborhood H {a, b}).ncard)
    (χ : V → Fin 2) (hnc : ∃ y z, χ y ≠ χ z)
    (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (hℓmax : ℓ ≤ 2 * s - 2) :
    ∃ y z, χ y ≠ χ z ∧ ∃ p : H.Walk y z, p.IsPath ∧ p.length = ℓ := by
  classical
  obtain ⟨x, y, z, hxy, hxz, hyzcol⟩ :=
    exists_common_neighbor_different_colours hconn hnb χ hnc
  obtain ⟨S, hxS, hyS, hzS, hSconn, hboundary⟩ := deleted_component hxy.ne hxz.ne
  let K := within H S
  have hKH : K ≤ H := within_le H S
  have hbound : ∀ a ∈ S, ∀ b, H.Adj a b → K.Adj a b ∨ b = y ∨ b = z := by
    intro a ha b hab
    rcases hboundary a ha b hab with hb | hb | hb
    · exact Or.inl ⟨hab, ha, hb⟩
    · exact Or.inr (Or.inl hb)
    · exact Or.inr (Or.inr hb)
  have hKdegree : ∀ a ∈ S, s - 2 ≤ K.degree a := by
    intro a ha
    have := degree_le_add_two_of_boundary (hbound a ha)
    have := hdegree a
    omega
  obtain ⟨v, p, hp, hmax⟩ := exists_longest_path_from K x
  have hpS := within_support p hxS
  have hvS := hpS v p.end_mem_support
  have hprefix : ∀ {a b : V}, H.Adj a y → H.Adj a z →
      (q : K.Walk a b) → q.IsPath → a ∈ S → ℓ ≤ q.length + 1 →
      ∃ y z, χ y ≠ χ z ∧ ∃ r : H.Walk y z, r.IsPath ∧ r.length = ℓ := by
    intro a b hay haz q hq ha hlen
    have hqS := within_support q ha
    apply different_colour_prefix χ hay haz hyzcol (q.mapLe hKH) (hq.mapLe hKH)
    · intro h
      exact hyS (hqS y (by simpa using h))
    · intro h
      exact hzS (hqS z (by simpa using h))
    · exact hℓ
    · simpa using hlen
  by_cases hlen : ℓ ≤ p.length + 1
  · exact hprefix hxy hxz p hp hxS hlen
  have hplen : 0 < p.length := by
    have hpcard : (p.support.toFinset : Set V).ncard = p.length + 1 := by
      simp only [Set.ncard_coe_finset, List.toFinset_card_of_nodup hp.support_nodup,
        SimpleGraph.Walk.length_support]
    have hnbp := longest_path_endpoint_neighbors p hp hmax
    have hc := degree_add_one_le_of_neighbors_subset (G := K) (v := v)
      (S := (p.support.toFinset : Set V)) (by simp)
      (fun w hw => by simpa using hnbp w hw)
    have := hKdegree v hvS
    omega
  let E := pathEnds K x p.support
  have hES : E ⊆ S := fun e he => hpS e (mem_pathEnds_support he)
  have hcl : K.IsClique E := by
    apply pathEnds_isClique p hp hmax
    intro a ha b hb hab hnab
    have haS := hES ha
    have hbS := hES hb
    have hnabH : ¬ H.Adj a b := fun h => hnab ⟨h, haS, hbS⟩
    have hI : ({a, b} : Set V) ⊆ S := by
      intro c hc
      rcases Set.mem_insert_iff.mp hc with hc | hc
      · exact hc ▸ haS
      · exact (Set.mem_singleton_iff.mp hc) ▸ hbS
    have hsub := closedNeighborhood_within_boundary hI hboundary
    have hc := Set.ncard_le_ncard hsub
    have hc₁ := Set.ncard_insert_le y (insert z (closedNeighborhood K {a, b}))
    have hc₂ := Set.ncard_insert_le z (closedNeighborhood K {a, b})
    have he := hexpand a b hab hnabH
    change (closedNeighborhood H {a, b}).ncard ≤
      (insert y (insert z (closedNeighborhood K {a, b}))).ncard at hc
    omega
  have hclH : H.IsClique E := fun a ha b hb hab => hKH (hcl ha hb hab)
  have hEnddeg : ∀ e ∈ E, K.degree e ≤ E.ncard := by
    intro e he
    obtain ⟨q, hq, hperm⟩ := he
    apply degree_le_card_pathEnds q hq hperm
    intro a hea
    exact hperm.mem_iff.mpr (pathEnds_neighbors p hmax ⟨q, hq, hperm⟩ a hea)
  have hvE : v ∈ E := ⟨p, hp, .refl _⟩
  have hEsize : s - 2 ≤ E.ncard := (hKdegree v hvS).trans (hEnddeg v hvE)
  obtain ⟨k, hkpos, hk, hsegment⟩ := pathEnds_final_segment p hp (.refl _) hcl
    (by simp only [SimpleGraph.Walk.length_support]; omega)
  let u := p.getVert (k - 1)
  let w₀ := p.getVert k
  have huS : u ∈ S := hpS u (p.getVert_mem_support _)
  have huE : u ∉ E := by
    intro hu
    have := (hsegment (k - 1) (by omega)).mp hu
    omega
  have hw₀ : w₀ ∈ E := (hsegment k hk).mpr le_rfl
  have huw₀ : K.Adj u w₀ := by
    have := p.adj_getVert_succ (show k - 1 < p.length by omega)
    simpa only [Nat.sub_add_cancel hkpos] using this
  have hyE : y ∉ E := fun h => hyS (hES h)
  have hzE : z ∉ E := fun h => hzS (hES h)
  have huy : u ≠ y := fun heq => hyS (heq ▸ huS)
  have huz : u ≠ z := fun heq => hzS (heq ▸ huS)
  have hEbound : ∀ e ∈ E, ∀ b, H.Adj e b → K.Adj e b ∨ b = y ∨ b = z :=
    fun e he => hbound e (hES he)
  obtain ⟨w₁, hw₁, hw₁ne, huw₁⟩ := endpoint_clique_two_entries hs hfree hdegree
    hclH hEsize hw₀ huE hyE hzE huy huz hEbound
    (fun e he hne => pathEnds_partial_attachment p hp hmax hcl hkpos hk hsegment he hne) hEnddeg
  have hattach := pathEnds_attachment_of_two_entries p hp hmax hcl hkpos hk hsegment
    hw₁ hw₁ne huw₁
  obtain ⟨w, hw, hwy, hwz⟩ := endpoint_clique_common_neighbor hs hfree hdegree
    hclH hEsize huE hyE hzE hEbound hattach hKH
  have hentry : ∃ e ∈ E, e ≠ w ∧ K.Adj e u := by
    by_cases hww₀ : w = w₀
    · exact ⟨w₁, hw₁, fun heq => hw₁ne (heq.trans hww₀), huw₁.symm⟩
    · exact ⟨w₀, hw₀, Ne.symm hww₀, huw₀.symm⟩
  obtain ⟨b, q, hq, hqlen⟩ := attached_clique_long_path hs hfree hdegree hexpand
    ⟨huS, huE⟩ hw hyS hzS hES hclH hSconn hboundary hattach hentry
  exact hprefix hwy hwz q hq (hES hw) (hℓmax.trans hqlen)

 
theorem colouredPathTarget_proved : ColouredPathTarget := by
  intro V _
  exact coloured_path

end CycleClique

end OAI
