import Mathlib
import OAI.Geometry.Cannon.Model

namespace OAI

/-! Thin geodesic triangles and fellow travelling in the Cayley graph. -/

section
section
section
section
section
section
noncomputable section
namespace CannonGraph
open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

def Thin (G : SimpleGraph V) (δ : ℕ) : Prop :=
  ∀ x y z : V, ∀ p : G.Walk x y, ∀ q : G.Walk y z, ∀ r : G.Walk z x,
    p.length = G.dist x y → q.length = G.dist y z → r.length = G.dist z x →
    ∀ a ∈ p.support, ∃ b ∈ q.support ++ r.support, G.dist a b ≤ δ

lemma start_getVert_dist (hG : G.Connected) {x y : V} (p : G.Walk x y)
    (hp : p.length = G.dist x y) {k : ℕ} (hk : k ≤ p.length) :
    G.dist x (p.getVert k) = k := by
  have ht := G.dist_le (p.take k)
  have hd := G.dist_le (p.drop k)
  have htri := @Connected.dist_triangle _ G x (p.getVert k) y hG
  rw [Walk.take_length, min_eq_left hk] at ht
  rw [Walk.drop_length] at hd
  omega

lemma getVert_end_dist (hG : G.Connected) {x y : V} (p : G.Walk x y)
    (hp : p.length = G.dist x y) {k : ℕ} (hk : k ≤ p.length) :
    G.dist (p.getVert k) y = p.length - k := by
  have ht := start_getVert_dist hG p hp hk
  have hd := G.dist_le (p.drop k)
  have htri := @Connected.dist_triangle _ G x (p.getVert k) y hG
  rw [Walk.drop_length] at hd
  omega

lemma getVert_dist_le {x y : V} (p : G.Walk x y) {i j : ℕ} (hij : i ≤ j) :
    G.dist (p.getVert i) (p.getVert j) ≤ j-i := by
  have h := G.dist_le ((p.drop i).take (j-i))
  rw [Walk.take_length, Walk.drop_getVert, Nat.add_sub_of_le hij] at h
  exact h.trans (min_le_left _ _)

lemma of_mem_geodesic (hG : G.Connected) {x y b : V} (p : G.Walk x y)
    (hp : p.length = G.dist x y) (hb : b ∈ p.support) :
    G.dist x b + G.dist b y = G.dist x y := by
  classical
  have h₁ := G.dist_le (p.takeUntil b hb)
  have h₂ := G.dist_le (p.dropUntil b hb)
  have h₃ := @Connected.dist_triangle _ G x b y hG
  have he : (p.takeUntil b hb).length + (p.dropUntil b hb).length = p.length := by
    rw [← Walk.length_append]; congr 1; exact p.take_spec hb
  omega

lemma opposite_side_bound (hG : G.Connected) {o x y a b : V}
    (q : G.Walk x y) (hq : q.length = G.dist x y) (hb : b ∈ q.support) :
    G.dist o x + G.dist o y ≤ 2 * G.dist o a + 2 * G.dist a b + G.dist x y := by
  have h₁ := @Connected.dist_triangle _ G o a b hG
  have h₂ := @Connected.dist_triangle _ G o b x hG
  have h₃ := @Connected.dist_triangle _ G o b y hG
  have hb' := of_mem_geodesic hG q hq hb
  rw [SimpleGraph.dist_comm (u := b) (v := x)] at h₂
  omega

lemma synchronous_of_near (hG : G.Connected) {o x y : V}
    (p : G.Walk o x) (q : G.Walk o y)
    (hp : p.length = G.dist o x) (hq : q.length = G.dist o y)
    {k δ : ℕ} (hkp : k ≤ p.length) (_hkq : k ≤ q.length)
    {b : V} (hb : b ∈ q.support) (hab : G.dist (p.getVert k) b ≤ δ) :
    G.dist (p.getVert k) (q.getVert k) ≤ 2*δ := by
  obtain ⟨j,hjb,hj⟩ := Walk.mem_support_iff_exists_getVert.mp hb
  subst b
  have hpk := start_getVert_dist hG p hp hkp
  have hqj := start_getVert_dist hG q hq hj
  have h₁ := @Connected.dist_triangle _ G o (p.getVert k) (q.getVert j) hG
  have h₂ := @Connected.dist_triangle _ G o (q.getVert j) (p.getVert k) hG
  rw [SimpleGraph.dist_comm (u := q.getVert j) (v := p.getVert k)] at h₂
  have hd : G.dist (q.getVert j) (q.getVert k) ≤ δ := by
    rcases le_total j k with hjk | hkj
    · have h := getVert_dist_le q hjk
      omega
    · have h := getVert_dist_le q hkj
      rw [SimpleGraph.dist_comm (u := q.getVert k) (v := q.getVert j)] at h
      omega
  have h₃ := @Connected.dist_triangle _ G (p.getVert k) (q.getVert j) (q.getVert k) hG
  omega

lemma fellow_travel_below_product (hG : G.Connected) {δ : ℕ} (hthin : Thin G δ)
    {o x y : V} (p : G.Walk o x) (q : G.Walk o y)
    (hp : p.length = G.dist o x) (hq : q.length = G.dist o y)
    {k : ℕ} (hkp : k ≤ p.length) (hkq : k ≤ q.length)
    (hprod : 2*k + 2*δ + G.dist x y < G.dist o x + G.dist o y) :
    G.dist (p.getVert k) (q.getVert k) ≤ 2*δ := by
  obtain ⟨s,hs⟩ := hG.exists_walk_length_eq_dist x y
  have hqr : q.reverse.length = G.dist y o := by simpa [SimpleGraph.dist_comm] using hq
  obtain ⟨b,hb,hab⟩ := hthin o x y p s q.reverse hp hs hqr
    (p.getVert k) (p.getVert_mem_support k)
  rcases List.mem_append.mp hb with hb | hb
  · have hh := opposite_side_bound hG s hs hb (a := p.getVert k) (o := o)
    rw [start_getVert_dist hG p hp hkp] at hh
    omega
  · apply synchronous_of_near hG p q hp hq hkp hkq _ hab
    simpa using hb

theorem synchronous_prefix (hG : G.Connected) {δ : ℕ} (hthin : Thin G δ)
    {o x y : V} (p : G.Walk o x) (q : G.Walk o y)
    (hp : p.length = G.dist o x) (hq : q.length = G.dist o y)
    {k C : ℕ} (hkp : k ≤ p.length) (hkq : k ≤ q.length)
    (hprod : 2*k + G.dist x y ≤ G.dist o x + G.dist o y + 2*C) :
    G.dist (p.getVert k) (q.getVert k) ≤ 4*δ + 2*C + 2 := by
  by_cases hk : k ≤ δ+C+1
  · have h₁ := start_getVert_dist hG p hp hkp
    have h₂ := start_getVert_dist hG q hq hkq
    have h₃ := @Connected.dist_triangle _ G (p.getVert k) o (q.getVert k) hG
    rw [SimpleGraph.dist_comm (u := p.getVert k) (v := o)] at h₃
    omega
  · let j := k - (δ+C+1)
    have hjk : j ≤ k := Nat.sub_le _ _
    have hjprod : 2*j + 2*δ + G.dist x y < G.dist o x + G.dist o y := by
      dsimp [j]
      omega
    have hj := fellow_travel_below_product hG hthin p q hp hq
      (hjk.trans hkp) (hjk.trans hkq) hjprod
    have h₁ := getVert_dist_le p hjk
    have h₂ := getVert_dist_le q hjk
    have h₃ := @Connected.dist_triangle _ G (p.getVert k) (p.getVert j) (q.getVert j) hG
    have h₄ := @Connected.dist_triangle _ G (p.getVert k) (q.getVert j) (q.getVert k) hG
    rw [SimpleGraph.dist_comm (u := p.getVert j) (v := p.getVert k)] at h₁
    dsimp [j] at *
    omega

def raySegment (r : ℕ → V) (hr : ∀ i j, G.dist (r i) (r j) = Nat.dist i j) :
    (n : ℕ) → G.Walk (r 0) (r n)
  | 0 => .nil
  | n+1 => (raySegment r hr n).concat (dist_eq_one_iff_adj.mp (by rw [hr]; simp [Nat.dist]))

@[simp] lemma raySegment_length (r : ℕ → V)
    (hr : ∀ i j, G.dist (r i) (r j) = Nat.dist i j) (n : ℕ) :
    (raySegment r hr n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [raySegment, ih]

lemma raySegment_getVert (r : ℕ → V)
    (hr : ∀ i j, G.dist (r i) (r j) = Nat.dist i j) {n k : ℕ} (hk : k ≤ n) :
    (raySegment r hr n).getVert k = r k := by
  induction n with
  | zero =>
    have : k = 0 := by omega
    subst k
    rfl
  | succ n ih =>
    by_cases hkn : k ≤ n
    · simp only [raySegment, Walk.concat_eq_append, Walk.getVert_append',
        raySegment_length, ite_eq_left hkn]
      exact ih hkn
    · have : k = n+1 := by omega
      subst k
      have h := (raySegment r hr (n+1)).getVert_length
      simpa using h

theorem asymptotic_rays_uniform (hG : G.Connected) {δ : ℕ} (hthin : Thin G δ)
    (r s : ℕ → V) (hr : ∀ i j, G.dist (r i) (r j) = Nat.dist i j)
    (hs : ∀ i j, G.dist (s i) (s j) = Nat.dist i j) (h₀ : r 0 = s 0)
    (hbounded : ∃ C : ℕ, ∀ n, G.dist (r n) (s n) ≤ C) :
    ∀ n, G.dist (r n) (s n) ≤ 2*δ := by
  obtain ⟨C,hC⟩ := hbounded
  intro n
  let N := n+δ+C+1
  let p := raySegment r hr N
  let q := (raySegment s hs N).copy h₀.symm rfl
  have hp : p.length = G.dist (r 0) (r N) := by simp [p,hr,Nat.dist]
  have hq : q.length = G.dist (r 0) (s N) := by simp [q,h₀,hs,Nat.dist]
  have hnp : n ≤ p.length := by simp only [p,raySegment_length]; dsimp [N]; omega
  have hnq : n ≤ q.length := by simp only [q,Walk.length_copy,raySegment_length]; dsimp [N]; omega
  have hprod : 2*n+2*δ+G.dist (r N) (s N) < G.dist (r 0) (r N)+G.dist (r 0) (s N) := by
    rw [hr, h₀, hs]
    simp only [Nat.dist_zero_left]
    have := hC N
    dsimp [N] at *
    omega
  have h := fellow_travel_below_product hG hthin p q hp hq hnp hnq hprod
  simpa only [p,q,Walk.getVert_copy, raySegment_getVert r hr (show n ≤ N by dsimp [N]; omega),
    raySegment_getVert s hs (show n ≤ N by dsimp [N]; omega)] using h

end CannonGraph

namespace CannonGraph
open SimpleGraph Set

variable {V : Type*} {G : SimpleGraph V}

lemma finite_short_walk_ends (hfin : ∀ v, (G.neighborSet v).Finite) (o : V) (n : ℕ) :
    {v | ∃ p : G.Walk o v, p.length ≤ n}.Finite := by
  induction n with
  | zero =>
    apply (Set.finite_singleton o).subset
    rintro v ⟨p,hp⟩
    exact Set.mem_singleton_iff.mpr (Walk.eq_of_length_eq_zero (p := p) (by omega)).symm
  | succ n ih =>
    apply ((Set.finite_singleton o).union (ih.biUnion (fun v _ => hfin v))).subset
    rintro v ⟨p,hp⟩
    by_cases hz : p.length = 0
    · exact Or.inl (Walk.eq_of_length_eq_zero hz).symm
    · right
      refine Set.mem_iUnion₂.mpr ⟨p.penultimate, ?_, p.adj_penultimate (by simpa only [← Walk.length_eq_zero_iff] using hz)⟩
      refine ⟨p.dropLast, ?_⟩
      rw [Walk.length_dropLast]
      omega

lemma finite_graph_ball (hG : G.Connected) (hfin : ∀ v, (G.neighborSet v).Finite)
    (o : V) (n : ℕ) : {v | G.dist o v ≤ n}.Finite := by
  apply (finite_short_walk_ends hfin o n).subset
  intro v hv
  obtain ⟨p,hp⟩ := hG.exists_walk_length_eq_dist o v
  exact ⟨p, hp ▸ hv⟩

lemma finite_cayley_neighbors {M : Type*} [Group M] (S : Finset M) (v : M) :
    ((SimpleGraph.mulCayley (S : Set M)).neighborSet v).Finite := by
  apply ((S.finite_toSet.image (v * ·)).union (S.finite_toSet.image (fun g => v * g⁻¹))).subset
  intro w hw
  obtain ⟨_,g,hg,he⟩ := (SimpleGraph.mulCayley_adj' (S : Set M) v w).mp hw
  rcases he with he | he
  · exact Or.inl ⟨g,hg,he⟩
  · exact Or.inr ⟨g,hg,by rw [he]; simp⟩

theorem compact_ray_space [TopologicalSpace V] [DiscreteTopology V]
    (hG : G.Connected) (hfin : ∀ v, (G.neighborSet v).Finite) (o : V) :
    IsCompact {r : ℕ → V | r 0 = o ∧ ∀ i j, G.dist (r i) (r j) = Nat.dist i j} := by
  let A : Set (ℕ → V) := {r | r 0 = o ∧ ∀ i j, G.dist (r i) (r j) = Nat.dist i j}
  have hA : IsClosed A := by
    refine (isClosed_eq (continuous_apply 0) continuous_const).inter ?_
    change IsClosed {r : ℕ → V | ∀ i j, G.dist (r i) (r j) = Nat.dist i j}
    simp only [Set.ofPred_forall]
    apply isClosed_iInter
    intro i
    apply isClosed_iInter
    intro j
    have hp : Continuous (fun r : ℕ → V => (r i, r j)) :=
      (continuous_apply i).prodMk (continuous_apply j)
    exact isClosed_eq ((continuous_of_discreteTopology : Continuous (fun p : V × V => G.dist p.1 p.2)).comp hp) continuous_const
  have hpi : IsCompact {r : ℕ → V | ∀ n, G.dist o (r n) ≤ n} :=
    isCompact_pi_infinite (fun n => (finite_graph_ball hG hfin o n).isCompact)
  apply hpi.of_isClosed_subset hA
  intro r hr n
  rw [← hr.1, hr.2, Nat.dist_zero_left]

end CannonGraph

namespace CannonGraph
open SimpleGraph Set Filter
open scoped Topology

variable {V : Type*} {G : SimpleGraph V}

lemma geodesic_getVert_dist (hG : G.Connected) {x y : V} (p : G.Walk x y)
    (hp : p.length = G.dist x y) {i j : ℕ} (hi : i ≤ p.length) (hj : j ≤ p.length) :
    G.dist (p.getVert i) (p.getVert j) = Nat.dist i j := by
  have hai := start_getVert_dist hG p hp hi
  have haj := start_getVert_dist hG p hp hj
  rcases le_total i j with hij | hji
  · have hu := getVert_dist_le p hij
    have hl := @Connected.dist_triangle _ G x (p.getVert i) (p.getVert j) hG
    simp only [Nat.dist_eq_sub_of_le hij]
    omega
  · have hu := getVert_dist_le p hji
    have hl := @Connected.dist_triangle _ G x (p.getVert j) (p.getVert i) hG
    rw [SimpleGraph.dist_comm (u := p.getVert j) (v := p.getVert i)] at hu hl
    simp only [Nat.dist_eq_sub_of_le_right hji]
    omega

lemma different_bases_same_endpoint (hG : G.Connected) {δ : ℕ} (hthin : Thin G δ)
    {o b w : V} (p : G.Walk o w) (q : G.Walk b w)
    (hp : p.length = G.dist o w) (hq : q.length = G.dist b w)
    {k : ℕ} (hkp : k ≤ p.length) (hkq : k ≤ q.length) :
    G.dist (p.getVert k) (q.getVert k) ≤ 3 * G.dist o b + 2*δ := by
  obtain ⟨s,hs⟩ := hG.exists_walk_length_eq_dist b o
  have hqr : q.reverse.length = G.dist w b := by simpa [SimpleGraph.dist_comm] using hq
  obtain ⟨z,hz,haz⟩ := hthin o w b p q.reverse s hp hqr hs
    (p.getVert k) (p.getVert_mem_support k)
  have hpk := start_getVert_dist hG p hp hkp
  have hqk := start_getVert_dist hG q hq hkq
  rcases List.mem_append.mp hz with hz | hz
  · have hzq : z ∈ q.support := by simpa using hz
    obtain ⟨j,hjz,hj⟩ := Walk.mem_support_iff_exists_getVert.mp hzq
    subst z
    have hqj := start_getVert_dist hG q hq hj
    have h₁ := @Connected.dist_triangle _ G o b (q.getVert j) hG
    have h₂ := @Connected.dist_triangle _ G o (q.getVert j) (p.getVert k) hG
    have h₃ := @Connected.dist_triangle _ G b o (p.getVert k) hG
    have h₄ := @Connected.dist_triangle _ G b (p.getVert k) (q.getVert j) hG
    rw [SimpleGraph.dist_comm (u := q.getVert j) (v := p.getVert k)] at h₂
    rw [SimpleGraph.dist_comm (u := b) (v := o)] at h₃
    have hd : G.dist (q.getVert j) (q.getVert k) ≤ G.dist o b + δ := by
      rcases le_total j k with hjk | hkj
      · have hh := getVert_dist_le q hjk
        omega
      · have hh := getVert_dist_le q hkj
        rw [SimpleGraph.dist_comm (u := q.getVert k) (v := q.getVert j)] at hh
        omega
    have hh := @Connected.dist_triangle _ G (p.getVert k) (q.getVert j) (q.getVert k) hG
    omega
  · have hz' := of_mem_geodesic hG s hs hz
    have h₁ := @Connected.dist_triangle _ G o z (p.getVert k) hG
    rw [SimpleGraph.dist_comm (u := z) (v := p.getVert k),
      SimpleGraph.dist_comm (u := o) (v := z)] at h₁
    rw [SimpleGraph.dist_comm (u := b) (v := o)] at hz'
    have h₂ := @Connected.dist_triangle _ G (p.getVert k) o b hG
    have h₃ := @Connected.dist_triangle _ G (p.getVert k) b (q.getVert k) hG
    rw [SimpleGraph.dist_comm (u := p.getVert k) (v := o)] at h₂
    omega

theorem exists_rebased_ray [TopologicalSpace V] [DiscreteTopology V]
    (hG : G.Connected) (hfin : ∀ v, (G.neighborSet v).Finite)
    {δ : ℕ} (hthin : Thin G δ) (r : ℕ → V)
    (hr : ∀ i j, G.dist (r i) (r j) = Nat.dist i j) (o : V) :
    ∃ s : ℕ → V, s 0 = o ∧
      (∀ i j, G.dist (s i) (s j) = Nat.dist i j) ∧
      ∀ n, G.dist (s n) (r n) ≤ 3 * G.dist o (r 0) + 2*δ := by
  choose p hp using fun n => hG.exists_walk_length_eq_dist o (r n)
  let f : ℕ → ℕ → V := fun N k => (p N).getVert k
  have hfball : ∀ N, f N ∈ {s : ℕ → V | ∀ n, G.dist o (s n) ≤ n} := by
    intro N n
    have hh := G.dist_le ((p N).take n)
    rw [Walk.take_length] at hh
    exact hh.trans (min_le_left _ _)
  have hbox : IsCompact {s : ℕ → V | ∀ n, G.dist o (s n) ≤ n} :=
    isCompact_pi_infinite (fun n => (finite_graph_ball hG hfin o n).isCompact)
  obtain ⟨s,hs,φ,hφ,ht⟩ := hbox.tendsto_subseq hfball
  have hlength : ∀ N k, k + G.dist o (r 0) ≤ N → k ≤ (p N).length := by
    intro N k hNk
    have hh := @Connected.dist_triangle _ G (r 0) o (r N) hG
    rw [hr, Nat.dist_zero_left, SimpleGraph.dist_comm (u := r 0) (v := o), ← hp N] at hh
    omega
  have hstart : s 0 = o := by
    have hclosed : IsClosed {s : ℕ → V | s 0 = o} :=
      isClosed_eq (continuous_apply 0) continuous_const
    apply hclosed.mem_of_tendsto ht
    exact Filter.Eventually.of_forall (fun n => by simp [f])
  refine ⟨s,hstart,?_,?_⟩
  · intro i j
    have hclosed : IsClosed {s : ℕ → V | G.dist (s i) (s j) = Nat.dist i j} := by
      exact (isClosed_discrete {n : ℕ | n = Nat.dist i j}).preimage
        ((continuous_of_discreteTopology : Continuous (fun p : V × V => G.dist p.1 p.2)).comp
          ((continuous_apply i : Continuous (fun s : ℕ → V => s i)).prodMk
            (continuous_apply j : Continuous (fun s : ℕ → V => s j))))
    apply hclosed.mem_of_tendsto ht
    filter_upwards [hφ.tendsto_atTop.eventually_ge_atTop (max i j + G.dist o (r 0))] with N hN
    exact geodesic_getVert_dist hG (p (φ N)) (hp (φ N))
      (hlength _ _ (by omega)) (hlength _ _ (by omega))
  · intro k
    have hclosed : IsClosed {s : ℕ → V | G.dist (s k) (r k) ≤ 3 * G.dist o (r 0) + 2*δ} := by
      exact (isClosed_discrete {n : ℕ | n ≤ 3 * G.dist o (r 0) + 2*δ}).preimage
        ((continuous_of_discreteTopology : Continuous (fun v : V => G.dist v (r k))).comp
          (continuous_apply k))
    apply hclosed.mem_of_tendsto ht
    filter_upwards [hφ.tendsto_atTop.eventually_ge_atTop (k + G.dist o (r 0))] with N hN
    have hNk : k ≤ φ N := by omega
    have hh := different_bases_same_endpoint hG hthin (p (φ N)) (raySegment r hr (φ N))
      (hp (φ N)) (by simp [hr, Nat.dist]) (hlength _ _ hN)
      (by simpa only [raySegment_length] using hNk)
    simpa only [Function.comp_apply, f, raySegment_getVert r hr hNk] using hh

end CannonGraph

noncomputable section
open Set Topology

namespace CannonBoundary

lemma quotient_closedMap {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (s : Setoid X) (hs : IsClosed {p : X × X | s.r p.1 p.2}) :
    IsClosedMap (@Quotient.mk' X s) := by
  intro F hF
  apply isQuotientMap_quotient_mk'.isCoinducing.isClosed_preimage.mp
  have h := isClosedMap_fst_of_compactSpace (X := X) (Y := X)
    _ (hs.inter (isClosed_univ.prod hF))
  convert h using 1
  ext x
  constructor
  · rintro ⟨y,hy,hxy⟩
    refine ⟨(x,y),⟨?_,⟨trivial,hy⟩⟩,rfl⟩
    exact s.symm (Quotient.exact hxy)
  · rintro ⟨⟨x',y⟩,⟨hxy,_,hy⟩,rfl⟩
    exact ⟨y,hy,Quotient.sound (s.symm hxy)⟩

theorem quotient_t2_of_closed {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (s : Setoid X) (hs : IsClosed {p : X × X | s.r p.1 p.2}) :
    T2Space (Quotient s) := by
  have hcont : Continuous (@Quotient.mk' X s) := continuous_quotient_mk'
  have hcl := quotient_closedMap s hs
  have hfib : ∀ y : Quotient s, IsCompact ((@Quotient.mk' X s) ⁻¹' {y}) := by
    intro y
    induction y using Quotient.inductionOn with
    | h x =>
      have h : IsClosed {z : X | s.r x z} := hs.preimage (continuous_const.prodMk continuous_id)
      convert h.isCompact using 1
      ext z
      simp only [mem_ofPred_eq, mem_preimage, mem_singleton_iff]
      exact ⟨fun hz => s.symm (Quotient.exact hz), fun hz => Quotient.sound (s.symm hz)⟩
  have hproper := isProperMap_iff_isClosedMap_and_compact_fibers.mpr ⟨hcont,hcl,hfib⟩
  apply t2_iff_isClosed_diagonal.mpr
  have hh := hproper.prodMap hproper
  have he : Set.diagonal (Quotient s) =
      Prod.map (@Quotient.mk' X s) (@Quotient.mk' X s) '' {p : X × X | s.r p.1 p.2} := by
    ext p
    constructor
    · intro hp
      obtain ⟨x,hx⟩ := Quotient.mk'_surjective p.1
      refine ⟨(x,x),s.refl x,?_⟩
      apply Prod.ext
      · exact hx
      · exact hx.trans (Set.mem_diagonal_iff.mp hp)
    · rintro ⟨⟨x,y⟩,hxy,rfl⟩
      exact Quotient.sound hxy
  rw [he]
  exact hh.isClosedMap _ hs

end CannonBoundary

noncomputable section
namespace CannonRelease

universe u

def CannonStatement : Prop :=
  ∀ (G : Type u) [Group G] [TopologicalSpace G] [DiscreteTopology G]
    (D : CayleyData G), D.ThinTriangles → Nonempty (Boundary D ≃ₜ SphereTwo) →
    ∃ ρ : G →* H3Isom, ProperAction ρ ∧ CocompactAction ρ ∧
      (ρ.ker : Set G).Finite

theorem finite_kernel_of_proper {G : Type u} [Group G] (ρ : G →* H3Isom)
    (hρ : ProperAction ρ) : (ρ.ker : Set G).Finite := by
  let o : HyperbolicThree := ⟨fun i => if i = 2 then 1 else 0, by norm_num⟩
  have h := hρ {o} isCompact_singleton
  apply h.subset
  intro g hg
  refine ⟨o, Set.mem_singleton o, ?_⟩
  have hg' : ρ g = 1 := MonoidHom.mem_ker.mp hg
  simp [hg']

end CannonRelease

namespace CannonRelease
open Set

universe v
variable {G : Type v} [Group G] [TopologicalSpace G] [DiscreteTopology G] (D : CayleyData G)

instance basedRay_compactSpace : CompactSpace (BasedRay D) := by
  apply isCompact_iff_compactSpace.mp
  exact CannonGraph.compact_ray_space D.connected
    (CannonGraph.finite_cayley_neighbors D.generators) 1

instance boundary_compactSpace : CompactSpace (Boundary D) :=
  inferInstanceAs (CompactSpace (Quotient (raySetoid D)))

lemma raySetoid_isClosed (hthin : D.ThinTriangles) :
    IsClosed {p : BasedRay D × BasedRay D | (raySetoid D).r p.1 p.2} := by
  obtain ⟨δ,hδ⟩ := hthin
  have hr : {p : BasedRay D × BasedRay D | (raySetoid D).r p.1 p.2} =
    ⋂ n : ℕ, {p | D.graph.dist (p.1.val n) (p.2.val n) ≤ 2*δ} := by
    ext p
    simp only [Set.mem_ofPred_eq, Set.mem_iInter]
    constructor
    · intro hp
      exact CannonGraph.asymptotic_rays_uniform D.connected hδ p.1.val p.2.val
        p.1.property.2 p.2.property.2 (p.1.property.1.trans p.2.property.1.symm) hp
    · intro hp
      exact ⟨2*δ,hp⟩
  rw [hr]
  apply isClosed_iInter
  intro n
  have h₁ : Continuous (fun p : BasedRay D × BasedRay D => p.1.val n) :=
    (continuous_apply n).comp (continuous_subtype_val.comp continuous_fst)
  have h₂ : Continuous (fun p : BasedRay D × BasedRay D => p.2.val n) :=
    (continuous_apply n).comp (continuous_subtype_val.comp continuous_snd)
  exact (isClosed_discrete {k : ℕ | k ≤ 2*δ}).preimage
    ((continuous_of_discreteTopology : Continuous (fun p : G × G => D.graph.dist p.1 p.2)).comp
      (h₁.prodMk h₂))

 theorem boundary_t2Space (hthin : D.ThinTriangles) : T2Space (Boundary D) :=
  CannonBoundary.quotient_t2_of_closed (raySetoid D) (raySetoid_isClosed D hthin)

end CannonRelease

namespace CannonGraph
open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

lemma iso_dist (hG : G.Connected) (e : G ≃g G) (x y : V) :
    G.dist (e x) (e y) = G.dist x y := by
  apply le_antisymm
  · obtain ⟨p,hp⟩ := hG.exists_walk_length_eq_dist x y
    simpa [hp] using G.dist_le (p.map e.toHom)
  · obtain ⟨p,hp⟩ := hG.exists_walk_length_eq_dist (e x) (e y)
    simpa [hp] using G.dist_le (p.map e.symm.toHom)

theorem asymptotic_rays_different_bases_uniform
    [TopologicalSpace V] [DiscreteTopology V]
    (hG : G.Connected) (hfin : ∀ v, (G.neighborSet v).Finite)
    {δ : ℕ} (hthin : Thin G δ) (r s : ℕ → V)
    (hr : ∀ i j, G.dist (r i) (r j) = Nat.dist i j)
    (hs : ∀ i j, G.dist (s i) (s j) = Nat.dist i j)
    (hbounded : ∃ C : ℕ, ∀ n, G.dist (r n) (s n) ≤ C) :
    ∀ n, G.dist (r n) (s n) ≤ 3 * G.dist (r 0) (s 0) + 4*δ := by
  obtain ⟨t,ht₀,ht,hts⟩ := exists_rebased_ray hG hfin hthin s hs (r 0)
  obtain ⟨C,hC⟩ := hbounded
  have hrt : ∃ C : ℕ, ∀ n, G.dist (r n) (t n) ≤ C := by
    refine ⟨C + (3 * G.dist (r 0) (s 0) + 2*δ), fun n => ?_⟩
    have h := @Connected.dist_triangle _ G (r n) (s n) (t n) hG
    rw [SimpleGraph.dist_comm (u := s n) (v := t n)] at h
    exact h.trans (Nat.add_le_add (hC n) (hts n))
  have hrt' := asymptotic_rays_uniform hG hthin r t hr ht ht₀.symm hrt
  intro n
  have h := @Connected.dist_triangle _ G (r n) (t n) (s n) hG
  have := hrt' n
  have := hts n
  omega
end CannonGraph

namespace CannonRelease
open Set Topology

universe v
variable {G : Type v} [Group G] [TopologicalSpace G] [DiscreteTopology G]
variable (D : CayleyData G)

def CayleyData.leftIso (g : G) : D.graph ≃g D.graph where
  toEquiv := Equiv.mulLeft g
  map_rel_iff' := SimpleGraph.mulCayley_adj_mul_iff_right

omit [TopologicalSpace G] [DiscreteTopology G] in
lemma CayleyData.dist_mul_left (g x y : G) :
    D.graph.dist (g*x) (g*y) = D.graph.dist x y :=
  CannonGraph.iso_dist D.connected (D.leftIso g) x y

def Asymptotic (r s : ℕ → G) : Prop := ∃ C : ℕ, ∀ n, D.graph.dist (r n) (s n) ≤ C

omit [TopologicalSpace G] [DiscreteTopology G] in
lemma Asymptotic.refl (r : ℕ → G) : Asymptotic D r r := ⟨0, fun _ => by simp⟩

omit [TopologicalSpace G] [DiscreteTopology G] in
lemma Asymptotic.symm {r s : ℕ → G} (h : Asymptotic D r s) : Asymptotic D s r := by
  obtain ⟨C,hC⟩ := h
  exact ⟨C, fun n => by rw [SimpleGraph.dist_comm]; exact hC n⟩

omit [TopologicalSpace G] [DiscreteTopology G] in
lemma Asymptotic.trans {r s t : ℕ → G} (h : Asymptotic D r s)
    (h' : Asymptotic D s t) : Asymptotic D r t := by
  obtain ⟨C,hC⟩ := h
  obtain ⟨E,hE⟩ := h'
  exact ⟨C+E, fun n => (@SimpleGraph.Connected.dist_triangle _ D.graph (r n) (s n) (t n) D.connected).trans
    (Nat.add_le_add (hC n) (hE n))⟩

omit [TopologicalSpace G] [DiscreteTopology G] in
lemma Asymptotic.mul_left {r s : ℕ → G} (h : Asymptotic D r s) (g : G) :
    Asymptotic D (fun n => g*r n) (fun n => g*s n) := by
  obtain ⟨C,hC⟩ := h
  exact ⟨C,fun n => by rw [D.dist_mul_left]; exact hC n⟩

variable (hthin : D.ThinTriangles)

include hthin in
lemma exists_translate_ray (g : G) (r : BasedRay D) :
    ∃ s : BasedRay D, Asymptotic D s.val (fun n => g*r.val n) := by
  obtain ⟨δ,hδ⟩ := hthin
  have hg : ∀ i j, D.graph.dist (g*r.val i) (g*r.val j) = Nat.dist i j :=
    fun i j => (D.dist_mul_left g _ _).trans (r.property.2 i j)
  obtain ⟨s,hs,hr,ha⟩ := CannonGraph.exists_rebased_ray D.connected
    (CannonGraph.finite_cayley_neighbors D.generators) hδ (fun n => g*r.val n)
    hg 1
  exact ⟨⟨s,hs,hr⟩,_,ha⟩

def translateRay (g : G) (r : BasedRay D) : BasedRay D :=
  (exists_translate_ray D hthin g r).choose

lemma translateRay_spec (g : G) (r : BasedRay D) :
    Asymptotic D (translateRay D hthin g r).val (fun n => g*r.val n) :=
  (exists_translate_ray D hthin g r).choose_spec

lemma translateRay_respects (g : G) {r s : BasedRay D}
    (h : (raySetoid D).r r s) :
    (raySetoid D).r (translateRay D hthin g r) (translateRay D hthin g s) :=
  Asymptotic.trans D (Asymptotic.trans D (translateRay_spec D hthin g r)
    (Asymptotic.mul_left D h g)) (Asymptotic.symm D (translateRay_spec D hthin g s))

local instance : Setoid (BasedRay D) := raySetoid D

def boundaryTranslate (g : G) : Boundary D → Boundary D :=
  Quotient.map (translateRay D hthin g) (by
    intro r s hrs
    exact translateRay_respects D hthin g hrs)

@[simp] lemma boundaryTranslate_mk (g : G) (r : BasedRay D) :
    boundaryTranslate D hthin g (Quotient.mk' r) = Quotient.mk' (translateRay D hthin g r) := rfl

lemma boundaryTranslate_one (x : Boundary D) : boundaryTranslate D hthin 1 x = x := by
  induction x using Quotient.inductionOn with
  | h r =>
    apply Quotient.sound
    change Asymptotic D (translateRay D hthin 1 r).val r.val
    simpa only [one_mul] using translateRay_spec D hthin 1 r

lemma boundaryTranslate_mul (g h : G) (x : Boundary D) :
    boundaryTranslate D hthin (g*h) x =
      boundaryTranslate D hthin g (boundaryTranslate D hthin h x) := by
  induction x using Quotient.inductionOn with
  | h r =>
    apply Quotient.sound
    have h₁ := Asymptotic.mul_left D (translateRay_spec D hthin h r) g
    have h₂ := Asymptotic.trans D (translateRay_spec D hthin g (translateRay D hthin h r)) h₁
    exact Asymptotic.trans D (translateRay_spec D hthin (g*h) r)
      (Asymptotic.symm D (by simpa only [mul_assoc] using h₂))

end CannonRelease

end
end
end
end
end
end
end
end
end

end OAI
