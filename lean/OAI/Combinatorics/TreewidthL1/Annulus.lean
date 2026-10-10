import OAI.Combinatorics.TreewidthL1.Anchors

namespace OAI

universe treewidthLevel1 treewidthLevel2

namespace BoundedTreewidthL1

section ReachableWeightedPaths
variable {V : Type*} (G : SimpleGraph V) (ℓ : G.edgeSet → ℝ)

lemma path_length_set_nonempty_of_reachable {u v : V} (hr : G.Reachable u v) :
    {r : ℝ | ∃ p : G.Walk u v, p.IsPath ∧ walkLength G ℓ p = r}.Nonempty := by
  classical
  obtain ⟨p⟩ := hr
  exact ⟨walkLength G ℓ p.toPath.val, p.toPath.val, p.toPath.property, rfl⟩

lemma shortestPathDistance_attained_of_reachable [Fintype V] {u v : V}
    (hr : G.Reachable u v) :
    ∃ p : G.Walk u v, p.IsPath ∧ walkLength G ℓ p = shortestPathDistance G ℓ u v :=
  (path_length_set_nonempty_of_reachable G ℓ hr).csInf_mem (path_length_set_finite G ℓ u v)

lemma shortestPathDistance_nonneg_of_reachable (hℓ : ∀ e, 0 ≤ ℓ e)
    {u v : V} (hr : G.Reachable u v) : 0 ≤ shortestPathDistance G ℓ u v := by
  apply le_csInf (path_length_set_nonempty_of_reachable G ℓ hr)
  rintro r ⟨p, _, rfl⟩
  exact walkLength_nonneg G ℓ hℓ p

lemma shortestPathDistance_self_of_nonneg (hℓ : ∀ e, 0 ≤ ℓ e) (u : V) :
    shortestPathDistance G ℓ u u = 0 :=
  le_antisymm (shortestPathDistance_le_walkLength G ℓ hℓ .nil)
    (shortestPathDistance_nonneg_of_reachable G ℓ hℓ .rfl)

lemma shortestPathDistance_comm_of_reachable [Fintype V] (hℓ : ∀ e, 0 ≤ ℓ e)
    {u v : V} (hr : G.Reachable u v) :
    shortestPathDistance G ℓ u v = shortestPathDistance G ℓ v u := by
  have hle {a b : V} (hab : G.Reachable a b) :
      shortestPathDistance G ℓ a b ≤ shortestPathDistance G ℓ b a := by
    obtain ⟨p, hp, heq⟩ := shortestPathDistance_attained_of_reachable G ℓ hab.symm
    rw [← heq, ← walkLength_reverse G ℓ p]
    exact shortestPathDistance_le_pathLength G ℓ hℓ p.reverse hp.reverse
  exact le_antisymm (hle hr) (hle hr.symm)

lemma shortestPathDistance_triangle_of_reachable [Fintype V] (hℓ : ∀ e, 0 ≤ ℓ e)
    {u v w : V} (huv : G.Reachable u v) (hvw : G.Reachable v w) :
    shortestPathDistance G ℓ u w ≤ shortestPathDistance G ℓ u v + shortestPathDistance G ℓ v w := by
  obtain ⟨p, _, hp⟩ := shortestPathDistance_attained_of_reachable G ℓ huv
  obtain ⟨q, _, hq⟩ := shortestPathDistance_attained_of_reachable G ℓ hvw
  rw [← hp, ← hq, ← walkLength_append G ℓ p q]
  exact shortestPathDistance_le_walkLength G ℓ hℓ (p.append q)

lemma walkLength_takeUntil_le [DecidableEq V] (hℓ : ∀ e, 0 ≤ ℓ e)
    {u v z : V} (p : G.Walk u v) (hz : z ∈ p.support) :
    walkLength G ℓ (p.takeUntil z hz) ≤ walkLength G ℓ p := by
  have h := walkLength_nonneg G ℓ hℓ (p.dropUntil z hz)
  have heq := walkLength_append G ℓ (p.takeUntil z hz) (p.dropUntil z hz)
  rw [SimpleGraph.Walk.take_spec] at heq
  linarith

lemma geodesic_split_of_reachable [Fintype V] [DecidableEq V]
    (hℓ : ∀ e, 0 ≤ ℓ e) {a b z : V} (p : G.Walk a b)
    (hmin : walkLength G ℓ p = shortestPathDistance G ℓ a b) (hz : z ∈ p.support) :
    shortestPathDistance G ℓ a z + shortestPathDistance G ℓ z b = shortestPathDistance G ℓ a b := by
  have heq : walkLength G ℓ (p.takeUntil z hz) + walkLength G ℓ (p.dropUntil z hz) =
      shortestPathDistance G ℓ a b := by
    rw [← walkLength_append, SimpleGraph.Walk.take_spec, hmin]
  have h1 := shortestPathDistance_le_walkLength G ℓ hℓ (p.takeUntil z hz)
  have h2 := shortestPathDistance_le_walkLength G ℓ hℓ (p.dropUntil z hz)
  have h3 := shortestPathDistance_triangle_of_reachable G ℓ hℓ
    (p.takeUntil z hz).reachable (p.dropUntil z hz).reachable
  linarith

/-- Intrinsic balls are connected even when the ambient graph is disconnected;
reachability is explicit, so the empty-infimum convention never adds vertices. -/
lemma reachable_openBall_connected [Fintype V] [DecidableEq V]
    (hℓ : ∀ e, 0 ≤ ℓ e) (u : V) {r : ℝ} (hr : 0 < r) :
    (G.induce {v | G.Reachable u v ∧ shortestPathDistance G ℓ u v < r}).Connected := by
  let S := {v | G.Reachable u v ∧ shortestPathDistance G ℓ u v < r}
  have hu : u ∈ S := ⟨.rfl, by simpa [shortestPathDistance_self_of_nonneg G ℓ hℓ] using hr⟩
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  refine ⟨⟨u, hu⟩, ?_⟩
  rintro ⟨v, hv⟩
  obtain ⟨p, _, hp⟩ := shortestPathDistance_attained_of_reachable G ℓ hv.1
  have hsupp : ∀ z ∈ p.support, z ∈ S := by
    intro z hz
    refine ⟨(p.takeUntil z hz).reachable, ?_⟩
    calc
      shortestPathDistance G ℓ u z ≤ walkLength G ℓ (p.takeUntil z hz) :=
        shortestPathDistance_le_walkLength G ℓ hℓ _
      _ ≤ walkLength G ℓ p := walkLength_takeUntil_le G ℓ hℓ p hz
      _ < r := hp ▸ hv.2
  exact ⟨(p.induce S hsupp).copy (Subtype.ext rfl) (Subtype.ext rfl)⟩

lemma reachable_closedBall_connected [Fintype V] [DecidableEq V]
    (hℓ : ∀ e, 0 ≤ ℓ e) (u : V) {r : ℝ} (hr : 0 ≤ r) :
    (G.induce {v | G.Reachable u v ∧ shortestPathDistance G ℓ u v ≤ r}).Connected := by
  let S := {v | G.Reachable u v ∧ shortestPathDistance G ℓ u v ≤ r}
  have hu : u ∈ S := ⟨.rfl, by simpa [shortestPathDistance_self_of_nonneg G ℓ hℓ] using hr⟩
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  refine ⟨⟨u, hu⟩, ?_⟩
  rintro ⟨v, hv⟩
  obtain ⟨p, _, hp⟩ := shortestPathDistance_attained_of_reachable G ℓ hv.1
  have hsupp : ∀ z ∈ p.support, z ∈ S := by
    intro z hz
    refine ⟨(p.takeUntil z hz).reachable, ?_⟩
    calc
      shortestPathDistance G ℓ u z ≤ walkLength G ℓ (p.takeUntil z hz) :=
        shortestPathDistance_le_walkLength G ℓ hℓ _
      _ ≤ walkLength G ℓ p := walkLength_takeUntil_le G ℓ hℓ p hz
      _ ≤ r := hp ▸ hv.2
  exact ⟨(p.induce S hsupp).copy (Subtype.ext rfl) (Subtype.ext rfl)⟩

lemma shortest_closedBall_connected [Fintype V] [DecidableEq V]
    (hG : G.Connected) (hℓ : ∀ e, 0 ≤ ℓ e) (u : V) {r : ℝ} (hr : 0 ≤ r) :
    (G.induce {v | shortestPathDistance G ℓ u v ≤ r}).Connected := by
  have heq : {v | G.Reachable u v ∧ shortestPathDistance G ℓ u v ≤ r} =
      {v | shortestPathDistance G ℓ u v ≤ r} := by
    ext v
    simp [hG u v]
  rw [← heq]
  exact reachable_closedBall_connected G ℓ hℓ u hr

end ReachableWeightedPaths

@[instance_reducible]
noncomputable def weightedMetricSpace {V : Type*} [Fintype V]
    (G : SimpleGraph V) (ℓ : G.edgeSet → ℝ)
    (hG : G.Connected) (hℓ : ∀ e, 0 < ℓ e) : MetricSpace V where
  dist := shortestPathDistance G ℓ
  dist_self := shortestPathDistance_self G ℓ hG (fun e => (hℓ e).le)
  dist_comm := shortestPathDistance_comm G ℓ hG (fun e => (hℓ e).le)
  dist_triangle := shortestPathDistance_triangle G ℓ hG (fun e => (hℓ e).le)
  eq_of_dist_eq_zero := fun {_ _} h => (shortestPathDistance_metric G ℓ hG hℓ).2.2.2.2.1 _ _ h

end BoundedTreewidthL1

namespace BoundedTreewidthL1.Annulus

variable {V : Type*}

abbrev weights (H : SimpleGraph V) (w : Sym2 V → ℝ) : H.edgeSet → ℝ := fun e => w e.val

noncomputable def distance (H : SimpleGraph V) (w : Sym2 V → ℝ) : V → V → ℝ :=
  shortestPathDistance H (weights H w)

noncomputable def root (H : SimpleGraph V) (x : V) : V :=
  Quot.out (H.connectedComponentMk x)

lemma root_reachable (H : SimpleGraph V) (x : V) : H.Reachable (root H x) x :=
  SimpleGraph.ConnectedComponent.exact (Quot.out_eq _)

lemma root_eq {H : SimpleGraph V} {x y : V} (h : H.Reachable x y) :
    root H x = root H y := congrArg Quot.out (SimpleGraph.ConnectedComponent.sound h)

lemma root_idem (H : SimpleGraph V) (x : V) : root H (root H x) = root H x :=
  root_eq (root_reachable H x)

noncomputable def height (H : SimpleGraph V) (w : Sym2 V → ℝ) (x : V) : ℝ :=
  distance H w (root H x) x

lemma walkLength_weights {H : SimpleGraph V} (w : Sym2 V → ℝ)
    {u v : V} (p : H.Walk u v) :
    walkLength H (weights H w) p = (p.edges.map w).sum := by
  induction p with
  | nil => rfl
  | cons h p ih => simp only [walkLength, SimpleGraph.Walk.edges_cons,
      List.map_cons, List.sum_cons, weights, ih]

lemma walkLength_transfer {H G : SimpleGraph V} (w : Sym2 V → ℝ)
    {u v : V} (p : H.Walk u v) (hp : ∀ e ∈ p.edges, e ∈ G.edgeSet) :
    walkLength G (weights G w) (p.transfer G hp) = walkLength H (weights H w) p := by
  simp only [walkLength_weights, SimpleGraph.Walk.edges_transfer]

lemma walkLength_mono_map {H G : SimpleGraph V} (hHG : H ≤ G) (w : Sym2 V → ℝ)
    {u v : V} (p : H.Walk u v) :
    walkLength G (weights G w) (p.map (.ofLE hHG)) = walkLength H (weights H w) p := by
  induction p with
  | nil => rfl
  | @cons u v z h p ih => simpa only [SimpleGraph.Walk.map_cons, walkLength,
      SimpleGraph.Hom.ofLE_apply, weights] using congrArg (fun r => w s(u,v) + r) ih

lemma distance_mono [Fintype V] {H G : SimpleGraph V} (hHG : H ≤ G)
    (w : Sym2 V → ℝ) (hw : ∀ e, 0 ≤ w e) {u v : V} (huv : H.Reachable u v) :
    distance G w u v ≤ distance H w u v := by
  obtain ⟨p, _, hp⟩ := shortestPathDistance_attained_of_reachable H (weights H w) huv
  change shortestPathDistance G (weights G w) u v ≤ shortestPathDistance H (weights H w) u v
  rw [← hp, ← walkLength_mono_map hHG w p]
  exact shortestPathDistance_le_walkLength G (weights G w) (fun e => hw e.val) _

lemma distance_edge (H : SimpleGraph V) (w : Sym2 V → ℝ) (hw : ∀ e, 0 ≤ w e)
    {u v : V} (huv : H.Adj u v) : distance H w u v ≤ w s(u,v) := by
  simpa [distance, walkLength, weights] using
    shortestPathDistance_le_walkLength H (weights H w) (fun e => hw e.val) huv.toWalk

lemma height_nonneg (H : SimpleGraph V) (w : Sym2 V → ℝ) (hw : ∀ e, 0 ≤ w e)
    (x : V) : 0 ≤ height H w x :=
  shortestPathDistance_nonneg_of_reachable H (weights H w) (fun e => hw e.val)
    (root_reachable H x)

lemma height_root (H : SimpleGraph V) (w : Sym2 V → ℝ) (hw : ∀ e, 0 ≤ w e)
    (x : V) : height H w (root H x) = 0 := by
  simp only [height, root_idem, distance]
  exact shortestPathDistance_self_of_nonneg H (weights H w) (fun e => hw e.val) _

lemma height_eq_of_reachable {H : SimpleGraph V} (w : Sym2 V → ℝ) {x y : V}
    (hxy : H.Reachable x y) : height H w y = distance H w (root H x) y := by
  simp only [height, root_eq hxy]

lemma height_le_add_distance [Fintype V] (H : SimpleGraph V) (w : Sym2 V → ℝ)
    (hw : ∀ e, 0 ≤ w e) {x y : V} (hxy : H.Reachable x y) :
    height H w y ≤ height H w x + distance H w x y := by
  rw [height_eq_of_reachable w hxy]
  exact shortestPathDistance_triangle_of_reachable H (weights H w) (fun e => hw e.val)
    (root_reachable H x) hxy

lemma height_edge [Fintype V] (H : SimpleGraph V) (w : Sym2 V → ℝ)
    (hw : ∀ e, 0 ≤ w e) {x y : V} (hxy : H.Adj x y) :
    height H w y ≤ height H w x + w s(x,y) := by
  have h1 := height_le_add_distance H w hw hxy.reachable
  have h2 := distance_edge H w hw hxy
  linarith

/-- The predecessor of a first height crossing is strictly inside the ball. -/
lemma walk_crossing_below (H : SimpleGraph V) (f : V → ℝ) {ε t : ℝ}
    (hstep : ∀ a b, H.Adj a b → f b ≤ f a + ε)
    {u v : V} (p : H.Walk u v) (hu : f u < t) (hv : t ≤ f v) :
    ∃ z ∈ p.support, t - ε ≤ f z ∧ f z < t := by
  induction p with
  | nil => exact (not_lt_of_ge hv hu).elim
  | @cons a b c hab p ih =>
    by_cases hb : f b < t
    · obtain ⟨z, hz, hlo, hhi⟩ := ih hb hv
      exact ⟨z, by simp [hz], hlo, hhi⟩
    · have hs := hstep a b hab
      exact ⟨a, by simp, by linarith, hu⟩

/-- The strict intrinsic inner ball, with reachability explicitly imposed. -/
def inner (H : SimpleGraph V) (w : Sym2 V → ℝ) (x : V) (t : ℝ) : Set V :=
  {z | H.Reachable (root H x) z ∧ distance H w (root H x) z < t}

lemma inner_connected [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (w : Sym2 V → ℝ) (hw : ∀ e, 0 ≤ w e) (x : V) {t : ℝ} (ht : 0 < t) :
    (H.induce (inner H w x t)).Connected :=
  reachable_openBall_connected H (weights H w) (fun e => hw e.val) (root H x) ht

lemma inner_reachable {H : SimpleGraph V} {w : Sym2 V → ℝ} {x z : V} {t : ℝ}
    (hz : z ∈ inner H w x t) : H.Reachable x z :=
  (root_reachable H x).symm.trans hz.1

lemma inner_height {H : SimpleGraph V} {w : Sym2 V → ℝ} {x z : V} {t : ℝ}
    (hz : z ∈ inner H w x t) : height H w z < t := by
  rw [height_eq_of_reachable w (inner_reachable hz)]
  exact hz.2

lemma inner_dominates [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) (w : Sym2 V → ℝ) (hw : ∀ e, 0 ≤ w e)
    {ε : ℝ} (hmesh : ∀ u v, H.Adj u v → w s(u,v) ≤ ε)
    (x c : V) (hxc : H.Reachable x c) {t R : ℝ}
    (ht : 0 < t) (hlo : t ≤ height H w c) (hhi : height H w c ≤ t + R) :
    ∃ z ∈ inner H w x t, distance H w c z ≤ R + ε := by
  have hrc := (root_reachable H x).trans hxc
  obtain ⟨p, _, hp⟩ := shortestPathDistance_attained_of_reachable H (weights H w) hrc
  have hstep : ∀ a b, H.Adj a b → height H w b ≤ height H w a + ε := by
    intro a b hab
    have h1 := height_edge H w hw hab
    have h2 := hmesh a b hab
    linarith
  obtain ⟨z, hz, hzlo, hzhi⟩ := walk_crossing_below H (height H w) hstep p
    (by simpa [height_root H w hw] using ht) hlo
  have hrz := (p.takeUntil z hz).reachable
  have hxz := (root_reachable H x).symm.trans hrz
  have hzheight := height_eq_of_reachable w hxz
  have hcHeight := height_eq_of_reachable w hxc
  refine ⟨z, ⟨hrz, by rwa [← hzheight]⟩, ?_⟩
  have hsplit := geodesic_split_of_reachable H (weights H w) (fun e => hw e.val) p hp hz
  have hsym := shortestPathDistance_comm_of_reachable H (weights H w) (fun e => hw e.val)
    (p.dropUntil z hz).reachable
  change distance H w (root H x) z + distance H w z c = distance H w (root H x) c at hsplit
  change distance H w z c = distance H w c z at hsym
  rw [← hzheight, ← hcHeight, hsym] at hsplit
  linarith

noncomputable def band (H : SimpleGraph V) (w : Sym2 V → ℝ) (R a : ℝ) (x : V) : ℤ :=
  ⌊(height H w x + a) / R⌋

noncomputable def cut (H : SimpleGraph V) (w : Sym2 V → ℝ) (R a : ℝ) : SimpleGraph V where
  Adj u v := H.Adj u v ∧ band H w R a u = band H w R a v
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => H.irrefl h.1⟩

lemma cut_le (H : SimpleGraph V) (w : Sym2 V → ℝ) (R a : ℝ) : cut H w R a ≤ H :=
  fun _ _ h => h.1

lemma band_eq_of_cut_reachable {H : SimpleGraph V} {w : Sym2 V → ℝ} {R a : ℝ}
    {x y : V} (h : (cut H w R a).Reachable x y) : band H w R a x = band H w R a y := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => rfl
  | cons h p ih => exact h.2.trans ih

lemma band_bounds (H : SimpleGraph V) (w : Sym2 V → ℝ) {R : ℝ} (hR : 0 < R)
    (a : ℝ) (x : V) :
    (band H w R a x : ℝ) * R - a ≤ height H w x ∧
      height H w x < (band H w R a x : ℝ) * R - a + R := by
  have hlo := Int.floor_le ((height H w x + a) / R)
  have hhi := Int.lt_floor_add_one ((height H w x + a) / R)
  have hlo' := (le_div_iff₀ hR).mp hlo
  have hhi' := (div_lt_iff₀ hR).mp hhi
  change (band H w R a x : ℝ) * R ≤ height H w x + a at hlo'
  change height H w x + a < ((band H w R a x : ℝ) + 1) * R at hhi'
  constructor <;> nlinarith

lemma band_nonneg (H : SimpleGraph V) (w : Sym2 V → ℝ) (hw : ∀ e, 0 ≤ w e)
    {R a : ℝ} (hR : 0 < R) (ha : 0 ≤ a) (x : V) : 0 ≤ band H w R a x :=
  Int.floor_nonneg.mpr (div_nonneg (add_nonneg (height_nonneg H w hw x) ha) hR.le)

/-- A single annulus either is close to its root, or has a connected inner
ball deleted from its component and uniformly close to all of that component. -/
theorem cut_component_alternative [Fintype V] [DecidableEq V]
    (G H : SimpleGraph V) (hHG : H ≤ G)
    (w : Sym2 V → ℝ) (hw : ∀ e, 0 ≤ w e)
    {R a ε : ℝ} (hR : 0 < R) (ha0 : 0 ≤ a) (haR : a < R)
    (hmesh : ∀ u v, H.Adj u v → w s(u,v) ≤ ε) (x : V) :
    (∀ y z, (cut H w R a).Reachable x y → (cut H w R a).Reachable x z →
      distance G w y z ≤ 2 * R) ∨
    ∃ B : Set V, (G.induce B).Connected ∧
      (∀ z ∈ B, H.Reachable x z) ∧
      (∀ z ∈ B, ¬(cut H w R a).Reachable x z) ∧
      ∀ c, (cut H w R a).Reachable x c → ∃ z ∈ B, distance G w c z ≤ R + ε := by
  let n := band H w R a x
  have hn : 0 ≤ n := band_nonneg H w hw hR ha0 x
  by_cases hn0 : n = 0
  · left
    intro y z hxy hxz
    have hy := (band_bounds H w hR a y).2
    have hz := (band_bounds H w hR a z).2
    have hby : band H w R a y = 0 := (band_eq_of_cut_reachable hxy).symm.trans hn0
    have hbz : band H w R a z = 0 := (band_eq_of_cut_reachable hxz).symm.trans hn0
    rw [hby] at hy
    rw [hbz] at hz
    have hyR : height H w y ≤ R := by simp only [Int.cast_zero, zero_mul, zero_sub] at hy; linarith
    have hzR : height H w z ≤ R := by simp only [Int.cast_zero, zero_mul, zero_sub] at hz; linarith
    have hHy := hxy.mono (cut_le H w R a)
    have hHz := hxz.mono (cut_le H w R a)
    have hry := (root_reachable H x).trans hHy
    have hrz := (root_reachable H x).trans hHz
    have hm := distance_mono hHG w hw (hHy.symm.trans hHz)
    have ht := shortestPathDistance_triangle_of_reachable H (weights H w) (fun e => hw e.val)
      hry.symm hrz
    have hs := shortestPathDistance_comm_of_reachable H (weights H w) (fun e => hw e.val) hry
    change distance H w y z ≤ distance H w y (root H x) + distance H w (root H x) z at ht
    change distance H w (root H x) y = distance H w y (root H x) at hs
    rw [← hs, ← height_eq_of_reachable w hHy, ← height_eq_of_reachable w hHz] at ht
    linarith
  · right
    have hn1 : (1 : ℤ) ≤ n := by omega
    have hn1r : (1 : ℝ) ≤ n := by exact_mod_cast hn1
    let t : ℝ := (n : ℝ) * R - a
    have ht : 0 < t := by dsimp [t]; nlinarith
    refine ⟨inner H w x t, (inner_connected H w hw x ht).mono (fun _ _ h => hHG h),
      fun _ hz => inner_reachable hz, ?_, ?_⟩
    · intro z hz hcz
      have hzb := (band_eq_of_cut_reachable hcz).symm
      have hzlo := (band_bounds H w hR a z).1
      rw [hzb] at hzlo
      exact (inner_height hz).not_ge hzlo
    · intro c hxc
      have hHxc := hxc.mono (cut_le H w R a)
      have hcb := (band_eq_of_cut_reachable hxc).symm
      have hc := band_bounds H w hR a c
      rw [hcb] at hc
      obtain ⟨z, hz, hnear⟩ := inner_dominates H w hw hmesh x c hHxc ht hc.1 hc.2.le
      refine ⟨z, hz, (distance_mono hHG w hw ?_).trans hnear⟩
      exact hHxc.symm.trans (inner_reachable hz)

variable {A : Type*}

/-- Successive annulus cuts, with one finite random choice at each round. -/
noncomputable def run (w : Sym2 V → ℝ) (R : ℝ) (offset : A → ℝ) :
    (n : ℕ) → SimpleGraph V → (Fin n → A) → SimpleGraph V
  | 0, H, _ => H
  | n + 1, H, σ => run w R offset n (cut H w R (offset (σ 0))) (fun i => σ i.succ)

lemma run_le (w : Sym2 V → ℝ) (R : ℝ) (offset : A → ℝ)
    (n : ℕ) (H : SimpleGraph V) (σ : Fin n → A) : run w R offset n H σ ≤ H := by
  induction n generalizing H with
  | zero => exact le_rfl
  | succ n ih => exact (ih _ _).trans (cut_le H w R _)

/-- Connected barriers around a final component. The inside/outside fields are
what permit nested cuts to add one more *disjoint* barrier at each round. -/
structure BarrierFamily (G H F : SimpleGraph V) (w : Sym2 V → ℝ)
    (ρ : ℝ) (x : V) (n : ℕ) where
  sets : Fin n → Set V
  connected : ∀ i, (G.induce (sets i)).Connected
  inside : ∀ i z, z ∈ sets i → H.Reachable x z
  outside : ∀ i z, z ∈ sets i → ¬F.Reachable x z
  separated : Pairwise (fun i j => Disjoint (sets i) (sets j))
  dominates : ∀ i c, F.Reachable x c → ∃ z ∈ sets i, distance G w c z ≤ ρ

/-- Deterministic invariant of the annulus recursion. A large component has
one genuinely connected, disjoint nearby barrier for every cut round. -/
theorem run_component_alternative [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (w : Sym2 V → ℝ) (hw : ∀ e, 0 ≤ w e)
    {R ε : ℝ} (hR : 0 < R) (offset : A → ℝ)
    (hoff0 : ∀ a, 0 ≤ offset a) (hoffR : ∀ a, offset a < R)
    (n : ℕ) (H : SimpleGraph V) (hHG : H ≤ G)
    (hmesh : ∀ u v, H.Adj u v → w s(u,v) ≤ ε) (σ : Fin n → A) (x : V) :
    (∀ y z, (run w R offset n H σ).Reachable x y →
      (run w R offset n H σ).Reachable x z → distance G w y z ≤ 2 * R) ∨
    Nonempty (BarrierFamily G H (run w R offset n H σ) w (R + ε) x n) := by
  induction n generalizing H with
  | zero =>
    right
    exact ⟨{ sets := Fin.elim0
             connected := fun i => Fin.elim0 i
             inside := fun i => Fin.elim0 i
             outside := fun i => Fin.elim0 i
             separated := fun i => Fin.elim0 i
             dominates := fun i => Fin.elim0 i }⟩
  | succ n ih =>
    let H' := cut H w R (offset (σ 0))
    let τ : Fin n → A := fun i => σ i.succ
    let F := run w R offset n H' τ
    have hF : run w R offset (n + 1) H σ = F := rfl
    rw [hF]
    have hH'H : H' ≤ H := cut_le H w R _
    have hFH' : F ≤ H' := run_le w R offset n H' τ
    have halt := cut_component_alternative G H hHG w hw hR (hoff0 (σ 0))
      (hoffR (σ 0)) hmesh x
    rcases halt with hsmall | ⟨B, hB, hBin, hBout, hBdom⟩
    · left
      exact fun y z hy hz => hsmall y z (hy.mono hFH') (hz.mono hFH')
    · have hH'G := hH'H.trans hHG
      have hmesh' : ∀ u v, H'.Adj u v → w s(u,v) ≤ ε := fun u v h => hmesh u v (hH'H h)
      rcases ih H' hH'G hmesh' τ with hsmall | hex
      · exact Or.inl hsmall
      · obtain ⟨D⟩ := hex
        right
        refine ⟨{
          sets := Fin.cons B D.sets
          connected := ?_
          inside := ?_
          outside := ?_
          separated := ?_
          dominates := ?_ }⟩
        · intro i
          refine Fin.cases hB (fun j => D.connected j) i
        · intro i
          refine Fin.cases hBin ?_ i
          intro j z hz
          exact (D.inside j z hz).mono hH'H
        · intro i
          refine Fin.cases ?_ (fun j => D.outside j) i
          intro z hz hFz
          exact hBout z hz (hFz.mono hFH')
        · intro i j
          refine Fin.cases ?_ ?_ i
          · refine Fin.cases ?_ ?_ j
            · intro hij; exact (hij rfl).elim
            · intro l _
              apply Set.disjoint_left.mpr
              intro z hzB hzD
              exact hBout z hzB (D.inside l z hzD)
          · intro l
            refine Fin.cases ?_ ?_ j
            · intro _; apply Set.disjoint_left.mpr
              intro z hzD hzB
              exact hBout z hzB (D.inside l z hzD)
            · intro m hij
              exact D.separated (fun hlm => hij (congrArg Fin.succ hlm))
        · intro i
          refine Fin.cases ?_ (fun j => D.dominates j) i
          intro c hc
          exact hBdom c (hc.mono hFH')

lemma reachable_set_connected [DecidableEq V] (H : SimpleGraph V) (x : V) :
    (H.induce {z | H.Reachable x z}).Connected := by
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  refine ⟨⟨x, .rfl⟩, ?_⟩
  rintro ⟨z, hz⟩
  obtain ⟨p⟩ := hz
  have hsupp : ∀ y ∈ p.support, H.Reachable x y := fun y hy => (p.takeUntil y hy).reachable
  exact ⟨(p.induce {z | H.Reachable x z} hsupp).copy (Subtype.ext rfl) (Subtype.ext rfl)⟩

end BoundedTreewidthL1.Annulus

namespace BoundedTreewidthL1

/-- Convexity with respect to the unique simple paths in a tree. -/
def TreePathClosed {I : Type*} (T : SimpleGraph I) (S : Set I) : Prop :=
  ∀ ⦃u v : I⦄, u ∈ S → v ∈ S → ∀ (p : T.Walk u v), p.IsPath →
    ∀ z ∈ p.support, z ∈ S

private theorem tree_helly_aux (n : ℕ) :
    ∀ {I J : Type*} [Fintype I], Fintype.card I ≤ n →
    ∀ (T : SimpleGraph I), T.IsTree → ∀ (S : J → Set I),
    (∀ j, (S j).Nonempty) → (∀ j, TreePathClosed T (S j)) →
    (∀ i j, (S i ∩ S j).Nonempty) → ∃ v, ∀ j, v ∈ S j := by
  classical
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro I J _ hn T hT S hne hconv hpair
    have : Nonempty I := hT.connected.nonempty
    by_cases hsub : Subsingleton I
    · let := hsub
      refine ⟨Classical.choice (inferInstance : Nonempty I), ?_⟩
      intro j
      obtain ⟨z, hz⟩ := hne j
      simpa only [Subsingleton.elim (Classical.choice (inferInstance : Nonempty I)) z] using hz
    · let : Nontrivial I := not_subsingleton_iff_nontrivial.mp hsub
      obtain ⟨v, hv⟩ := hT.exists_vert_degree_one_of_nontrivial
      obtain ⟨u, hvu, huniq⟩ := SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp hv
      by_cases hsingle : ∃ j, S j = {v}
      · obtain ⟨j, hj⟩ := hsingle
        refine ⟨v, fun i => ?_⟩
        obtain ⟨z, hzj, hzi⟩ := hpair j i
        have hzv : z = v := by simpa [hj] using hzj
        exact hzv ▸ hzi
      · have hneighbor : ∀ j, v ∈ S j → u ∈ S j := by
          intro j hvj
          have hex : ∃ w ∈ S j, w ≠ v := by
            by_contra! hh
            apply hsingle
            refine ⟨j, Set.Subset.antisymm ?_ ?_⟩
            · intro w hw
              exact Set.mem_singleton_iff.mpr (hh w hw)
            · simpa only [Set.singleton_subset_iff] using hvj
          obtain ⟨w, hw, hwv⟩ := hex
          obtain ⟨p, hp⟩ := hT.connected.exists_isPath v w
          have hnil : ¬p.Nil := SimpleGraph.Walk.not_nil_of_ne hwv.symm
          have hsu : p.snd = u := huniq _ (p.adj_snd hnil)
          exact hsu ▸ hconv j hvj hw p hp _ (p.getVert_mem_support 1)
        let I' := {x : I // x ∈ ({v} : Set I)ᶜ}
        let T' : SimpleGraph I' := T.induce {v}ᶜ
        let S' : J → Set I' := fun j => {x | x.val ∈ S j}
        have hunv : u ∈ ({v} : Set I)ᶜ := by
          simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hvu.ne'
        have hT' : T'.IsTree :=
          ⟨hT.connected.induce_compl_singleton_of_degree_eq_one hv,
            hT.isAcyclic.induce _⟩
        have hne' : ∀ j, (S' j).Nonempty := by
          intro j
          obtain ⟨z, hz⟩ := hne j
          by_cases hzv : z = v
          · exact ⟨⟨u, hunv⟩, hneighbor j (hzv ▸ hz)⟩
          · exact ⟨⟨z, by simpa using hzv⟩, hz⟩
        have hconv' : ∀ j, TreePathClosed T' (S' j) := by
          intro j a b ha hb p hp z hz
          let f := (SimpleGraph.Embedding.induce (G := T) ({v} : Set I)ᶜ).toHom
          have hp' : (p.map f).IsPath := hp.map Subtype.val_injective
          have hmem : f z ∈ (p.map f).support := by
            rw [SimpleGraph.Walk.support_map]
            exact List.mem_map.mpr ⟨z, hz, rfl⟩
          exact hconv j ha hb (p.map f) hp' (f z) hmem
        have hpair' : ∀ i j, (S' i ∩ S' j).Nonempty := by
          intro i j
          obtain ⟨z, hzi, hzj⟩ := hpair i j
          by_cases hzv : z = v
          · exact ⟨⟨u, hunv⟩, hneighbor i (hzv ▸ hzi), hneighbor j (hzv ▸ hzj)⟩
          · exact ⟨⟨z, by simpa using hzv⟩, hzi, hzj⟩
        have hcard : Fintype.card I' < Fintype.card I :=
          Fintype.card_subtype_lt (x := v) (by simp)
        obtain ⟨z, hz⟩ := ih (Fintype.card I') (lt_of_lt_of_le hcard hn)
          (le_refl _) T' hT' S' hne' hconv' hpair'
        exact ⟨z.val, hz⟩

/-- Finite trees have the Helly property for connected vertex sets.  The index
family need not be finite. This is the exact combinatorial input for the
bounded-treewidth padded-partition construction, not a main theorem claim. -/
theorem tree_subtree_helly {I J : Type*} [Fintype I]
    (T : SimpleGraph I) (hT : T.IsTree) (S : J → Set I)
    (hS : ∀ j, (T.induce (S j)).Connected)
    (hpair : ∀ i j, (S i ∩ S j).Nonempty) :
    ∃ v, ∀ j, v ∈ S j := by
  have hne : ∀ j, (S j).Nonempty := fun j => (Set.nonempty_coe_sort.mp (hS j).nonempty)
  have hconv : ∀ j, TreePathClosed T (S j) := by
    intro j u v hu hv p hp z hz
    exact tree_path_mem_connected T hT (hS j) hu hv p hp hz
  exact tree_helly_aux (Fintype.card I) (le_refl _) T hT S hne hconv hpair

/-- An arbitrary nonempty connected vertex set touches a connected set of bags. -/
lemma touched_bags_connected_set {V I : Type*} [DecidableEq V]
    (G : SimpleGraph V) (T : SimpleGraph I) (bag : I → Finset V)
    (hedge : ∀ u v, G.Adj u v → ∃ t, u ∈ bag t ∧ v ∈ bag t)
    (hocc : ∀ v, (T.induce {t | v ∈ bag t}).Connected)
    (S : Set V) (hS : (G.induce S).Connected) :
    (T.induce {t | ∃ z ∈ S, z ∈ bag t}).Connected := by
  obtain ⟨u, hu⟩ := hS.nonempty
  obtain ⟨A, hA⟩ := (hocc u).nonempty
  apply T.induce_connected_of_patches (s := {t | ∃ z ∈ S, z ∈ bag t}) A ⟨u, hu, hA⟩
  rintro B ⟨v, hv, hB⟩
  obtain ⟨p⟩ := hS ⟨u, hu⟩ ⟨v, hv⟩
  let f := (SimpleGraph.Embedding.induce (G := G) S).toHom
  let q := p.map f
  refine ⟨{t | ∃ z ∈ q.support, z ∈ bag t}, ?_,
    ⟨u, q.start_mem_support, hA⟩, ⟨v, q.end_mem_support, hB⟩, ?_⟩
  · rintro t ⟨z, hz, hzt⟩
    have hzS : z ∈ S := by
      change z ∈ (p.map f).support at hz
      rw [SimpleGraph.Walk.support_map] at hz
      obtain ⟨a, _, rfl⟩ := List.mem_map.mp hz
      exact a.property
    exact ⟨z, hzS, hzt⟩
  · exact touched_bags_connected G T bag hedge hocc q _ _

lemma card_le_of_pairwise_disjoint_hits {V A : Type*} [DecidableEq V] [Fintype A]
    (bag : Finset V) (X : A → Set V)
    (hdis : Pairwise (fun i j => Disjoint (X i) (X j)))
    (hhit : ∀ i, ∃ v ∈ X i, v ∈ bag) : Fintype.card A ≤ bag.card := by
  classical
  choose f hfX hfb using hhit
  let g : A → ↥bag := fun i => ⟨f i, hfb i⟩
  have hinj : Function.Injective g := by
    intro i j hij
    by_contra hne
    have hf : f i = f j := congrArg Subtype.val hij
    exact Set.disjoint_left.mp (hdis hne) (hfX i) (hf.symm ▸ hfX j)
  simpa using Fintype.card_le_of_injective g hinj

/-- A crossbar of two internally disjoint families of connected sets forces
a bag meeting every member of one family. Consequently its size is at least
the smaller family cardinality. This is the deterministic width obstruction
used by iterated annulus partitions. -/
theorem tree_decomposition_crossbar {V I A B : Type*} [DecidableEq V]
    [Fintype I] [Fintype A] [Fintype B]
    (G : SimpleGraph V) (T : SimpleGraph I) (bag : I → Finset V)
    (hT : T.IsTree)
    (hedge : ∀ u v, G.Adj u v → ∃ t, u ∈ bag t ∧ v ∈ bag t)
    (hocc : ∀ v, (T.induce {t | v ∈ bag t}).Connected)
    (X : A → Set V) (Y : B → Set V)
    (hX : ∀ i, (G.induce (X i)).Connected)
    (hY : ∀ j, (G.induce (Y j)).Connected)
    (hdisX : Pairwise (fun i j => Disjoint (X i) (X j)))
    (hdisY : Pairwise (fun i j => Disjoint (Y i) (Y j)))
    (hcross : ∀ i j, (X i ∩ Y j).Nonempty) :
    ∃ t, min (Fintype.card A) (Fintype.card B) ≤ (bag t).card := by
  classical
  let S : A × B → Set I := fun p => {t | ∃ z ∈ X p.1 ∪ Y p.2, z ∈ bag t}
  have hS : ∀ p, (T.induce (S p)).Connected := by
    intro p
    exact touched_bags_connected_set G T bag hedge hocc _
      (SimpleGraph.induce_union_connected (hX p.1).preconnected (hY p.2).preconnected
        (hcross p.1 p.2))
  have hpair : ∀ p q, (S p ∩ S q).Nonempty := by
    intro p q
    obtain ⟨z, hzX, hzY⟩ := hcross p.1 q.2
    obtain ⟨t, ht⟩ := (hocc z).nonempty
    exact ⟨t, ⟨z, Or.inl hzX, ht⟩, ⟨z, Or.inr hzY, ht⟩⟩
  obtain ⟨t, ht⟩ := tree_subtree_helly T hT S hS hpair
  refine ⟨t, ?_⟩
  by_cases hall : ∀ i, ∃ z ∈ X i, z ∈ bag t
  · exact le_trans (min_le_left _ _) (card_le_of_pairwise_disjoint_hits (bag t) X hdisX hall)
  · push Not at hall
    obtain ⟨i, hi⟩ := hall
    have hYhit : ∀ j, ∃ z ∈ Y j, z ∈ bag t := by
      intro j
      obtain ⟨z, hzX | hzY, hzt⟩ := ht (i, j)
      · exact (hi z hzX hzt).elim
      · exact ⟨z, hzY, hzt⟩
    exact le_trans (min_le_right _ _) (card_le_of_pairwise_disjoint_hits (bag t) Y hdisY hYhit)

/-- A discrete intermediate-value bound with an explicit mesh error. -/
lemma walk_crossing_window {V : Type*} (H : SimpleGraph V) (f : V → ℝ)
    {ε t : ℝ} (hε : 0 ≤ ε)
    (hstep : ∀ a b, H.Adj a b → f b ≤ f a + ε)
    {u v : V} (p : H.Walk u v) (hu : f u ≤ t) (hv : t ≤ f v) :
    ∃ z ∈ p.support, t ≤ f z ∧ f z ≤ t + ε := by
  induction p with
  | @nil x => exact ⟨x, by simp, hv, by linarith⟩
  | @cons a b c hab p ih =>
    by_cases hb : f b ≤ t
    · obtain ⟨z, hz, ht, he⟩ := ih hb hv
      exact ⟨z, by simp [hz], ht, he⟩
    · refine ⟨b, ?_, le_of_lt (lt_of_not_ge hb), ?_⟩
      · simp only [SimpleGraph.Walk.support_cons, List.mem_cons]
        exact Or.inr p.start_mem_support
      · exact (hstep a b hab).trans (by linarith : f a + ε ≤ t + ε)

/-- The deterministic diameter obstruction behind the annulus algorithm.
The radius balls are in the original metric; only the connectivity walk in C
uses the small-edge subgraph H. No intrinsic diameter replaces weak diameter. -/
theorem connected_multidomination_diameter {V I : Type*} [MetricSpace V]
    [DecidableEq V] [Fintype I]
    (G H : SimpleGraph V) (hHG : H ≤ G)
    (T : SimpleGraph I) (bag : I → Finset V) (k : ℕ)
    (hT : T.IsTree)
    (hedge : ∀ u v, G.Adj u v → ∃ t, u ∈ bag t ∧ v ∈ bag t)
    (hocc : ∀ v, (T.induce {t | v ∈ bag t}).Connected)
    (hwidth : ∀ t, (bag t).card ≤ k)
    {R ε : ℝ} (hR : 0 ≤ R) (hε : 0 < ε)
    (hmesh : ∀ u v, H.Adj u v → dist u v ≤ ε)
    (hballs : ∀ c, (G.induce {z | dist c z ≤ R}).Connected)
    (C : Set V) (hC : (H.induce C).Connected)
    (B : Fin k → Set V) (hB : ∀ i, (G.induce (B i)).Connected)
    (hdisB : Pairwise (fun i j => Disjoint (B i) (B j)))
    (hdisC : ∀ i, Disjoint C (B i))
    (hdom : ∀ i c, c ∈ C → ∃ z ∈ B i, dist c z ≤ R) :
    ∀ u ∈ C, ∀ v ∈ C, dist u v ≤ (k : ℝ) * (2 * R + 2 * ε) := by
  classical
  intro u hu v hv
  by_contra hle
  have hfar : (k : ℝ) * (2 * R + 2 * ε) < dist u v := lt_of_not_ge hle
  obtain ⟨p⟩ := hC ⟨u, hu⟩ ⟨v, hv⟩
  let a : ℝ := 2 * R + 2 * ε
  have ha : 0 < a := by dsimp [a]; positivity
  have hstep : ∀ x y : C, (H.induce C).Adj x y → dist u y.val ≤ dist u x.val + ε := by
    intro x y hxy
    have hm := hmesh x.val y.val hxy
    have ht := dist_triangle u x.val y.val
    linarith
  have hex : ∀ i : Fin (k + 1), ∃ c : C,
      (i.val : ℝ) * a ≤ dist u c.val ∧ dist u c.val ≤ (i.val : ℝ) * a + ε := by
    intro i
    have hstart : dist u (⟨u, hu⟩ : C).val ≤ (i.val : ℝ) * a := by
      simp only [dist_self]
      positivity
    have hend : (i.val : ℝ) * a ≤ dist u (⟨v, hv⟩ : C).val := by
      have hi : (i.val : ℝ) ≤ k := by exact_mod_cast (Nat.le_of_lt_succ i.isLt)
      exact (mul_le_mul_of_nonneg_right hi ha.le).trans hfar.le
    obtain ⟨c, _, hc⟩ := walk_crossing_window (H.induce C) (fun x : C => dist u x.val)
      hε.le hstep p hstart hend
    exact ⟨c, hc⟩
  choose c hclo hchi using hex
  have hsep : ∀ i j : Fin (k + 1), i.val < j.val → 2 * R < dist (c i).val (c j).val := by
    intro i j hij
    have hijr : (i.val : ℝ) + 1 ≤ j.val := by exact_mod_cast (Nat.succ_le_iff.mpr hij)
    have hm := mul_le_mul_of_nonneg_right hijr ha.le
    have ht := dist_triangle u (c i).val (c j).val
    have hlo := hclo j
    have hhi := hchi i
    dsimp [a] at *
    nlinarith
  let Y : Fin (k + 1) → Set V := fun i => {z | dist (c i).val z ≤ R}
  have hY : ∀ i, (G.induce (Y i)).Connected := fun i => hballs _
  have hdisY : Pairwise (fun i j => Disjoint (Y i) (Y j)) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro z hzi hzj
    have hnear : dist (c i).val (c j).val ≤ 2 * R := by
      have ht := dist_triangle (c i).val z (c j).val
      have hzj' : dist z (c j).val ≤ R := by simpa [Y, dist_comm] using hzj
      change dist (c i).val z ≤ R at hzi
      linarith
    have hvne : i.val ≠ j.val := fun h => hij (Fin.ext h)
    rcases lt_or_gt_of_ne hvne with hlt | hgt
    · exact (hsep i j hlt).not_ge hnear
    · exact (hsep j i hgt).not_ge (by simpa [dist_comm] using hnear)
  let X : Option (Fin k) → Set V := fun i => i.elim C B
  have hCG : (G.induce C).Connected := hC.mono (fun _ _ h => hHG h)
  have hX : ∀ i, (G.induce (X i)).Connected := by
    intro i
    cases i with
    | none => exact hCG
    | some i => exact hB i
  have hdisX : Pairwise (fun i j => Disjoint (X i) (X j)) := by
    intro i j hij
    cases i with
    | none =>
      cases j with
      | none => exact (hij rfl).elim
      | some j => exact hdisC j
    | some i =>
      cases j with
      | none => exact (hdisC i).symm
      | some j => exact hdisB (fun h => hij (congrArg some h))
  have hcross : ∀ i j, (X i ∩ Y j).Nonempty := by
    intro i j
    cases i with
    | none => exact ⟨(c j).val, (c j).property, by simpa [Y] using hR⟩
    | some i => exact hdom i (c j).val (c j).property
  obtain ⟨t, ht⟩ := tree_decomposition_crossbar G T bag hT hedge hocc X Y hX hY hdisX hdisY hcross
  have ht' : k + 1 ≤ (bag t).card := by simpa using ht
  have := hwidth t
  omega

end BoundedTreewidthL1

namespace BoundedTreewidthL1.Annulus

/-- The finite-round annulus decomposition has weak diameter bounded solely
by the width and scale. The metric here remains the original graph metric. -/
theorem run_diameter {V I A : Type*} [Fintype V] [DecidableEq V] [MetricSpace V]
    [Fintype I] (G H : SimpleGraph V) (hHG : H ≤ G)
    (w : Sym2 V → ℝ) (hw : ∀ e, 0 ≤ w e)
    (hdist : ∀ u v, dist u v = distance G w u v)
    (T : SimpleGraph I) (bag : I → Finset V) (k : ℕ) (hk : 1 ≤ k)
    (hT : T.IsTree)
    (hedge : ∀ u v, G.Adj u v → ∃ t, u ∈ bag t ∧ v ∈ bag t)
    (hocc : ∀ v, (T.induce {t | v ∈ bag t}).Connected)
    (hwidth : ∀ t, (bag t).card ≤ k)
    {R ε : ℝ} (hR : 0 < R) (hε : 0 < ε)
    (hmesh : ∀ u v, H.Adj u v → w s(u,v) ≤ ε)
    (hballs : ∀ c, (G.induce {z | dist c z ≤ R + ε}).Connected)
    (offset : A → ℝ) (hoff0 : ∀ a, 0 ≤ offset a) (hoffR : ∀ a, offset a < R)
    (σ : Fin k → A) (u v : V) (huv : (run w R offset k H σ).Reachable u v) :
    dist u v ≤ (k : ℝ) * (2 * R + 4 * ε) := by
  have hkr : (1 : ℝ) ≤ k := by exact_mod_cast hk
  rcases run_component_alternative G w hw hR offset hoff0 hoffR k H hHG hmesh σ u with hsmall | hex
  · have hs := hsmall u v .rfl huv
    rw [hdist]
    have hfac : 0 ≤ 2 * R + 4 * ε := by positivity
    have hmul := mul_le_mul_of_nonneg_right hkr hfac
    nlinarith
  · obtain ⟨B⟩ := hex
    let F := run w R offset k H σ
    have hFH : F ≤ H := run_le w R offset k H σ
    have hFG := hFH.trans hHG
    let C : Set V := {z | F.Reachable u z}
    have hC : (F.induce C).Connected := reachable_set_connected F u
    have hCdis : ∀ i, Disjoint C (B.sets i) := by
      intro i
      apply Set.disjoint_left.mpr
      intro z hzC hzB
      exact B.outside i z hzB hzC
    have hdom : ∀ i c, c ∈ C → ∃ z ∈ B.sets i, dist c z ≤ R + ε := by
      intro i c hc
      obtain ⟨z, hz, hnear⟩ := B.dominates i c hc
      exact ⟨z, hz, by rwa [hdist]⟩
    have hFmesh : ∀ a b, F.Adj a b → dist a b ≤ ε := by
      intro a b hab
      rw [hdist]
      exact (distance_edge G w hw (hFG hab)).trans (hmesh a b (hFH hab))
    have hb := connected_multidomination_diameter G F hFG T bag k hT hedge hocc hwidth
      (add_nonneg hR.le hε.le) hε hFmesh hballs C hC B.sets B.connected B.separated hCdis hdom
      u (.rfl) v huv
    convert hb using 1 ; ring

end BoundedTreewidthL1.Annulus

namespace BoundedTreewidthL1.Annulus
variable {V : Type*}
lemma floor_ne_boundary {x y : ℝ} (hxy : x ≤ y) (hne : ⌊x⌋ ≠ ⌊y⌋) :
    ∃ n : ℤ, x < n ∧ (n : ℝ) ≤ y := by
  refine ⟨⌊x⌋ + 1, ?_, ?_⟩
  · simp
  · have hle : ⌊x⌋ < ⌊y⌋ := lt_of_le_of_ne (Int.floor_mono hxy) hne
    have hn : ⌊x⌋ + 1 ≤ ⌊y⌋ := by omega
    exact (by exact_mod_cast hn : ((⌊x⌋ + 1 : ℤ) : ℝ) ≤ ⌊y⌋).trans (Int.floor_le y)

/-- A random finite grid incurs at most one bad offset at any prescribed
height. No minimum positive edge length enters this count. -/
theorem grid_bad_subsingleton (M : ℕ) (hM : 0 < M) (t β : ℝ)
    (hβ : 0 ≤ β) (hsep : 2 * (M : ℝ) * β < 1) :
    {j : Fin M | ⌊t + (j.val : ℝ) / M - β⌋ ≠ ⌊t + (j.val : ℝ) / M + β⌋}.Subsingleton := by
  intro j hj l hl
  obtain ⟨nj, hjlo, hjhi⟩ := floor_ne_boundary (by linarith) hj
  obtain ⟨nl, hllo, hlhi⟩ := floor_ne_boundary (by linarith) hl
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  let qj : ℤ := (M : ℤ) * nj - j.val
  let ql : ℤ := (M : ℤ) * nl - l.val
  have hjdiv : (j.val : ℝ) / M * M = j.val := div_mul_cancel₀ _ hMr.ne'
  have hldiv : (l.val : ℝ) / M * M = l.val := div_mul_cancel₀ _ hMr.ne'
  have hjlo' := mul_lt_mul_of_pos_right hjlo hMr
  have hjhi' := mul_le_mul_of_nonneg_right hjhi hMr.le
  have hllo' := mul_lt_mul_of_pos_right hllo hMr
  have hlhi' := mul_le_mul_of_nonneg_right hlhi hMr.le
  have hqjl : (qj : ℝ) < (ql : ℝ) + 1 := by
    dsimp [qj, ql]
    push_cast
    nlinarith
  have hqlj : (ql : ℝ) < (qj : ℝ) + 1 := by
    dsimp [qj, ql]
    push_cast
    nlinarith
  have hqjli : qj < ql + 1 := by exact_mod_cast hqjl
  have hqlji : ql < qj + 1 := by exact_mod_cast hqlj
  have hqeq : qj = ql := by omega
  have hqeqr : (qj : ℝ) = ql := by exact_mod_cast hqeq
  have hjlt : (j.val : ℝ) < M := by exact_mod_cast j.isLt
  have hllt : (l.val : ℝ) < M := by exact_mod_cast l.isLt
  have hjge : (0 : ℝ) ≤ j.val := by positivity
  have hlge : (0 : ℝ) ≤ l.val := by positivity
  have hneq : nj = nl := by
    by_contra hn
    rcases lt_or_gt_of_ne hn with hnlt | hngt
    · have hnle : nj + 1 ≤ nl := by omega
      have hnler : (nj : ℝ) + 1 ≤ nl := by exact_mod_cast hnle
      dsimp [qj, ql] at hqeqr
      push_cast at hqeqr
      nlinarith
    · have hnle : nl + 1 ≤ nj := by omega
      have hnler : (nl : ℝ) + 1 ≤ nj := by exact_mod_cast hnle
      dsimp [qj, ql] at hqeqr
      push_cast at hqeqr
      nlinarith
  have hval : j.val = l.val := by
    dsimp [qj, ql] at hqeq
    rw [hneq] at hqeq
    omega
  exact Fin.ext hval

lemma floor_eq_of_window {t s β : ℝ} (hlo : t - β ≤ s) (hhi : s ≤ t + β)
    (hgood : ⌊t - β⌋ = ⌊t + β⌋) : ⌊s⌋ = ⌊t⌋ := by
  have hβ : 0 ≤ β := by linarith
  have h1 := Int.floor_mono hlo
  have h2 := Int.floor_mono hhi
  have h3 := Int.floor_mono (by linarith : t - β ≤ t)
  have h4 := Int.floor_mono (by linarith : t ≤ t + β)
  omega

lemma walkLength_edge_le {H : SimpleGraph V} (w : Sym2 V → ℝ) (hw : ∀ e, 0 ≤ w e)
    {u v : V} (p : H.Walk u v) {e : Sym2 V} (he : e ∈ p.edges) :
    w e ≤ walkLength H (weights H w) p := by
  induction p with
  | nil => simp at he
  | @cons u v z h p ih =>
    simp only [SimpleGraph.Walk.edges_cons, List.mem_cons] at he
    rcases he with rfl | he
    · have hn := walkLength_nonneg H (weights H w) (fun e => hw e.val) p
      change w s(u,v) ≤ w s(u,v) + _
      linarith
    · have hle := ih he
      have hn := hw s(u,v)
      change w e ≤ w s(u,v) + _
      linarith

noncomputable def smallEdges (G : SimpleGraph V) (w : Sym2 V → ℝ) (ε : ℝ) : SimpleGraph V where
  Adj u v := G.Adj u v ∧ w s(u,v) ≤ ε
  symm := ⟨fun u v h => ⟨h.1.symm, by simpa only [Sym2.eq_swap] using h.2⟩⟩
  loopless := ⟨fun _ h => G.irrefl h.1⟩

lemma smallEdges_le (G : SimpleGraph V) (w : Sym2 V → ℝ) (ε : ℝ) : smallEdges G w ε ≤ G :=
  fun _ _ h => h.1

lemma smallEdges_mesh (G : SimpleGraph V) (w : Sym2 V → ℝ) (ε : ℝ) :
    ∀ u v, (smallEdges G w ε).Adj u v → w s(u,v) ≤ ε := fun _ _ h => h.2

lemma smallEdges_mem_iff (G : SimpleGraph V) (w : Sym2 V → ℝ) (ε : ℝ) (e : Sym2 V) :
    e ∈ (smallEdges G w ε).edgeSet ↔ e ∈ G.edgeSet ∧ w e ≤ ε := by
  induction e using Sym2.inductionOn with
  | _ u v => rfl

/-- The ball is preserved with its actual original shortest paths, not only
with unquantified reachability. This is the induction invariant for padding. -/
def PreservesBall (G H : SimpleGraph V) (w : Sym2 V → ℝ) (ε : ℝ) (x : V) : Prop :=
  ∀ y, distance G w x y ≤ ε →
    ∃ p : H.Walk x y, walkLength H (weights H w) p = distance G w x y

lemma smallEdges_preserves [Fintype V] (G : SimpleGraph V) (w : Sym2 V → ℝ)
    (hw : ∀ e, 0 ≤ w e) (hG : G.Connected) (ε : ℝ) (x : V) :
    PreservesBall G (smallEdges G w ε) w ε x := by
  intro y hy
  obtain ⟨p, _, hp⟩ := shortestPathDistance_attained_of_reachable G (weights G w) (hG x y)
  have hedges : ∀ e ∈ p.edges, e ∈ (smallEdges G w ε).edgeSet := by
    intro e he
    rw [smallEdges_mem_iff]
    refine ⟨p.edges_subset_edgeSet he, ?_⟩
    exact (walkLength_edge_le w hw p he).trans (hp ▸ hy)
  exact ⟨p.transfer _ hedges, (walkLength_transfer w p hedges).trans hp⟩

lemma walk_height_window [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) (w : Sym2 V → ℝ) (hw : ∀ e, 0 ≤ w e)
    {x y z : V} (p : H.Walk x y) (hz : z ∈ p.support) {ε : ℝ}
    (hp : walkLength H (weights H w) p ≤ ε) :
    height H w x - ε ≤ height H w z ∧ height H w z ≤ height H w x + ε := by
  let q := p.takeUntil z hz
  have hq : walkLength H (weights H w) q ≤ ε :=
    (walkLength_takeUntil_le H (weights H w) (fun e => hw e.val) p hz).trans hp
  have hd : distance H w x z ≤ ε :=
    (shortestPathDistance_le_walkLength H (weights H w) (fun e => hw e.val) q).trans hq
  have hds : distance H w z x ≤ ε := by
    have heq := walkLength_reverse H (weights H w) q
    exact (shortestPathDistance_le_walkLength H (weights H w) (fun e => hw e.val) q.reverse).trans
      (heq ▸ hq)
  have h1 := height_le_add_distance H w hw q.reachable
  have h2 := height_le_add_distance H w hw q.reachable.symm
  constructor <;> linarith

lemma band_eq_of_height_window (H : SimpleGraph V) (w : Sym2 V → ℝ)
    {R ε a : ℝ} (hR : 0 < R) (hε : 0 ≤ ε) {x z : V}
    (hlo : height H w x - ε ≤ height H w z)
    (hhi : height H w z ≤ height H w x + ε)
    (hgood : ⌊(height H w x + a - ε) / R⌋ = ⌊(height H w x + a + ε) / R⌋) :
    band H w R a z = band H w R a x := by
  have hzlo := Int.floor_mono (div_le_div_of_nonneg_right (by linarith :
      height H w x + a - ε ≤ height H w z + a) hR.le)
  have hzhi := Int.floor_mono (div_le_div_of_nonneg_right (by linarith :
      height H w z + a ≤ height H w x + a + ε) hR.le)
  have hxlo := Int.floor_mono (div_le_div_of_nonneg_right (by linarith :
      height H w x + a - ε ≤ height H w x + a) hR.le)
  have hxhi := Int.floor_mono (div_le_div_of_nonneg_right (by linarith :
      height H w x + a ≤ height H w x + a + ε) hR.le)
  unfold band
  omega

lemma preservesBall_cut [Fintype V] [DecidableEq V]
    (G H : SimpleGraph V) (w : Sym2 V → ℝ) (hw : ∀ e, 0 ≤ w e)
    {R ε a : ℝ} (hR : 0 < R) (hε : 0 ≤ ε) (x : V)
    (hpres : PreservesBall G H w ε x)
    (hgood : ⌊(height H w x + a - ε) / R⌋ = ⌊(height H w x + a + ε) / R⌋) :
    PreservesBall G (cut H w R a) w ε x := by
  intro y hy
  obtain ⟨p, hp⟩ := hpres y hy
  have hlen : walkLength H (weights H w) p ≤ ε := hp ▸ hy
  have hband : ∀ z ∈ p.support, band H w R a z = band H w R a x := by
    intro z hz
    obtain ⟨hlo, hhi⟩ := walk_height_window H w hw p hz hlen
    exact band_eq_of_height_window H w hR hε hlo hhi hgood
  have hedges : ∀ e ∈ p.edges, e ∈ (cut H w R a).edgeSet := by
    intro e
    induction e using Sym2.inductionOn with
    | _ u v =>
      intro he
      exact ⟨p.edges_subset_edgeSet he,
        (hband u (p.fst_mem_support_of_mem_edges he)).trans
          (hband v (p.snd_mem_support_of_mem_edges he)).symm⟩
  exact ⟨p.transfer _ hedges, (walkLength_transfer w p hedges).trans hp⟩

noncomputable def gridOffset (M : ℕ) (R : ℝ) (a : Fin M) : ℝ := R * ((a.val : ℝ) / M)

lemma gridOffset_nonneg {M : ℕ} {R : ℝ} (hR : 0 ≤ R) (a : Fin M) :
    0 ≤ gridOffset M R a := by unfold gridOffset; positivity

lemma gridOffset_lt {M : ℕ} {R : ℝ} (hR : 0 < R) (a : Fin M) :
    gridOffset M R a < R := by
  have hM : (0 : ℝ) < M := by exact_mod_cast (Nat.zero_lt_of_lt a.isLt)
  have ha : (a.val : ℝ) < M := by exact_mod_cast a.isLt
  have haf : (a.val : ℝ) / M < 1 := by rwa [div_lt_one hM]
  exact (mul_lt_mul_of_pos_left haf hR).trans_eq (mul_one R)

lemma grid_window_eq {M : ℕ} {R ε t : ℝ} (hR : 0 < R) (a : Fin M) :
    (⌊(t + gridOffset M R a - ε) / R⌋ = ⌊(t + gridOffset M R a + ε) / R⌋) ↔
    (⌊t / R + (a.val : ℝ) / M - ε / R⌋ = ⌊t / R + (a.val : ℝ) / M + ε / R⌋) := by
  have hcancel : gridOffset M R a / R = (a.val : ℝ) / M := by
    dsimp [gridOffset]
    exact mul_div_cancel_left₀ _ hR.ne'
  simp only [sub_div, add_div, hcancel]

end BoundedTreewidthL1.Annulus

/-! Finite adaptive random iteration. No independence assumptions on an
intermediate state: every fresh coordinate is independently enumerated. -/
namespace FiniteRandomIteration

variable {S : Type*} {A : Type*}

def run (step : S → A → S) : (n : ℕ) → S → (Fin n → A) → S
  | 0, s, _ => s
  | n + 1, s, σ => run step n (step s (σ 0)) (Fin.tail σ)

noncomputable def count [Fintype A] (step : S → A → S) (P : S → Prop)
    (n : ℕ) (s : S) : ℝ := by
  classical
  exact ∑ σ : Fin n → A, if P (run step n s σ) then 1 else 0

lemma count_nonneg [Fintype A] (step : S → A → S) (P : S → Prop)
    (n : ℕ) (s : S) : 0 ≤ count step P n s := by
  classical
  exact Finset.sum_nonneg fun σ _ => by split <;> norm_num

lemma count_succ [Fintype A] (step : S → A → S) (P : S → Prop)
    (n : ℕ) (s : S) :
    count step P (n+1) s = ∑ a : A, count step P n (step s a) := by
  classical
  unfold count
  rw [← (Fin.consEquiv (fun _ : Fin (n+1) => A)).sum_comp]
  rw [Fintype.sum_prod_type]
  congr 1

lemma count_lower [Fintype A] [Nonempty A]
    (step : S → A → S) (P : S → Prop)
    (hbad : ∀ s, P s → {a : A | ¬ P (step s a)}.Subsingleton)
    (n : ℕ) (s : S) (hs : P s) :
    ((Fintype.card A : ℝ) - 1)^n ≤ count step P n s := by
  classical
  have hc : (0 : ℝ) ≤ Fintype.card A - 1 := by
    have h : (1 : ℝ) ≤ Fintype.card A := by exact_mod_cast Fintype.card_pos (α := A)
    linarith
  induction n generalizing s with
  | zero => simp [count, run, hs]
  | succ n ih =>
    rw [count_succ]
    have hgood : (Fintype.card A : ℝ) - 1 ≤
        ∑ a : A, if P (step s a) then (1 : ℝ) else 0 := by
      rw [Finset.sum_boole]
      have hb : (Finset.univ.filter fun a : A => ¬ P (step s a)).card ≤ 1 := by
        rw [Finset.card_le_one_iff]
        intro a b ha hb
        exact hbad s hs (Finset.mem_filter.mp ha).2 (Finset.mem_filter.mp hb).2
      have heq := Finset.card_filter_add_card_filter_not (s := Finset.univ) (p := fun a : A => P (step s a))
      have hcard : Fintype.card A ≤ (Finset.univ.filter fun a => P (step s a)).card + 1 := by
        simp only [Finset.card_univ] at heq
        omega
      have hcR : (Fintype.card A : ℝ) ≤ (Finset.univ.filter fun a => P (step s a)).card + 1 := by exact_mod_cast hcard
      linarith
    calc
      ((Fintype.card A : ℝ) - 1)^(n+1) =
          ((Fintype.card A : ℝ) - 1) * ((Fintype.card A : ℝ) - 1)^n := by rw [pow_succ'];
      _ ≤ (∑ a : A, if P (step s a) then (1 : ℝ) else 0) *
          ((Fintype.card A : ℝ) - 1)^n := mul_le_mul_of_nonneg_right hgood (pow_nonneg hc n)
      _ = ∑ a : A, if P (step s a) then ((Fintype.card A : ℝ) - 1)^n else 0 := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro a _
        split <;> simp
      _ ≤ ∑ a : A, count step P n (step s a) := by
        apply Finset.sum_le_sum
        intro a _
        split_ifs with ha
        · exact ih (step s a) ha
        · exact count_nonneg step P n (step s a)

lemma fraction_lower [Fintype A] [Nonempty A]
    (step : S → A → S) (P : S → Prop)
    (hbad : ∀ s, P s → {a : A | ¬ P (step s a)}.Subsingleton)
    (n : ℕ) (s : S) (hs : P s) :
    1 - (n : ℝ) / Fintype.card A ≤
      count step P n s / (Fintype.card A : ℝ)^n := by
  have hM : (0 : ℝ) < Fintype.card A := by exact_mod_cast Fintype.card_pos (α := A)
  have hM1 : (1 : ℝ) ≤ Fintype.card A := by exact_mod_cast Fintype.card_pos (α := A)
  have ha : (-2 : ℝ) ≤ -(1 / (Fintype.card A : ℝ)) := by
    have hh : 1 / (Fintype.card A : ℝ) ≤ 1 := (div_le_one hM).mpr hM1
    linarith
  have hbern := one_add_mul_le_pow ha n
  calc
    1 - (n : ℝ) / Fintype.card A ≤ (1 - 1 / (Fintype.card A : ℝ))^n := by
      simpa only [sub_eq_add_neg, mul_neg, mul_one_div] using hbern
    _ = (((Fintype.card A : ℝ) - 1)^n) / (Fintype.card A : ℝ)^n := by
      rw [← div_pow]
      congr 1
      field_simp
    _ ≤ count step P n s / (Fintype.card A : ℝ)^n :=
      div_le_div_of_nonneg_right (count_lower step P hbad n s hs) (pow_nonneg hM.le n)

end FiniteRandomIteration

namespace BoundedTreewidthL1.Annulus
variable {V A : Type*}

lemma run_eq_iteration (w : Sym2 V → ℝ) (R : ℝ) (offset : A → ℝ)
    (n : ℕ) (H : SimpleGraph V) (σ : Fin n → A) :
    run w R offset n H σ =
    FiniteRandomIteration.run (fun H a => cut H w R (offset a)) n H σ := by
  induction n generalizing H with
  | zero => rfl
  | succ n ih => exact ih _ _

lemma preserves_bad_subsingleton [Fintype V] [DecidableEq V]
    (G H : SimpleGraph V) (w : Sym2 V → ℝ) (hw : ∀ e, 0 ≤ w e)
    (M : ℕ) (hM : 0 < M) {R ε : ℝ} (hR : 0 < R) (hε : 0 ≤ ε)
    (hsep : 2 * (M : ℝ) * (ε / R) < 1) (x : V)
    (hpres : PreservesBall G H w ε x) :
    {a : Fin M | ¬ PreservesBall G (cut H w R (gridOffset M R a)) w ε x}.Subsingleton := by
  have hgrid := grid_bad_subsingleton M hM (height H w x / R) (ε / R)
    (div_nonneg hε hR.le) hsep
  have hbadfloor : ∀ a : Fin M, ¬ PreservesBall G (cut H w R (gridOffset M R a)) w ε x →
      ⌊height H w x / R + (a.val : ℝ) / M - ε / R⌋ ≠
      ⌊height H w x / R + (a.val : ℝ) / M + ε / R⌋ := by
    intro a ha hg
    exact ha (preservesBall_cut G H w hw hR hε x hpres ((grid_window_eq hR a).mpr hg))
  intro a ha b hb
  exact hgrid (hbadfloor a ha) (hbadfloor b hb)

attribute [local instance] Classical.propDecidable
lemma preserves_fraction [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (w : Sym2 V → ℝ) (hw : ∀ e, 0 ≤ w e)
    (hG : G.Connected) (M : ℕ) (hM : 0 < M) {R ε : ℝ}
    (hR : 0 < R) (hε : 0 ≤ ε) (hsep : 2 * (M : ℝ) * (ε / R) < 1)
    (n : ℕ) (x : V) :
    1 - (n : ℝ) / M ≤
      (∑ σ : Fin n → Fin M,
        if PreservesBall G (run w R (gridOffset M R) n (smallEdges G w ε) σ) w ε x
        then (1 : ℝ) else 0) / (M : ℝ)^n := by
  classical
  let : Nonempty (Fin M) := ⟨⟨0, hM⟩⟩
  have hh := FiniteRandomIteration.fraction_lower (fun H a => cut H w R (gridOffset M R a))
    (fun H => PreservesBall G H w ε x)
    (fun H hp => preserves_bad_subsingleton G H w hw M hM hR hε hsep x hp)
    n (smallEdges G w ε) (smallEdges_preserves G w hw hG ε x)
  simpa only [FiniteRandomIteration.count, ← run_eq_iteration, Fintype.card_fin] using hh

end BoundedTreewidthL1.Annulus

namespace FiniteLawPush
attribute [local instance] Classical.propDecidable
variable {Ω B : Type*} [Fintype Ω] [Fintype B]

noncomputable def law (f : Ω → B) (b : B) : ℝ := by
  classical
  exact ∑ ω, if f ω = b then 1 / Fintype.card Ω else 0

lemma nonneg
    {Ω : Type treewidthLevel1} {B : Type treewidthLevel2} [Fintype Ω] [Fintype B]
    (f : Ω → B) (b : B) : 0 ≤ law f b := by
  classical
  exact Finset.sum_nonneg fun ω _ => by split <;> positivity

lemma total [Nonempty Ω] (f : Ω → B) : (∑ b, law f b) = 1 := by
  classical
  unfold law
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul]
  exact mul_one_div_cancel (by exact_mod_cast Fintype.card_ne_zero (α := Ω))

lemma supported
    {Ω : Type treewidthLevel1} {B : Type treewidthLevel2} [Fintype Ω] [Fintype B]
    (f : Ω → B) (b : B) (hb : 0 < law f b) : ∃ ω, f ω = b := by
  classical
  by_contra! hh
  have hz : law f b = 0 := by simp [law, hh]
  linarith

lemma event (f : Ω → B) (Q : B → Prop) :
    (∑ b, if Q b then law f b else 0) =
    (∑ ω, if Q (f ω) then (1 : ℝ) else 0) / Fintype.card Ω := by
  classical
  unfold law
  calc
    (∑ b, if Q b then (∑ ω, if f ω = b then 1 / (Fintype.card Ω : ℝ) else 0) else 0) =
        ∑ b, ∑ ω, if f ω = b then (if Q b then 1 / (Fintype.card Ω : ℝ) else 0) else 0 := by
      apply Finset.sum_congr rfl
      intro b _
      by_cases hb : Q b <;> simp [hb]
    _ = ∑ ω, ∑ b, if f ω = b then (if Q b then 1 / (Fintype.card Ω : ℝ) else 0) else 0 := Finset.sum_comm
    _ = (∑ ω, if Q (f ω) then (1 : ℝ) else 0) / Fintype.card Ω := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro ω _
      simp only [Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
      split <;> simp_all
end FiniteLawPush

end OAI
