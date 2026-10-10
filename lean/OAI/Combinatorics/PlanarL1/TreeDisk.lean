import OAI.Combinatorics.PlanarL1.HeightTree
import OAI.Combinatorics.PlanarL1.Polygonal

namespace OAI

section



namespace PlanarL1.Topology
open Set Real

/-- Radial inversion fixes the unit circle and puts the exterior into the disk.
This avoids any one-point-compactification assumption in the complementary
region of a prospective tree neighborhood. -/
noncomputable def exteriorToDisk (z : ℂ) : ℂ := star (z⁻¹)

lemma exteriorToDisk_injective : Function.Injective exteriorToDisk := by
  intro z w h
  exact inv_injective (star_injective h)

lemma exteriorToDisk_circle (a : ℝ) : exteriorToDisk (Circle.exp a : ℂ) = Circle.exp a := by
  change star ((Circle.exp a : ℂ)⁻¹) = _
  rw [← Circle.coe_inv, Circle.coe_inv_eq_conj]
  exact star_star _

lemma exteriorToDisk_norm {z : ℂ} (hz : 1 ≤ ‖z‖) : ‖exteriorToDisk z‖ ≤ 1 := by
  simp only [exteriorToDisk, norm_star, norm_inv]
  exact inv_le_one_of_one_le₀ hz

lemma exteriorToDisk_continuous_path {a b : ℂ} (p : Path a b)
    (hp : ∀ t, 1 ≤ ‖p t‖) : Continuous (fun t => exteriorToDisk (p t)) := by
  apply Continuous.star
  exact p.continuous.inv₀ (fun t => by
    intro h
    have := hp t
    norm_num [h] at this)

/-- The corresponding crossing theorem in the exterior of the unit disk.
Inversion fixes every endpoint and is injective; no simplicity assumption
on the two paths is needed. -/
lemma exterior_cyclic_arcs_meet (a₀ a₁ a₂ a₃ : ℝ)
    (h₀₁ : a₀ < a₁) (h₁₂ : a₁ < a₂) (h₂₃ : a₂ < a₃)
    (hspan : a₃ < a₀ + 2 * π)
    (f : Path (Circle.exp a₀ : ℂ) (Circle.exp a₂ : ℂ))
    (g : Path (Circle.exp a₁ : ℂ) (Circle.exp a₃ : ℂ))
    (hf : ∀ s, 1 ≤ ‖f s‖) (hg : ∀ s, 1 ≤ ‖g s‖) :
    ∃ s t, f s = g t := by
  let F : Path (Circle.exp a₀ : ℂ) (Circle.exp a₂ : ℂ) :=
    ⟨⟨fun s => exteriorToDisk (f s), exteriorToDisk_continuous_path f hf⟩,
      by change exteriorToDisk (f 0) = _; rw [f.source, exteriorToDisk_circle], by change exteriorToDisk (f 1) = _; rw [f.target, exteriorToDisk_circle]⟩
  let G : Path (Circle.exp a₁ : ℂ) (Circle.exp a₃ : ℂ) :=
    ⟨⟨fun s => exteriorToDisk (g s), exteriorToDisk_continuous_path g hg⟩,
      by change exteriorToDisk (g 0) = _; rw [g.source, exteriorToDisk_circle], by change exteriorToDisk (g 1) = _; rw [g.target, exteriorToDisk_circle]⟩
  obtain ⟨s,t,h⟩ := disk_cyclic_arcs_meet a₀ a₁ a₂ a₃ h₀₁ h₁₂ h₂₃ hspan F G
    (fun s => exteriorToDisk_norm (hf s)) (fun t => exteriorToDisk_norm (hg t))
  exact ⟨s,t,exteriorToDisk_injective h⟩


/-- Mutually disjoint exterior paths imply the literal noncrossing relation
on the finite cyclic list of their boundary ports. -/
lemma noncrossing_of_exterior_arcs {n : ℕ} (G : SimpleGraph (Fin n))
    (angle : Fin n → ℝ) (horder : StrictMono angle)
    (hspan : ∀ i j, angle j - angle i < 2 * π)
    (arc : ∀ i j, G.Adj i j → Path (Circle.exp (angle i) : ℂ)
      (Circle.exp (angle j) : ℂ))
    (hout : ∀ i j h t, 1 ≤ ‖arc i j h t‖)
    (hdisjoint : ∀ i j h k l h', i ≠ k → i ≠ l → j ≠ k → j ≠ l →
      Disjoint (range (arc i j h)) (range (arc k l h'))) :
    PlanarL1.ColumnOrder.Noncrossing G := by
  intro a b c d hab hbc hcd h
  obtain ⟨s,t,hst⟩ := exterior_cyclic_arcs_meet
    (angle a) (angle b) (angle c) (angle d)
    (horder hab) (horder hbc) (horder hcd) (by linarith [hspan a d])
    (arc a c h.1) (arc b d h.2) (hout a c h.1) (hout b d h.2)
  have hd := hdisjoint a c h.1 b d h.2 (ne_of_lt hab)
    (ne_of_lt (hab.trans (hbc.trans hcd))) (ne_of_gt hbc) (ne_of_lt hcd)
  exact Set.disjoint_left.mp hd (Set.mem_range_self s) (hst ▸ Set.mem_range_self t)

lemma circle_exp_arg {z : ℂ} (hz : ‖z‖ = 1) : (Circle.exp (Complex.arg z) : ℂ) = z := by
  simpa only [Circle.coe_exp, hz, Complex.ofReal_one, one_mul]
    using Complex.norm_mul_exp_arg_mul_I z

/-- A finite collection of distinct boundary ports supplies a cyclic list;
angles in a single half-open turn handle the wrap-around without choosing a
port as a special zero-angle endpoint. -/
lemma finite_port_order {V : Type} [Fintype V] (port : V → ℂ)
    (hnorm : ∀ v, ‖port v‖ = 1) (hinj : Function.Injective port) :
    ∃ e : Fin (Fintype.card V) ≃ V,
      StrictMono (fun i => Complex.arg (port (e i))) ∧
      (∀ i j, Complex.arg (port (e j)) - Complex.arg (port (e i)) < 2 * π) := by
  classical
  have ha : Function.Injective (fun v => Complex.arg (port v)) := by
    intro a b hab
    apply hinj
    exact (circle_exp_arg (hnorm a)).symm.trans
      ((congrArg (fun t => (Circle.exp t : ℂ)) hab).trans (circle_exp_arg (hnorm b)))
  let : LinearOrder V := LinearOrder.lift' (fun v => Complex.arg (port v)) ha
  let e := monoEquivOfFin V rfl
  refine ⟨e.toEquiv, ?_, ?_⟩
  · exact e.strictMono
  · intro i j
    change Complex.arg (port (e j)) - Complex.arg (port (e i)) < 2 * π
    linarith [Complex.arg_le_pi (port (e j)), Complex.neg_pi_lt_arg (port (e i))]

/-- Any bounded convex neighborhood has an ambient disk coordinate in which
points outside its interior remain outside the open disk. -/
lemma convex_disk_coordinates {S : Set ℂ} (hS : Convex ℝ S)
    (hne : (interior S).Nonempty) (hb : Bornology.IsBounded S) :
    ∃ h : ℂ ≃ₜ ℂ,
      (∀ z, z ∈ frontier S → ‖h z‖ = 1) ∧
      (∀ z, z ∉ interior S → 1 ≤ ‖h z‖) := by
  obtain ⟨h,hi,_,hf⟩ := exists_homeomorph_image_interior_closure_frontier_eq_unitBall hS hne hb
  refine ⟨h, ?_, ?_⟩
  · intro z hz
    have hm : h z ∈ Metric.sphere (0:ℂ) 1 := hf ▸ mem_image_of_mem h hz
    simpa [Metric.mem_sphere, dist_zero_right] using hm
  · intro z hz
    by_contra! hn
    have hm : h z ∈ Metric.ball (0:ℂ) 1 := by simpa [Metric.mem_ball, dist_zero_right]
    rw [← hi] at hm
    obtain ⟨w,hw,he⟩ := hm
    exact hz (h.injective he ▸ hw)


/-- Complementary arcs outside an actual convex tree-merging neighborhood
produce a noncrossing cyclic order of its distinct leaf ports. All hypotheses
here concern the geometric sets and paths, not a promised column model. -/
lemma convex_ports_noncrossing {V : Type} [Fintype V] (G : SimpleGraph V)
    {S : Set ℂ} (hS : Convex ℝ S) (hne : (interior S).Nonempty)
    (hb : Bornology.IsBounded S) (port : V → ℂ)
    (hport : ∀ v, port v ∈ frontier S) (hinj : Function.Injective port)
    (arc : ∀ i j, G.Adj i j → Path (port i) (port j))
    (hout : ∀ i j h t, arc i j h t ∉ interior S)
    (hdisjoint : ∀ i j h k l h', i ≠ k → i ≠ l → j ≠ k → j ≠ l →
      Disjoint (range (arc i j h)) (range (arc k l h'))) :
    ∃ e : Fin (Fintype.card V) ≃ V,
      PlanarL1.ColumnOrder.Noncrossing (SimpleGraph.comap e G) := by
  obtain ⟨h,hf,ho⟩ := convex_disk_coordinates hS hne hb
  have hn (v : V) : ‖h (port v)‖ = 1 := hf _ (hport v)
  obtain ⟨e,he,hspan⟩ := finite_port_order (fun v => h (port v)) hn (h.injective.comp hinj)
  let angle (i : Fin (Fintype.card V)) := Complex.arg (h (port (e i)))
  let A : ∀ i j, (SimpleGraph.comap e G).Adj i j →
      Path (Circle.exp (angle i) : ℂ) (Circle.exp (angle j) : ℂ) :=
    fun i j hij => ((arc (e i) (e j) hij).map h.continuous).cast
      (circle_exp_arg (hn (e i))) (circle_exp_arg (hn (e j)))
  refine ⟨e, noncrossing_of_exterior_arcs _ angle he hspan A ?_ ?_⟩
  · intro i j hij t
    exact ho _ (hout (e i) (e j) hij t)
  · intro i j hij k l hkl hik hil hjk hjl
    rw [Set.disjoint_left]
    rintro z ⟨s,hs⟩ ⟨t,ht⟩
    have hh : h (arc (e i) (e j) hij s) = h (arc (e k) (e l) hkl t) := hs.trans ht.symm
    have hd := hdisjoint (e i) (e j) hij (e k) (e l) hkl
      (e.injective.ne hik) (e.injective.ne hil) (e.injective.ne hjk) (e.injective.ne hjl)
    exact Set.disjoint_left.mp hd (Set.mem_range_self s)
      ((h.injective hh) ▸ Set.mem_range_self t)

end PlanarL1.Topology




namespace PlanarL1.Columns
attribute [local instance] Classical.propDecidable

/-- An interval of selected consecutive indices is connected without using the
wrap-around edge. -/
lemma interval_reachable {n : ℕ} (G : SimpleGraph (Fin n)) (S : Set (Fin n))
    (he : ∀ i j, i.val+1=j.val → i∈S → j∈S → G.Adj i j)
    {i j : Fin n} (hij : i≤j) (hS : ∀ k, i≤k → k≤j → k∈S) :
    G.Reachable i j := by
  have go (m : ℕ) : ∀ j : Fin n, j.val-i.val=m → i≤j →
      (∀ k, i≤k → k≤j → k∈S) → G.Reachable i j := by
    induction m with
    | zero =>
      intro j hm hij _
      have : i=j := Fin.ext (by omega)
      subst j
      exact .rfl
    | succ m ih =>
      intro j hm hij hS
      have hj : 0<j.val := by omega
      let k : Fin n := ⟨j.val-1,by omega⟩
      have hik : i≤k := by change i.val≤j.val-1; omega
      have hkj : k≤j := by change j.val-1≤j.val; omega
      have hmk : k.val-i.val=m := by dsimp [k]; omega
      exact (ih k hmk hik (fun a ha hb => hS a ha (hb.trans hkj))).trans
        ((he k j (by dsimp [k]; omega) (hS k hik hkj) (hS j hij le_rfl)).reachable)
  exact go _ j rfl hij hS

/-- The elementary circular-interval criterion: if a set and its complement
have no alternating four indices, consecutive selected indices connect it. -/
lemma consecutive_connected {n : ℕ} (G : SimpleGraph (Fin n)) (S : Set (Fin n))
    (he : ∀ i j, i≠j → Consecutive i j → i∈S → j∈S → G.Adj i j)
    (halt : ∀ a b c d : Fin n, a<b → b<c → c<d →
      ¬((a∈S ∧ b∉S ∧ c∈S ∧ d∉S) ∨ (a∉S ∧ b∈S ∧ c∉S ∧ d∈S)))
    {i j : Fin n} (hi : i∈S) (hj : j∈S) : G.Reachable i j := by
  have edge : ∀ a b : Fin n, a.val+1=b.val → a∈S → b∈S → G.Adj a b := by
    intro a b hab ha hb
    exact he a b (fun h => by subst b; omega) (Or.inl hab) ha hb
  suffices h : ∀ a b : Fin n, a≤b → a∈S → b∈S → G.Reachable a b by
    rcases le_total i j with hij | hji
    · exact h i j hij hi hj
    · exact (h j i hji hj hi).symm
  intro a b hab ha hb
  by_cases hwhole : ∀ k, a≤k → k≤b → k∈S
  · exact interval_reachable G S edge hab hwhole
  push Not at hwhole
  obtain ⟨k,hak,hkb,hk⟩ := hwhole
  have hak' : a<k := lt_of_le_of_ne hak (fun h => hk (h ▸ ha))
  have hkb' : k<b := lt_of_le_of_ne hkb (fun h => hk (h.symm ▸ hb))
  have hlow (t : Fin n) (ht : t≤a) : t∈S := by
    by_contra hn
    have hta : t<a := lt_of_le_of_ne ht (fun h => hn (h.symm ▸ ha))
    exact halt t a k b hta hak' hkb' (Or.inr ⟨hn,ha,hk,hb⟩)
  have hhigh (t : Fin n) (ht : b≤t) : t∈S := by
    by_contra hn
    have hbt : b<t := lt_of_le_of_ne ht (fun h => hn (h ▸ hb))
    exact halt a k b t hak' hkb' hbt (Or.inl ⟨ha,hk,hb,hn⟩)
  let first : Fin n := ⟨0,by have := a.isLt; omega⟩
  let last : Fin n := ⟨n-1,by have := a.isLt; omega⟩
  have hfa : first≤a := by change 0≤a.val; omega
  have hbl : b≤last := by change b.val≤n-1; omega
  have hleft := interval_reachable G S edge hfa (fun t _ ht => hlow t ht)
  have hright := interval_reachable G S edge hbl (fun t ht _ => hhigh t ht)
  have hwrap : G.Reachable first last := by
    by_cases hfl : first=last
    · rw [hfl]
    · apply SimpleGraph.Adj.reachable
      apply he first last hfl
      · exact Or.inr (Or.inr (Or.inl ⟨rfl,by dsimp [last]; omega⟩))
      · exact hlow first hfa
      · exact hhigh last hbl
  exact (hleft.symm.trans hwrap).trans hright.symm

end PlanarL1.Columns

namespace PlanarL1.Topology.Drawing
open Set
variable {V : Type} {G : SimpleGraph V} (D : Drawing G)

def carrier (S : Set V) : Set ℂ :=
  {z | (∃ v∈S, z=D.point v) ∨
    (∃ u∈S, ∃ v∈S, ∃ h : G.Adj u v, z∈range (D.edge u v h))}

lemma point_mem_carrier {S : Set V} {v : V} (hv : v∈S) :
    D.point v ∈ D.carrier S := Or.inl ⟨v,hv,rfl⟩

lemma edge_mem_carrier {S : Set V} {u v : V} (h : G.Adj u v)
    (hu : u∈S) (hv : v∈S) (t : unitInterval) : D.edge u v h t∈D.carrier S :=
  Or.inr ⟨u,hu,v,hv,h,mem_range_self t⟩

lemma carrier_disjoint {S T : Set V} (hst : Disjoint S T) :
    Disjoint (D.carrier S) (D.carrier T) := by
  have sep : ∀ u∈S, ∀ v∈T, u≠v := by
    intro u hu v hv he
    exact disjoint_left.mp hst hu (he ▸ hv)
  have point_edge : ∀ u∈S, ∀ v∈T, ∀ w∈T, ∀ h : G.Adj v w,
      ∀ t, D.point u≠D.edge v w h t := by
    intro u hu v hv w hw h t he
    rcases (D.point_on_edge_iff v w h u t).mp he.symm with ⟨_,he⟩ | ⟨_,he⟩
    · exact sep u hu v hv he
    · exact sep u hu w hw he
  rw [disjoint_left]
  rintro z (⟨u,hu,rfl⟩ | ⟨u,hu,v,hv,h,s,rfl⟩)
    (⟨w,hw,he⟩ | ⟨w,hw,x,hx,k,t,ht⟩)
  · exact sep u hu w hw (D.point_injective he)
  · exact point_edge u hu w hw x hx k t ht.symm
  · rcases (D.point_on_edge_iff u v h w s).mp he with ⟨_,he⟩ | ⟨_,he⟩
    · exact sep u hu w hw he.symm
    · exact sep v hv w hw he.symm
  · by_cases hs0 : s=0
    · subst s
      rw [Path.source] at ht
      exact point_edge u hu w hw x hx k t ht.symm
    by_cases hs1 : s=1
    · subst s
      rw [Path.target] at ht
      exact point_edge v hv w hw x hx k t ht.symm
    by_cases ht0 : t=0
    · subst t
      rw [Path.source] at ht
      rcases (D.point_on_edge_iff u v h w s).mp ht.symm with ⟨he,_⟩ | ⟨he,_⟩
      · exact hs0 he
      · exact hs1 he
    by_cases ht1 : t=1
    · subst t
      rw [Path.target] at ht
      rcases (D.point_on_edge_iff u v h x s).mp ht.symm with ⟨he,_⟩ | ⟨he,_⟩
      · exact hs0 he
      · exact hs1 he
    have interior (r : unitInterval) (h0 : r≠0) (h1 : r≠1) : 0<(r:ℝ) ∧ (r:ℝ)<1 :=
      ⟨lt_of_le_of_ne r.2.1 (fun h => h0 (Subtype.ext h.symm)),
        lt_of_le_of_ne r.2.2 (fun h => h1 (Subtype.ext h))⟩
    rcases D.interior_disjoint u v h w x k s t (interior s hs0 hs1).1
      (interior s hs0 hs1).2 (interior t ht0 ht1).1 (interior t ht0 ht1).2 ht.symm
      with ⟨he,_⟩ | ⟨he,_⟩
    · exact sep u hu w hw he
    · exact sep u hu x hx he

end PlanarL1.Topology.Drawing

namespace PlanarL1.HeightTree
open Set
attribute [local instance] Classical.propDecidable
variable {V : Type} (T : HeightTree V)

def graph : SimpleGraph V where
  Adj u v := T.Step u v ∨ T.Step v u
  symm := ⟨fun _ _ => Or.symm⟩
  loopless := ⟨by
    intro v h
    rcases h with h | h <;> exact (lt_irrefl (T.depth v)) (T.step_depth h)⟩

lemma ancestor_path (D : Topology.Drawing T.graph) {u v : V} (h : T.Ancestor u v)
    {S : Set V} (hS : ∀ w, T.Ancestor u w → T.Ancestor w v → w∈S) :
    ∃ p : Path (D.point u) (D.point v), range p ⊆ D.carrier S := by
  induction h with
  | refl =>
    refine ⟨Path.refl _,?_⟩
    rintro z ⟨t,rfl⟩
    exact D.point_mem_carrier (hS _ .refl .refl)
  | @tail v w huv hvw ih =>
    obtain ⟨p,hp⟩ := ih (fun a ha hb => hS a ha (hb.tail hvw))
    let q := D.edge v w (Or.inl hvw)
    refine ⟨p.trans q,?_⟩
    rw [Path.trans_range]
    apply union_subset hp
    rintro z ⟨t,rfl⟩
    exact D.edge_mem_carrier _ (hS v huv (.single hvw))
      (hS w (huv.tail hvw) .refl) t

lemma descendants_joined (D : Topology.Drawing T.graph) (a : V) {u v : V}
    (hu : T.Ancestor a u) (hv : T.Ancestor a v) :
    ∃ p : Path (D.point u) (D.point v), range p ⊆ D.carrier {w | T.Ancestor a w} := by
  obtain ⟨p,hp⟩ := T.ancestor_path D hu (fun _ h _ => h)
  obtain ⟨q,hq⟩ := T.ancestor_path D hv (fun _ h _ => h)
  exact ⟨p.symm.trans q,by
    rw [Path.trans_range,Path.symm_range]
    intro z hz
    exact hz.elim (fun h => hp h) (fun h => hq h)⟩

lemma nondescendants_joined (D : Topology.Drawing T.graph) (a : V) {u v : V}
    (hu : ¬T.Ancestor a u) (hv : ¬T.Ancestor a v) :
    ∃ p : Path (D.point u) (D.point v), range p ⊆ D.carrier {w | ¬T.Ancestor a w} := by
  obtain ⟨p,hp⟩ := T.ancestor_path D (T.root_ancestor u)
    (S := {w | ¬T.Ancestor a w}) (fun _ _ h ha => hu (ha.trans h))
  obtain ⟨q,hq⟩ := T.ancestor_path D (T.root_ancestor v)
    (S := {w | ¬T.Ancestor a w}) (fun _ _ h ha => hv (ha.trans h))
  exact ⟨p.symm.trans q,by
    rw [Path.trans_range,Path.symm_range]
    intro z hz
    exact hz.elim (fun h => hp h) (fun h => hq h)⟩

end PlanarL1.HeightTree

namespace PlanarL1.HeightTree
open Set Real
attribute [local instance] Classical.propDecidable
variable {V : Type} (T : HeightTree V)

lemma disk_prefix_connected {n : ℕ} (D : Topology.Drawing T.graph)
    (hpoint : ∀ v, ‖D.point v‖≤1)
    (hedge : ∀ u v h t, ‖D.edge u v h t‖≤1)
    (leaf : Fin n → V) (angle : Fin n → ℝ)
    (hend : ∀ i, D.point (leaf i)=(Circle.exp (angle i) : ℂ))
    (horder : StrictMono angle) (hspan : ∀ i j, angle j-angle i<2*π)
    (a : V) {i j : Fin n} (hi : T.Ancestor a (leaf i)) (hj : T.Ancestor a (leaf j)) :
    (T.prefixGraph leaf a).Reachable i j := by
  have hcarrier (S : Set V) : ∀ z∈D.carrier S, ‖z‖≤1 := by
    rintro z (⟨v,_,rfl⟩ | ⟨u,_,v,_,h,t,rfl⟩)
    · exact hpoint v
    · exact hedge u v h t
  apply Columns.consecutive_connected (T.prefixGraph leaf a) {k | T.Ancestor a (leaf k)}
    (fun _ _ hne hc ha hb => ⟨hne,hc,ha,hb⟩) _ hi hj
  intro w x y z hwx hxy hyz hbad
  suffices impossible : ∀ (S U : Set V), Disjoint S U →
      (∃ p : Path (D.point (leaf w)) (D.point (leaf y)), range p⊆D.carrier S) →
      (∃ q : Path (D.point (leaf x)) (D.point (leaf z)), range q⊆D.carrier U) → False by
    rcases hbad with ⟨hw,hx,hy,hz⟩ | ⟨hw,hx,hy,hz⟩
    · exact impossible {v | T.Ancestor a v} {v | ¬T.Ancestor a v}
        (disjoint_compl_right) (T.descendants_joined D a hw hy)
        (T.nondescendants_joined D a hx hz)
    · exact impossible {v | ¬T.Ancestor a v} {v | T.Ancestor a v}
        (disjoint_compl_left) (T.nondescendants_joined D a hw hy)
        (T.descendants_joined D a hx hz)
  intro S U hdis ⟨p,hp⟩ ⟨q,hq⟩
  let p' := p.cast (hend w).symm (hend y).symm
  let q' := q.cast (hend x).symm (hend z).symm
  obtain ⟨s,t,hst⟩ := Topology.disk_cyclic_arcs_meet (angle w) (angle x) (angle y) (angle z)
    (horder hwx) (horder hxy) (horder hyz) (by linarith [hspan w z]) p' q'
    (fun t => hcarrier S _ (hp (mem_range_self t)))
    (fun t => hcarrier U _ (hq (mem_range_self t)))
  exact disjoint_left.mp (D.carrier_disjoint hdis) (hp (mem_range_self s))
    (hst ▸ hq (mem_range_self t))

/-- The exact leaf layout follows from a geometric disk drawing and disjoint
complementary paths. This lemma does not assert the still-required disk surgery
on the supplied planar drawing. -/
lemma layout_of_disk [Fintype V] (D : Topology.Drawing T.graph)
    (hpoint : ∀ v, ‖D.point v‖≤1)
    (hedge : ∀ u v h t, ‖D.edge u v h t‖≤1)
    (hleaf : ∀ v, T.IsLeaf v → ‖D.point v‖=1)
    (P : SimpleGraph {v : V // T.IsLeaf v})
    (hheight : ∀ i j, P.Adj i j → T.height i.val=T.height j.val)
    (hmatch : ∀ i j k, P.Adj i j → P.Adj i k → j=k)
    (arc : ∀ i j, P.Adj i j → Path (D.point i.val) (D.point j.val))
    (hout : ∀ i j h t, 1≤‖arc i j h t‖)
    (hdis : ∀ i j h k l h', i≠k → i≠l → j≠k → j≠l →
      Disjoint (range (arc i j h)) (range (arc k l h'))) :
    ∃ (L : T.Layout (Fintype.card {v : V // T.IsLeaf v})),
      ∀ i j, L.pair.Adj i j ↔ P.Adj ⟨L.leaf i,L.isLeaf i⟩ ⟨L.leaf j,L.isLeaf j⟩ := by
  obtain ⟨e,he,hspan⟩ := Topology.finite_port_order (fun v : {v : V // T.IsLeaf v} => D.point v.val)
    (fun v => hleaf v.val v.property) (D.point_injective.comp Subtype.val_injective)
  let angle (i : Fin (Fintype.card {v : V // T.IsLeaf v})) := Complex.arg (D.point (e i).val)
  have hend i : D.point (e i).val=(Circle.exp (angle i) : ℂ) :=
    (Topology.circle_exp_arg (hleaf _ (e i).property)).symm
  let A : ∀ i j, (SimpleGraph.comap e P).Adj i j →
      Path (Circle.exp (angle i) : ℂ) (Circle.exp (angle j) : ℂ) :=
    fun i j h => (arc (e i) (e j) h).cast (hend i).symm (hend j).symm
  have hnc : ColumnOrder.Noncrossing (SimpleGraph.comap e P) := by
    apply Topology.noncrossing_of_exterior_arcs _ angle he hspan A
    · intro i j h t; exact hout (e i) (e j) h t
    · intro i j h k l h' hik hil hjk hjl
      exact hdis (e i) (e j) h (e k) (e l) h'
        (e.injective.ne hik) (e.injective.ne hil) (e.injective.ne hjk) (e.injective.ne hjl)
  let L : T.Layout (Fintype.card {v : V // T.IsLeaf v}) := {
    leaf := fun i => (e i).val
    isLeaf := fun i => (e i).property
    injective := Subtype.val_injective.comp e.injective
    covers := fun v hv => ⟨e.symm ⟨v,hv⟩,by simp⟩
    prefix_connected := fun a i j hi hj =>
      T.disk_prefix_connected D hpoint hedge _ angle hend he hspan a hi hj
    pair := SimpleGraph.comap e P
    noncrossing := hnc
    paired_height := fun i j h => hheight (e i) (e j) h
    matching := fun i j k hij hik => e.injective (hmatch (e i) (e j) (e k) hij hik) }
  exact ⟨L,fun _ _ => Iff.rfl⟩

end PlanarL1.HeightTree



end

end OAI
