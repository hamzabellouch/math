import OAI.GroupTheory.Hyperbolic.Incidence

namespace OAI

namespace Release075

/-- Internal reduction of an edge walk; no condition is imposed at the closing seam. -/
def ReducedWalk {V : Type*} {G : SimpleGraph V} {a b : V} (p : G.Walk a b) : Prop :=
  ∀ n, n + 2 ≤ p.length → p.getVert n ≠ p.getVert (n + 2)

theorem ReducedWalk.tail {V : Type*} {G : SimpleGraph V} {a b c : V}
    {e : G.Adj a b} {p : G.Walk b c} (h : ReducedWalk (p.cons e)) : ReducedWalk p := by
  intro n hn
  have hh := h (n + 1) (by simpa using Nat.add_le_add_right hn 1)
  simpa only [SimpleGraph.Walk.getVert_cons_succ, Nat.add_right_comm n 1 2] using hh

/-- A locally injective graph homomorphism preserves internal reduction. -/
def LocallyInjective {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (f : G →g H) : Prop :=
  ∀ a b c, G.Adj a b → G.Adj a c → f b = f c → b = c

theorem ReducedWalk.map {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (f : G →g H) (hf : LocallyInjective f) {a b : V} {p : G.Walk a b}
    (hp : ReducedWalk p) : ReducedWalk (p.map f) := by
  intro n hn heq
  simp only [SimpleGraph.Walk.length_map] at hn
  simp only [SimpleGraph.Walk.getVert_map] at heq
  apply hp n hn
  apply hf (p.getVert (n+1)) _ _
    (p.adj_getVert_succ (by omega)).symm (p.adj_getVert_succ (by omega)) heq

/-- A reduced walk which is not a simple path contains a cycle of no greater length.
In particular, a nonempty reduced *closed* walk need not be reduced at its seam. -/
theorem reduced_path_or_cycle {V : Type*} {G : SimpleGraph V} {a b : V}
    (p : G.Walk a b) (hp : ReducedWalk p) :
    p.IsPath ∨ ∃ (c : V) (w : G.Walk c c), w.IsCycle ∧ w.length ≤ p.length := by
  classical
  induction p with
  | nil => exact Or.inl SimpleGraph.Walk.IsPath.nil
  | @cons a b c e p ih =>
    rcases ih hp.tail with hpath | ⟨d,w,hw,hlen⟩
    · by_cases ha : a ∈ p.support
      · right
        let t := p.takeUntil a ha
        have ht : t.IsPath := hpath.takeUntil ha
        have hedge : s(a,b) ∉ t.edges := by
          intro he
          have he' : s(b,a) ∈ t.edges := by simpa only [Sym2.eq_swap] using he
          have hlen : t.length = 1 := ht.length_eq_one_of_mem_edges he'
          have hget : p.getVert 1 = a := by
            change (p.takeUntil a ha).length = 1 at hlen
            simpa only [hlen] using p.getVert_length_takeUntil ha
          have hp0 := hp 0 (by
            simp only [SimpleGraph.Walk.length_cons]
            have hh := p.length_takeUntil_le_length ha
            change t.length ≤ p.length at hh
            omega)
          apply hp0
          simpa only [SimpleGraph.Walk.getVert_zero, SimpleGraph.Walk.getVert_cons_succ] using hget.symm
        exact ⟨a,t.cons e,(SimpleGraph.Walk.cons_isCycle_iff _ _).mpr ⟨ht,hedge⟩,
          Nat.add_le_add_right (p.length_takeUntil_le_length ha) 1⟩
      · exact Or.inl ((SimpleGraph.Walk.cons_isPath_iff _ _).mpr ⟨hpath,ha⟩)
    · exact Or.inr ⟨d,w,hw,hlen.trans (by simp)⟩

theorem reduced_closed_length_ge {V : Type*} {G : SimpleGraph V} (k : ℕ)
    (hgirth : ∀ a (w : G.Walk a a), w.IsCycle → k ≤ w.length)
    {a : V} (p : G.Walk a a) (hne : 0 < p.length) (hp : ReducedWalk p) :
    k ≤ p.length := by
  rcases reduced_path_or_cycle p hp with hpath | ⟨c,w,hw,hlen⟩
  · have h := SimpleGraph.Walk.length_eq_zero_iff.mpr (SimpleGraph.Walk.isPath_iff_nil.mp hpath)
    omega
  · exact (hgirth c w hw).trans hlen

/-- The same girth bound controls a reduced path between distinct vertices of one
fiber of an immersion, even without a closing-seam condition. -/
theorem immersion_fiber_distance {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (f : G →g H) (hf : LocallyInjective f) (k : ℕ)
    (hgirth : ∀ a (w : H.Walk a a), w.IsCycle → k ≤ w.length)
    {a b : V} (hneq : a ≠ b) (heq : f a = f b) (p : G.Walk a b)
    (hp : ReducedWalk p) : k ≤ p.length := by
  have hpos : 0 < p.length := Nat.pos_iff_ne_zero.mpr (fun h => hneq (p.eq_of_length_eq_zero h))
  let w := (p.map f).copy rfl heq.symm
  have hr : ReducedWalk w := by
    intro n hn
    simpa only [w, SimpleGraph.Walk.length_copy, SimpleGraph.Walk.getVert_copy] using
      (hp.map f hf n (by simpa only [w, SimpleGraph.Walk.length_copy] using hn))
  simpa [w] using reduced_closed_length_ge k hgirth w (by simpa [w] using hpos) hr

/-- Simple paths are internally reduced. -/
theorem ReducedWalk.of_isPath {V : Type*} {G : SimpleGraph V} {a b : V}
    {p : G.Walk a b} (hp : p.IsPath) : ReducedWalk p := by
  intro n hn he
  have hh := hp.getVert_injOn (by change n ≤ p.length; omega)
    (by change n + 2 ≤ p.length; omega) he
  omega

/-- Bipartiteness gives four as the least possible cycle length, without a finiteness assumption. -/
theorem relationGraph_cycle_length {A B : Type*} (R : A → B → Prop)
    (a : A ⊕ B) (p : (relationGraph R).Walk a a) (hp : p.IsCycle) : 4 ≤ p.length := by
  let c : (relationGraph R).Coloring Bool :=
    {toFun := Sum.elim (fun _ => false) (fun _ => true)
     map_rel' := by intro x y h; cases x <;> cases y <;> simp_all [relationGraph]}
  have he := (c.even_length_iff_congr p).mpr Iff.rfl
  have ht := hp.three_le_length
  obtain ⟨n,hn⟩ := he
  omega

/-- The shift by a number in [0,r) remains injective modulo any modulus at least r. -/
theorem fin_natCast_injective (r s : ℕ) (hs : r ≤ s) :
    Function.Injective (fun v : Fin r => (v.val : ZMod s)) := by
  intro v w h
  by_cases hsz : s = 0
  · have : r = 0 := by omega
    exact Fin.elim0 (this ▸ v)
  · let : NeZero s := ⟨hsz⟩
    apply Fin.ext
    have hh := congrArg ZMod.val h
    simpa only [ZMod.val_natCast, Nat.mod_eq_of_lt (v.isLt.trans_le hs),
      Nat.mod_eq_of_lt (w.isLt.trans_le hs)] using hh

/-- Data of either of the two small-angle links. At V use the first block coordinate;
at W use the second and swap u,v. The membership and uniqueness fields are exactly
the partition of I(z) into blocks, not geometric conclusions. -/
structure ShiftScheme (I P B : Type*) (r : ℕ) (inc : P → Finset I) where
  size : B → ℕ
  size_ge : ∀ b, r ≤ size b
  labels : B → Finset I
  coord : ∀ b, {i // i ∈ labels b} → ZMod (size b)
  point : B → P
  incident : ∀ b i, i ∈ labels b → i ∈ inc (point b)
  unique : ∀ b c i, point b = point c → i ∈ labels b → i ∈ labels c → b = c

namespace ShiftScheme
variable {I P B : Type*} {r : ℕ} {inc : P → Finset I} (d : ShiftScheme I P B r inc)

abbrev XDirection := I × Fin r × Fin r
abbrev LDirection := Σ b : B, Fin r × ZMod (d.size b)

def attached (x : XDirection (I := I) (r := r)) (l : d.LDirection) : Prop :=
  ∃ hi : x.1 ∈ d.labels l.1,
    x.2.1 = l.2.1 ∧ l.2.2 = d.coord l.1 ⟨x.1,hi⟩ + (x.2.2.val : ZMod (d.size l.1))

def link : SimpleGraph ((XDirection (I := I) (r := r)) ⊕ d.LDirection) :=
  relationGraph d.attached

def projection : d.link →g relationGraph (fun i z => i ∈ inc z) where
  toFun := Sum.map (fun x => x.1) (fun l => d.point l.1)
  map_rel' := by
    intro x y h
    cases x with
    | inl x => cases y with
      | inl y => exact h.elim
      | inr l => obtain ⟨hi,_,_⟩ := h; exact d.incident l.1 x.1 hi
    | inr l => cases y with
      | inr m => exact h.elim
      | inl x => obtain ⟨hi,_,_⟩ := h; exact d.incident l.1 x.1 hi

theorem projection_locallyInjective : LocallyInjective d.projection := by
  intro a b c hab hac heq
  cases a with
  | inl x =>
    cases b with
    | inl y => exact hab.elim
    | inr b =>
      cases c with
      | inl y => exact hac.elim
      | inr c =>
        obtain ⟨i,u,v⟩ := x
        obtain ⟨b,ub,j⟩ := b
        obtain ⟨c,uc,k⟩ := c
        obtain ⟨hi,hui,hj⟩ := hab
        obtain ⟨hi',hui',hk⟩ := hac
        have hbc : d.point b = d.point c := Sum.inr.inj heq
        have hbc' := d.unique b c i hbc hi hi'
        subst c
        have hu : ub = uc := hui.symm.trans hui'
        subst uc
        have hjk : j = k := hj.trans hk.symm
        subst k
        rfl
  | inr l =>
    cases b with
    | inr m => exact hab.elim
    | inl x =>
      cases c with
      | inr m => exact hac.elim
      | inl y =>
        obtain ⟨b,ub,j⟩ := l
        obtain ⟨i,u,v⟩ := x
        obtain ⟨i',u',v'⟩ := y
        have hii : i = i' := Sum.inl.inj heq
        subst i'
        obtain ⟨hi,hu,hj⟩ := hab
        obtain ⟨hi',hu',hj'⟩ := hac
        have huu : u = u' := hu.trans hu'.symm
        subst u'
        have hvv : (v.val : ZMod (d.size b)) = (v'.val : ZMod (d.size b)) :=
          add_left_cancel (hj.symm.trans hj')
        have hv := fin_natCast_injective r (d.size b) (d.size_ge b) hvv
        subst v'
        rfl

/-- Girth transfers through the locally injective projection. -/
theorem link_cycle_length (k : ℕ)
    (hgirth : ∀ a (w : (relationGraph (fun i z => i ∈ inc z)).Walk a a),
      w.IsCycle → k ≤ w.length)
    (a : XDirection (I := I) (r := r) ⊕ d.LDirection)
    (p : d.link.Walk a a) (hp : p.IsCycle) : k ≤ p.length := by
  have hred : ReducedWalk p := by
    intro n hn he
    have h3 := hp.three_le_length
    by_cases hn0 : n = 0
    · subst n
      have he' : p.getVert p.length = p.getVert 2 := by simpa using he
      have hh := hp.getVert_injOn (by exact ⟨by omega, le_rfl⟩)
        (by exact ⟨by omega, by omega⟩) he'
      omega
    · have hh := hp.getVert_injOn (by exact ⟨by omega, by omega⟩)
        (by exact ⟨by omega, hn⟩) he
      omega
  have hmap := hred.map d.projection d.projection_locallyInjective
  simpa using reduced_closed_length_ge k hgirth (p.map d.projection)
    (by have h3 := hp.three_le_length; simp only [SimpleGraph.Walk.length_map]; omega) hmap

/-- Distinct directions of one x-label are separated by the full incidence girth. -/
theorem same_label_path_length (k : ℕ)
    (hgirth : ∀ a (w : (relationGraph (fun i z => i ∈ inc z)).Walk a a),
      w.IsCycle → k ≤ w.length)
    (i : I) (u v u' v' : Fin r) (hne : (u,v) ≠ (u',v'))
    (p : d.link.Walk (.inl (i,u,v)) (.inl (i,u',v'))) (hp : p.IsPath) :
    k ≤ p.length := by
  have hn : (Sum.inl (i,u,v) : XDirection (I := I) (r := r) ⊕ d.LDirection) ≠
      Sum.inl (i,u',v') := by
    intro h
    exact hne (Prod.mk.inj (Sum.inl.inj h)).2
  exact immersion_fiber_distance d.projection d.projection_locallyInjective k hgirth
    hn rfl p (ReducedWalk.of_isPath hp)

end ShiftScheme

end Release075

namespace Release075

/-- Pick one block and one leaf index for the two edges in the spanning tree. -/
structure BlockPresentation (I B : Type*) (r : ℕ) where
  block : B → CartesianBlock I r
  baseBlock : B
  baseIndex : Fin r

namespace BlockPresentation
variable {I B : Type*} {r : ℕ} (d : BlockPresentation I B r)

abbrev XEdge := I × Fin r × Fin r
abbrev LEdge := Σ b : B, Fin r × ZMod (d.block b).s
abbrev REdge := Σ b : B, Fin r × ZMod (d.block b).t
abbrev Edge := XEdge (I := I) (r := r) ⊕ (d.LEdge ⊕ d.REdge)

/-- The orientation of a face is `L x R⁻¹`, not a permuted product. -/
def triangleWord (b : B) (i : (d.block b).labels) (u v : Fin r) : FreeGroup d.Edge :=
  FreeGroup.of (.inr (.inl ⟨b,u,((d.block b).coordinates i).1 + (v.val : ZMod (d.block b).s)⟩)) *
  FreeGroup.of (.inl (i.val,u,v)) *
  (FreeGroup.of (.inr (.inr ⟨b,v,((d.block b).coordinates i).2 + (u.val : ZMod (d.block b).t)⟩)))⁻¹

def treeL : d.Edge := .inr (.inl ⟨d.baseBlock,d.baseIndex,0⟩)
def treeR : d.Edge := .inr (.inr ⟨d.baseBlock,d.baseIndex,0⟩)

def relators : Set (FreeGroup d.Edge) :=
  {w | (∃ b i u v, w = d.triangleWord b i u v) ∨
    w = FreeGroup.of d.treeL ∨ w = FreeGroup.of d.treeR}

abbrev GroupType := PresentedGroup d.relators

def edge (e : d.Edge) : d.GroupType := PresentedGroup.of e

def x (i : I) (u v : Fin r) : d.GroupType := d.edge (.inl (i,u,v))
def l (b : B) (u : Fin r) (j : ZMod (d.block b).s) : d.GroupType :=
  d.edge (.inr (.inl ⟨b,u,j⟩))
def rr (b : B) (v : Fin r) (k : ZMod (d.block b).t) : d.GroupType :=
  d.edge (.inr (.inr ⟨b,v,k⟩))

/-- The triangle faces impose precisely the factorization used by the rank proof. -/
theorem triangle_relation (b : B) (i : (d.block b).labels) (u v : Fin r) :
    d.x i u v = (d.l b u (((d.block b).coordinates i).1 + (v.val : ZMod (d.block b).s)))⁻¹ *
      d.rr b v (((d.block b).coordinates i).2 + (u.val : ZMod (d.block b).t)) := by
  have h := PresentedGroup.one_of_mem (rels := d.relators)
    (show d.triangleWord b i u v ∈ d.relators from Or.inl ⟨b,i,u,v,rfl⟩)
  apply (eq_inv_mul_iff_mul_eq).mpr
  exact mul_inv_eq_one.mp (by simpa only [triangleWord,map_mul,map_inv,
    edge,x,l,rr,PresentedGroup.of] using h)

theorem block_relations (b : B) : (d.block b).Relations d.x :=
  ⟨d.l b,d.rr b,d.triangle_relation b⟩

theorem treeL_eq_one : d.edge d.treeL = 1 :=
  PresentedGroup.one_of_mem (Or.inr (Or.inl rfl))

theorem treeR_eq_one : d.edge d.treeR = 1 :=
  PresentedGroup.one_of_mem (Or.inr (Or.inr rfl))

theorem edge_closure : Subgroup.closure (Set.range d.edge) = ⊤ :=
  PresentedGroup.closure_range_of d.relators

/-- A rectangular word is nontrivial exactly when it lies outside the actual normal
closure of the triangle and tree relators. This does not assume that nonmembership. -/
theorem rectangle_ne_one_iff (i : I) (u u' v v' : Fin r) :
    d.x i u v * (d.x i u' v)⁻¹ * d.x i u' v' * (d.x i u v')⁻¹ ≠ 1 ↔
      FreeGroup.of (.inl (i,u,v) : d.Edge) * (FreeGroup.of (.inl (i,u',v) : d.Edge))⁻¹ *
      FreeGroup.of (.inl (i,u',v') : d.Edge) * (FreeGroup.of (.inl (i,u,v') : d.Edge))⁻¹ ∉
        Subgroup.normalClosure d.relators := by
  rw [← PresentedGroup.mk_eq_one_iff]
  simp only [map_mul,map_inv,x,edge,PresentedGroup.of]

end BlockPresentation

/-- Left translation is an automorphism of the right-generator Cayley graph. -/
def cayleyLeft {G : Type*} [Group G] (S : Set G) (a : G) :
    SimpleGraph.mulCayley S →g SimpleGraph.mulCayley S where
  toFun := (a * ·)
  map_rel' := by
    intro x y h
    exact (SimpleGraph.mulCayley_adj_mul_iff_right).mpr h

theorem cayley_reachable_mul_left {G : Type*} [Group G] (S : Set G) (a : G)
    {b c : G} (h : (SimpleGraph.mulCayley S).Reachable b c) :
    (SimpleGraph.mulCayley S).Reachable (a*b) (a*c) := h.map (cayleyLeft S a)

/-- The connected Cayley graph is derived from generation, not included as data. -/
theorem cayley_connected_of_closure {G : Type*} [Group G] (S : Set G)
    (hS : Subgroup.closure S = ⊤) : (SimpleGraph.mulCayley S).Connected := by
  classical
  have hreach (g : G) : (SimpleGraph.mulCayley S).Reachable 1 g := by
    have hg : g ∈ Subgroup.closure S := by rw [hS]; exact Subgroup.mem_top _
    induction hg using Subgroup.closure_induction with
    | mem g hg =>
      by_cases h : 1 = g
      · subst g; exact SimpleGraph.Reachable.refl _
      · exact (SimpleGraph.mulCayley_adj' S 1 g |>.mpr
          ⟨h,g,hg,Or.inl (one_mul g)⟩).reachable
    | one => exact SimpleGraph.Reachable.refl _
    | mul a b _ _ ha hb =>
      exact ha.trans (by simpa using cayley_reachable_mul_left S a hb)
    | inv a _ ha =>
      have hh := cayley_reachable_mul_left S a⁻¹ ha
      simpa using hh.symm
  exact ⟨fun a b => (hreach a).symm.trans (hreach b)⟩

namespace BlockPresentation
variable {I B : Type*} {r : ℕ} (d : BlockPresentation I B r)

instance [Fintype I] [Fintype B] : Fintype d.Edge := by
  unfold Edge LEdge REdge
  infer_instance

theorem generators_finite [Fintype I] [Fintype B] : (Set.range d.edge).Finite :=
  Set.finite_range d.edge

theorem cayley_connected : (SimpleGraph.mulCayley (Set.range d.edge)).Connected :=
  cayley_connected_of_closure _ d.edge_closure

end BlockPresentation
end Release075

namespace Release075
noncomputable section
open scoped BigOperators
local instance (α : Type*) : DecidableEq α := Classical.decEq α

/-- The two formalizations of puncturing remove exactly parameter zero / the
line's own mark. Other marked points are retained in both. -/
theorem mem_puncturedLine_iff_incidence {T K : Type*} [Fintype T] [Field K] [Fintype K]
    (a z : T → K) (d : Projectivization K (T → K)) :
    z ∈ puncturedLine a d.rep ↔ PuncturedIncidence a z d := by
  classical
  simp only [puncturedLine,Finset.mem_image,Finset.mem_erase,Finset.mem_univ,and_true]
  constructor
  · rintro ⟨t,ht,rfl⟩
    refine ⟨?_,t,?_⟩
    · intro h
      have hh : affineLineMap a d.rep t = affineLineMap a d.rep 0 := by
        rw [show affineLineMap a d.rep 0 = a by ext t; simp [affineLineMap]]
        exact h
      exact ht (affineLineMap_injective a d.rep d.rep_nonzero hh)
    · rfl
  · rintro ⟨hz,t,ht⟩
    refine ⟨t,?_,ht⟩
    intro he
    subst t
    simp only [zero_smul,add_zero] at ht
    exact hz ht.symm

/-- A chosen two-block partition. The fields contain only finite combinatorial
partition data, no geometric or group-theoretic conclusion. -/
structure TwoBlockPartition (I : Type*) (r : ℕ) (A : Finset I) where
  zero : CartesianBlock I r
  one : CartesianBlock I r
  disjoint : Disjoint zero.labels one.labels
  cover : zero.labels ∪ one.labels = A

namespace MarkedLineData
variable {q r : ℕ} [Fact q.Prime] (d : MarkedLineData q r)

def incidences (z : Fin 20 → ZMod q) : Finset d.Label :=
  lineIncidence d.mark (fun i => (d.direction i).rep) z

theorem mem_incidences (z : Fin 20 → ZMod q) (i : d.Label) :
    i ∈ d.incidences z ↔ PuncturedIncidence (d.mark i) z (d.direction i) := by
  classical
  simp only [incidences,lineIncidence,Finset.mem_filter,Finset.mem_univ,true_and]
  exact mem_puncturedLine_iff_incidence _ _ _

theorem incidences_card_ge (z : Fin 20 → ZMod q) (hz : z ∉ d.exceptional) :
    4*r^2 ≤ (d.incidences z).card := by
  convert d.degree z hz using 1
  congr 1
  ext i
  simp only [d.mem_incidences,Finset.mem_filter,Finset.mem_univ,true_and]

abbrev Regular := {z : Fin 20 → ZMod q // z ∉ d.exceptional}
abbrev BlockIndex := d.Regular × Bool

instance : Fintype d.Regular := Fintype.ofFinite _

noncomputable def partition (hr : 0 < r) (z : d.Regular) :
    TwoBlockPartition d.Label r (d.incidences z) := by
  classical
  have hn : Nonempty (TwoBlockPartition d.Label r (d.incidences z)) := by
    obtain ⟨b₀,b₁,hd,hu⟩ := exists_two_cartesian_blocks r hr (d.incidences z)
      (d.incidences_card_ge z z.property)
    exact ⟨⟨b₀,b₁,hd,hu⟩⟩
  exact Classical.choice hn

noncomputable def block (hr : 0 < r) (b : d.BlockIndex) : CartesianBlock d.Label r :=
  if b.2 then (d.partition hr b.1).one else (d.partition hr b.1).zero

theorem block_incident (hr : 0 < r) (b : d.BlockIndex) (i : d.Label)
    (hi : i ∈ (d.block hr b).labels) : i ∈ d.incidences b.1 := by
  rw [← (d.partition hr b.1).cover]
  rcases b with ⟨z,e⟩
  cases e with
  | false => exact Finset.mem_union_left _ hi
  | true => exact Finset.mem_union_right _ hi

theorem block_unique (hr : 0 < r) (b c : d.BlockIndex) (i : d.Label)
    (hz : b.1.val = c.1.val) (hi : i ∈ (d.block hr b).labels)
    (hi' : i ∈ (d.block hr c).labels) : b = c := by
  rcases b with ⟨z,e⟩
  rcases c with ⟨w,f⟩
  have hw : z = w := Subtype.ext hz
  subst w
  cases e <;> cases f
  · rfl
  · exact ((Finset.disjoint_left.mp (d.partition hr z).disjoint) hi hi').elim
  · exact ((Finset.disjoint_left.mp (d.partition hr z).disjoint) hi' hi).elim
  · rfl

/-- The presentation is fixed from the finite data, before any quotient or
putative separation homomorphism is considered. -/
noncomputable def presentation (hr : 0 < r) : BlockPresentation d.Label d.BlockIndex r where
  block := d.block hr
  baseBlock := (⟨d.exists_regular.choose,d.exists_regular.choose_spec⟩,false)
  baseIndex := ⟨0,hr⟩

def RectangularNontriviality (hr : 0 < r) : Prop :=
  ∀ i, RectanglesSurvive ((d.presentation hr).x i)

/-- The complete finite-quotient argument applied to the actual fixed
presentation. The geometric nontriviality premise is established below. -/
theorem presentation_not_residuallyFinite (hr : 0 < r) (hq : r < q) (hq200 : 200 ≤ q)
    (hrect : d.RectangularNontriviality hr) :
    ¬ Group.ResiduallyFinite (d.presentation hr).GroupType := by
  classical
  apply not_residuallyFinite_of_line_blocks r q hq d.scalarGrid d.mark
    (fun i => (d.direction i).rep) d.marks_mem d.marks_injective
    (fun i => (d.direction i).rep_nonzero) (by simpa only [Fintype.card_fin] using d.degree_cutoff hq200)
    d.exceptional (d.presentation hr).x hrect _ (by
      simpa only [Fintype.card_fun,Fintype.card_fin,ZMod.card] using d.budget)
  intro z hz
  let p := d.partition hr ⟨z,hz⟩
  refine ⟨p.zero,p.one,p.disjoint,p.cover,?_,?_⟩
  · exact (d.presentation hr).block_relations (⟨z,hz⟩,false)
  · exact (d.presentation hr).block_relations (⟨z,hz⟩,true)

/-- Small-angle link at V. -/
noncomputable def vShift (hr : 0 < r) :
    ShiftScheme d.Label (Fin 20 → ZMod q) d.BlockIndex r d.incidences where
  size b := (d.block hr b).s
  size_ge b := (d.block hr b).hs
  labels b := (d.block hr b).labels
  coord b i := ((d.block hr b).coordinates i).1
  point b := b.1
  incident := d.block_incident hr
  unique := d.block_unique hr

/-- Small-angle link at W, with u,v interchanged. -/
noncomputable def wShift (hr : 0 < r) :
    ShiftScheme d.Label (Fin 20 → ZMod q) d.BlockIndex r d.incidences where
  size b := (d.block hr b).t
  size_ge b := (d.block hr b).ht
  labels b := (d.block hr b).labels
  coord b i := ((d.block hr b).coordinates i).2
  point b := b.1
  incident := d.block_incident hr
  unique := d.block_unique hr

/-- Switch the two incidence-graph parts without altering any incidence. -/
def swapIncidence : relationGraph (fun i z => i ∈ d.incidences z) →g
    relationGraph (fun z i => PuncturedIncidence (d.mark i) z (d.direction i)) where
  toFun := Sum.swap
  map_rel' := by
    intro x y h
    cases x with
    | inl i => cases y with
      | inl j => exact h.elim
      | inr z => exact (d.mem_incidences z i).mp h
    | inr z => cases y with
      | inr w => exact h.elim
      | inl i => exact (d.mem_incidences z i).mp h

theorem incidences_girth (a : d.Label ⊕ (Fin 20 → ZMod q))
    (p : (relationGraph (fun i z => i ∈ d.incidences z)).Walk a a) (hp : p.IsCycle) :
    14 ≤ p.length := by
  have hi : Function.Injective d.swapIncidence := by
    intro x y h
    have hh := congrArg Sum.swap h
    simpa [swapIncidence] using hh
  have hh := d.girth _ (p.map d.swapIncidence) (hp.map hi)
  simp only [SimpleGraph.Walk.length_map] at hh
  have he := relationGraph_cycle_length (fun i z => i ∈ d.incidences z) a p hp
  let c : (relationGraph (fun i z => i ∈ d.incidences z)).Coloring Bool :=
    {toFun := Sum.elim (fun _ => false) (fun _ => true)
     map_rel' := by intro x y h; cases x <;> cases y <;> simp_all [relationGraph]}
  obtain ⟨n,hn⟩ := (c.even_length_iff_congr p).mpr Iff.rfl
  omega

theorem v_link_girth (hr : 0 < r) (a)
    (p : (d.vShift hr).link.Walk a a) (hp : p.IsCycle) : 14 ≤ p.length :=
  (d.vShift hr).link_cycle_length 14 d.incidences_girth a p hp

theorem w_link_girth (hr : 0 < r) (a)
    (p : (d.wShift hr).link.Walk a a) (hp : p.IsCycle) : 14 ≤ p.length :=
  (d.wShift hr).link_cycle_length 14 d.incidences_girth a p hp

theorem v_same_label_distance (hr : 0 < r) (i : d.Label)
    (u v u' v' : Fin r) (hne : (u,v) ≠ (u',v'))
    (p : (d.vShift hr).link.Walk (.inl (i,u,v)) (.inl (i,u',v'))) (hp : p.IsPath) :
    14 ≤ p.length :=
  (d.vShift hr).same_label_path_length 14 d.incidences_girth i u v u' v' hne p hp

theorem w_same_label_distance (hr : 0 < r) (i : d.Label)
    (u v u' v' : Fin r) (hne : (u,v) ≠ (u',v'))
    (p : (d.wShift hr).link.Walk (.inl (i,u,v)) (.inl (i,u',v'))) (hp : p.IsPath) :
    14 ≤ p.length :=
  (d.wShift hr).same_label_path_length 14 d.incidences_girth i u v u' v' hne p hp

end MarkedLineData

end
end Release075

end OAI
