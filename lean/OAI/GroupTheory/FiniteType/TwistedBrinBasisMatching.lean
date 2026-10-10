import Mathlib
import OAI.GroupTheory.FiniteType.PosetTransport
import OAI.GroupTheory.FiniteType.TwistedBrinBasisGroundMatching

namespace OAI

open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
noncomputable section
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Classical
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits _root_.Representation _root_.OAI.Representation
open scoped MonoidalCategory
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
attribute [instance] AddCommGroup.toIntModule
open Set Function
open scoped Pointwise
namespace TwistedBrin.Basis.Matching
open PosetTransport
universe u v w t
variable {A : Type v} [Group A] {S : Type u} {ρ : A →* Equiv.Perm S}
variable {C : Basis ρ} {I : Type w} [Fintype I] (M : Matching C I)
variable {H : Type t} [Group H]

theorem near_cocycle_trivial [Nonempty I] (m : ℕ)
    (hav : ∀ B : CutDown.Near C m, (M.available B.val.val Finset.univ).Nonempty)
    (c : Cocycle (CutDown C) H) : (c.pull (CutDown.nearInclude C m)).Trivial := by
  classical
  let a := CutDown.nearInclude C m
  let p := M.projectPair m
  let q := M.contractPair m
  let s := M.selectedPair m
  let g := M.ground
  have hg : (c.pull g).Trivial :=
    (c.pull g).trivial_of_bottom ⟨Finset.univ,Finset.univ_nonempty⟩
      (fun _ => Finset.subset_univ _)
  have ht : (c.pull (g.comp s)).Trivial := (c.pull g).trivial_pull hg s
  have hq : (c.pull q).Trivial :=
    c.trivial_compare_rev q (g.comp s) (M.contractPair_le_ground m) ht
  have hf : (c.pull (a.comp p)).Trivial :=
    c.trivial_compare q (a.comp p) (M.contractPair_le_base m) hq
  exact (c.pull a).trivial_of_lower_fibers p
    (fun B => M.fiber_nonempty m B (hav B))
    (fun B => connected_of_exactIn _ (M.fiber_exactIn m B (hav B) 0)) hf
end TwistedBrin.Basis.Matching

namespace TwistedBrin.Basis.CutDown
open PosetTransport OrderChains
universe u v t
variable {A : Type v} [Group A] {S : Type u} {ρ : A →* Equiv.Perm S}
variable {H : Type t} [Group H]

theorem cocycle_trivial_high_rank [Nonempty S] (C : Basis ρ)
    (hC : 18 ≤ rank ρ C) (c : Cocycle (CutDown C) H) : c.Trivial := by
  classical
  let m := rank ρ C - 4
  let M := groundMatching C (Classical.choice ‹Nonempty S›) 9 (by omega)
  have hav (B : Near C m) : (M.available B.val.val Finset.univ).Nonempty := by
    apply M.available_nonempty B.val.upper
    simp only [Finset.card_univ,Fintype.card_fin]
    have hb := B.property
    change m ≤ rank ρ B.val.val at hb
    dsimp [m] at hb
    omega
  apply c.trivial_of_rank (fun B => rank ρ B.val) strictMono_rank m
  · intro B hB
    have hr : rank ρ B.val + 4 ≤ rank ρ C := by dsimp [m] at hB; omega
    obtain ⟨D,hD⟩ := upper_nonempty B (by omega)
    refine ⟨⟨⟨D,hD⟩⟩,?_⟩
    apply connected_of_exactIn
    exact exactIn_of_orderIso B.upperInterval
      (properCutInterval_exactIn ρ B.upper B.ne (n := 0) (by simpa using hr))
  · exact M.near_cocycle_trivial m hav c
end TwistedBrin.Basis.CutDown

namespace TwistedBrin.Basis.CutBasis
open PosetTransport
universe u v t
variable {A : Type v} [Group A] {S : Type u} {ρ : A →* Equiv.Perm S}
variable {H : Type t} [Group H]

theorem sublevel_cocycle_trivial [Nonempty S] (h : ℕ) (hh : 18 ≤ h)
    (c : Cocycle (rankBelow (fun B : CutBasis ρ => rank ρ B.val) h) H) : c.Trivial := by
  apply Cocycle.trivial_sublevel (fun B : CutBasis ρ => rank ρ B.val) strictMono_rank h c
  · intro C hC d
    let e : Set.Iio C ≃o CutDown C.val := lowerEquiv C
    let i : Set.Iio C →o CutDown C.val := ⟨e,e.monotone⟩
    let j : CutDown C.val →o Set.Iio C := ⟨e.symm,e.symm.monotone⟩
    have ht := CutDown.cocycle_trivial_high_rank C.val (by omega) (d.pull j)
    have hp := (d.pull j).trivial_pull ht i
    obtain ⟨v,hv⟩ := hp
    refine ⟨v,?_⟩
    intro x y hxy
    simpa only [Cocycle.pull,i,j,OrderHom.coe_mk,OrderIso.symm_apply_apply] using hv hxy
  · exact directed
end TwistedBrin.Basis.CutBasis

namespace ActionTransport
section
open PosetTransport
universe u v w
variable {G : Type u} [Group G] {P : Type v} [Preorder P] [MulAction G P]
variable {Q : Type w} [Group Q]

structure Gauge (p : Q →* G) (t : P → G) where
  value : G → P → Q
  one : ∀ x, value 1 x = 1
  mul : ∀ g h x, value (g*h) x = value g (h • x) * value h x
  projects : ∀ g x, p (value g x) = (t (g • x))⁻¹ * g * t x

theorem section_of_cocycle [Nonempty P] (hconn : Connected P)
    (hmono : ∀ g : G, Monotone (g • · : P → P))
    (p : Q →* G) (t : P → G) (d : Gauge p t) (c : Cocycle P Q)
    (hc : c.Trivial)
    (proj : ∀ {x y} (h : x ≤ y), p (c.edge h) = (t x)⁻¹ * t y)
    (equiv : ∀ g {x y} (h : x ≤ y), c.edge (hmono g h) =
      d.value g x * c.edge h * (d.value g y)⁻¹) :
    ∃ s : G →* Q, p.comp s = MonoidHom.id G := by
  classical
  obtain ⟨v,hv⟩ := hc
  let b : P := Classical.choice inferInstance
  let F (g : G) (x : P) : Q := v (g • x) * d.value g x * (v x)⁻¹
  have hF (g : G) (x y : P) : F g x = F g y := by
    apply hconn.constant (F g) ?_ x y
    intro a b hab
    have hv' := hv (hmono g hab)
    rw [equiv g hab] at hv'
    have hvab := hv hab
    dsimp [F]
    rw [← hv',← hvab]
    group
  have hproj (x y : P) : p (v x) * (t x)⁻¹ = p (v y) * (t y)⁻¹ := by
    apply hconn.constant (fun z => p (v z) * (t z)⁻¹) ?_ x y
    intro a b hab
    have hp := congrArg p (hv hab)
    rw [map_mul,proj hab] at hp
    rw [← hp]
    group
  let f : G →* Q := {
    toFun := fun g => F g b
    map_one' := by simp [F,d.one]
    map_mul' := by
      intro g h
      have hh := hF g (h • b) b
      dsimp [F] at hh ⊢
      rw [mul_smul,d.mul,← hh]
      group }
  let k := p (v b) * (t b)⁻¹
  have hf (g : G) : p (f g) = k * g * k⁻¹ := by
    change p (v (g • b) * d.value g b * (v b)⁻¹) = _
    rw [map_mul,map_mul,map_inv,d.projects]
    have hh := hproj (g • b) b
    calc
      _ = (p (v (g • b)) * (t (g • b))⁻¹) * g * t b * (p (v b))⁻¹ := by group
      _ = (p (v b) * (t b)⁻¹) * g * t b * (p (v b))⁻¹ := by rw [hh]
      _ = k * g * k⁻¹ := by dsimp [k]; group
  let j : G →* G := {
    toFun := fun g => k⁻¹ * g * k
    map_one' := by group
    map_mul' := by intros; group }
  refine ⟨f.comp j,?_⟩
  ext g
  change p (f (k⁻¹ * g * k)) = g
  rw [hf]
  group

end

section
open PosetTransport
open scoped Pointwise
universe u v w
variable {G : Type u} [Group G] {P : Type v} [Preorder P] [MulAction G P]
class IsMonotoneAction (G P : Type*) [Group G] [Preorder P] [MulAction G P] : Prop where
  mono : ∀ g : G, Monotone (g • · : P → P)

structure Frames (G : Type u) [Group G] (P : Type v) [MulAction G P] where
  Index : Type v
  rep : Index → P
  index : P → Index
  index_rep : ∀ i, index (rep i) = i
  index_smul : ∀ (g : G) x, index (g • x) = index x
  element : P → G
  frame : ∀ x, element x • rep (index x) = x

namespace Frames
variable {X : Type v} [MulAction G X] (F : Frames G X)
def stab (i : F.Index) : Subgroup G := MulAction.stabilizer G (F.rep i)
lemma mem_stab (i : F.Index) (g : G) : g ∈ F.stab i ↔ g • F.rep i = F.rep i := Iff.rfl
lemma difference_mem (g : G) (x : X) :
    (F.element (g • x))⁻¹ * g * F.element x ∈ F.stab (F.index x) := by
  rw [mem_stab,mul_smul,mul_smul,F.frame]
  apply inv_smul_eq_iff.mpr
  simpa only [F.index_smul] using (F.frame (g • x)).symm
lemma difference (x y : X) (g : G) (h : g • x = y) :
    (F.element y)⁻¹ * g * F.element x ∈ F.stab (F.index x) := by
  simpa only [h] using F.difference_mem g x
end Frames

variable [IsMonotoneAction G P]
lemma act_mono (g : G) : Monotone (g • · : P → P) := IsMonotoneAction.mono g

def Edge (P : Type v) [Preorder P] := {xy : P × P // xy.1 ≤ xy.2}
namespace Edge
instance : MulAction G (Edge P) where
  smul g e := ⟨(g • e.val.1,g • e.val.2),act_mono g e.property⟩
  one_smul e := by
    apply Subtype.ext
    change (1 • e.val.1, 1 • e.val.2) = e.val
    simp
  mul_smul g h e := by
    apply Subtype.ext
    change ((g*h) • e.val.1, (g*h) • e.val.2) = (g • h • e.val.1,g • h • e.val.2)
    simp [mul_smul]
@[simp] lemma fst_smul (g : G) (e : Edge P) : (g • e).val.1 = g • e.val.1 := rfl
@[simp] lemma snd_smul (g : G) (e : Edge P) : (g • e).val.2 = g • e.val.2 := rfl
end Edge

lemma eq_top_of_frames [Nonempty P] (hconn : Connected P)
    (F : Frames G P) (E : Frames G (Edge P)) (K : Subgroup G)
    (hstab : ∀ i, F.stab i ≤ K)
    (hend : ∀ i, F.element (E.rep i).val.1 ∈ K ∧ F.element (E.rep i).val.2 ∈ K) :
    K = ⊤ := by
  classical
  let c (x : P) : Set G := F.element x • (K : Set G)
  have hcos (g : G) (x : P) :
      F.element (g • x) • (K : Set G) = (g * F.element x) • (K : Set G) := by
    apply (leftCoset_eq_iff K).mpr
    exact hstab _ (by simpa only [mul_assoc] using F.difference_mem g x)
  have hc (x y : P) : c x = c y := by
    apply hconn.constant c ?_ x y
    intro a b hab
    let e : Edge P := ⟨(a,b),hab⟩
    let i := E.index e
    let g := E.element e
    have ha : g • (E.rep i).val.1 = a := congrArg (fun e : Edge P => e.val.1) (E.frame e)
    have hb : g • (E.rep i).val.2 = b := congrArg (fun e : Edge P => e.val.2) (E.frame e)
    dsimp [c]
    rw [← ha,← hb,hcos,hcos]
    apply (leftCoset_eq_iff K).mpr
    convert K.mul_mem (K.inv_mem (hend i).1) (hend i).2 using 1; group
  let b : P := Classical.choice inferInstance
  have h0 : F.element (F.rep (F.index b)) ∈ K := by
    apply hstab (F.index b)
    rw [Frames.mem_stab]
    simpa only [F.index_rep] using F.frame (F.rep (F.index b))
  apply top_unique
  intro g _
  have he := hc (g • F.rep (F.index b)) (F.rep (F.index b))
  dsimp [c] at he
  rw [hcos] at he
  have hh := (leftCoset_eq_iff K).mp he
  have hg : (F.element (F.rep (F.index b)))⁻¹ * g⁻¹ * F.element (F.rep (F.index b)) ∈ K := by
    simpa only [mul_inv_rev] using hh
  have hi := K.mul_mem (K.mul_mem h0 hg) (K.inv_mem h0)
  have hgi : g⁻¹ ∈ K := by convert hi using 1; group
  simpa only [inv_inv] using K.inv_mem hgi

lemma fg_of_frames [Nonempty P] (hconn : Connected P)
    (F : Frames G P) (E : Frames G (Edge P))
    [Finite F.Index] [Finite E.Index] (hstab : ∀ i, (F.stab i).FG) : Group.FG G := by
  classical
  choose S hS using hstab
  let T : Set G := (⋃ i, (S i : Set G)) ∪
    Set.range (fun i => F.element (E.rep i).val.1) ∪
    Set.range (fun i => F.element (E.rep i).val.2)
  have hfin : T.Finite := ((Set.finite_iUnion fun i => (S i).finite_toSet).union
    (Set.finite_range _)).union (Set.finite_range _)
  have htop : Subgroup.closure T = ⊤ := by
    apply eq_top_of_frames hconn F E
    · intro i
      rw [← hS i]
      apply Subgroup.closure_mono
      intro g hg
      exact Or.inl (Or.inl (Set.mem_iUnion.mpr ⟨i,hg⟩))
    · intro i
      constructor
      · exact Subgroup.subset_closure (Or.inl (Or.inr ⟨i,rfl⟩))
      · exact Subgroup.subset_closure (Or.inr ⟨i,rfl⟩)
  exact Group.fg_iff.mpr ⟨T,htop,hfin⟩
end

section
open PosetTransport
universe u v w
variable {G : Type u} [Group G] {P : Type v} [Preorder P] [MulAction G P]
variable {Q : Type w} [Group Q]
structure LiftedFrames (F : Frames G P) (p : Q →* G) where
  hom : ∀ i, F.stab i →* Q
  projects : ∀ i h, p (hom i h) = (h : G)
namespace LiftedFrames
variable {F : Frames G P} {p : Q →* G} (J : LiftedFrames F p)
noncomputable def eval (i : F.Index) (g : G) : Q := by
  classical
  exact if h : g ∈ F.stab i then J.hom i ⟨g,h⟩ else 1
omit [Preorder P] in
lemma eval_valid [Preorder P] (i : F.Index) (g : G) (h : g ∈ F.stab i) :
    J.eval i g = J.hom i ⟨g,h⟩ := by
  classical
  exact dite_eq_left h
lemma eval_one (i : F.Index) : J.eval i 1 = 1 := by
  rw [J.eval_valid i 1 (F.stab i).one_mem]
  exact (J.hom i).map_one
lemma eval_mul (i : F.Index) (g h : G) (hg : g ∈ F.stab i) (hh : h ∈ F.stab i) :
    J.eval i (g*h) = J.eval i g * J.eval i h := by
  rw [J.eval_valid _ _ ((F.stab i).mul_mem hg hh),J.eval_valid _ _ hg,J.eval_valid _ _ hh]
  exact (J.hom i).map_mul ⟨g,hg⟩ ⟨h,hh⟩
lemma eval_projects (i : F.Index) (g : G) (hg : g ∈ F.stab i) : p (J.eval i g) = g := by
  rw [J.eval_valid _ _ hg]
  exact J.projects _ _
noncomputable def gauge : Gauge p F.element where
  value g x := J.eval (F.index x) ((F.element (g • x))⁻¹ * g * F.element x)
  one x := by simpa using J.eval_one (F.index x)
  mul g h x := by
    simp only [F.index_smul,mul_smul]
    have hg : (F.element (g • h • x))⁻¹ * g * F.element (h • x) ∈ F.stab (F.index x) := by
      simpa only [F.index_smul] using F.difference_mem g (h • x)
    rw [← J.eval_mul _ _ _ hg (F.difference_mem h x)]
    congr 1
    group
  projects g x := J.eval_projects _ _ (F.difference_mem g x)
end LiftedFrames

variable [IsMonotoneAction G P]
variable {p : Q →* G}

def edgeTransport (F : Frames G P) (E : Frames G (Edge P))
    (d : Gauge p F.element) (L : E.Index → Q) (i : E.Index) (g : G) : Q :=
  d.value g (E.rep i).val.1 * L i * (d.value g (E.rep i).val.2)⁻¹
noncomputable def rawEdge (F : Frames G P) (E : Frames G (Edge P))
    (d : Gauge p F.element) (L : E.Index → Q) (e : Edge P) : Q :=
  edgeTransport F E d L (E.index e) (E.element e)

lemma rawEdge_projects (F : Frames G P) (E : Frames G (Edge P))
    (p : Q →* G) (d : Gauge p F.element) (L : E.Index → Q)
    (hL : ∀ i, p (L i) = (F.element (E.rep i).val.1)⁻¹ * F.element (E.rep i).val.2)
    (e : Edge P) : p (rawEdge F E d L e) = (F.element e.val.1)⁻¹ * F.element e.val.2 := by
  have h1 := congrArg (fun e : Edge P => e.val.1) (E.frame e)
  have h2 := congrArg (fun e : Edge P => e.val.2) (E.frame e)
  change E.element e • (E.rep (E.index e)).val.1 = e.val.1 at h1
  change E.element e • (E.rep (E.index e)).val.2 = e.val.2 at h2
  simp only [rawEdge,edgeTransport,map_mul,map_inv,d.projects,hL,h1,h2]
  group

lemma edgeTransport_stabilizer (F : Frames G P) (E : Frames G (Edge P))
    (d : Gauge p F.element) (L : E.Index → Q)
    (coherent : ∀ i k, k ∈ E.stab i →
      d.value k (E.rep i).val.1 * L i = L i * d.value k (E.rep i).val.2)
    (i : E.Index) (g k : G) (hk : k ∈ E.stab i) :
    edgeTransport F E d L i (g*k) = edgeTransport F E d L i g := by
  have h1 := congrArg (fun e : Edge P => e.val.1) hk
  have h2 := congrArg (fun e : Edge P => e.val.2) hk
  change k • (E.rep i).val.1 = (E.rep i).val.1 at h1
  change k • (E.rep i).val.2 = (E.rep i).val.2 at h2
  simp only [edgeTransport,d.mul,h1,h2]
  rw [mul_assoc (d.value g _),coherent i k hk]
  group

lemma rawEdge_equivariant (F : Frames G P) (E : Frames G (Edge P))
    (d : Gauge p F.element) (L : E.Index → Q)
    (coherent : ∀ i k, k ∈ E.stab i →
      d.value k (E.rep i).val.1 * L i = L i * d.value k (E.rep i).val.2)
    (g : G) (e : Edge P) : rawEdge F E d L (g • e) =
      d.value g e.val.1 * rawEdge F E d L e * (d.value g e.val.2)⁻¹ := by
  have hk := E.difference_mem g e
  let k := (E.element (g • e))⁻¹ * g * E.element e
  have he : E.element (g • e) * k = g * E.element e := by dsimp [k]; group
  have hh := edgeTransport_stabilizer F E d L coherent (E.index e) (E.element (g • e)) k hk
  rw [he] at hh
  have h1 := congrArg (fun e : Edge P => e.val.1) (E.frame e)
  have h2 := congrArg (fun e : Edge P => e.val.2) (E.frame e)
  change E.element e • (E.rep (E.index e)).val.1 = e.val.1 at h1
  change E.element e • (E.rep (E.index e)).val.2 = e.val.2 at h2
  simp only [rawEdge,E.index_smul]
  rw [← hh]
  simp only [edgeTransport,d.mul,h1,h2]
  group
end

open PosetTransport
universe u v w z
variable {G : Type u} [Group G] {P : Type v} [Preorder P] [MulAction G P]
variable {Q : Type w} [Group Q] {R : Type z} [Group R]
namespace Gauge
variable {p : Q →* G} {t : P → G}
def map (d : Gauge p t) (q : Q →* R) (p' : R →* G) (hp' : p'.comp q = p) : Gauge p' t where
  value g x := q (d.value g x)
  one x := by rw [d.one,map_one]
  mul g h x := by rw [d.mul,map_mul]
  projects g x := (DFunLike.congr_fun hp' _).trans (d.projects g x)
end Gauge
variable [IsMonotoneAction G P]
namespace Edge
def diag (x : P) : Edge P := ⟨(x,x),le_rfl⟩
@[simp] lemma diag_smul (g : G) (x : P) : diag (g • x) = g • diag x := rfl
end Edge

def Triangle (P : Type v) [Preorder P] :=
  {xyz : P × P × P // xyz.1 ≤ xyz.2.1 ∧ xyz.2.1 ≤ xyz.2.2}
namespace Triangle
instance : MulAction G (Triangle P) where
  smul g t := ⟨(g • t.val.1,g • t.val.2.1,g • t.val.2.2),
    act_mono g t.property.1,act_mono g t.property.2⟩
  one_smul t := by
    apply Subtype.ext
    change (1 • t.val.1,1 • t.val.2.1,1 • t.val.2.2) = t.val
    simp
  mul_smul g h t := by
    apply Subtype.ext
    change ((g*h) • t.val.1,(g*h) • t.val.2.1,(g*h) • t.val.2.2) =
      (g • h • t.val.1,g • h • t.val.2.1,g • h • t.val.2.2)
    simp only [mul_smul]
def e01 (t : Triangle P) : Edge P := ⟨(t.val.1,t.val.2.1),t.property.1⟩
def e12 (t : Triangle P) : Edge P := ⟨(t.val.2.1,t.val.2.2),t.property.2⟩
def e02 (t : Triangle P) : Edge P := ⟨(t.val.1,t.val.2.2),t.property.1.trans t.property.2⟩
@[simp] lemma e01_smul (g : G) (t : Triangle P) : e01 (g • t) = g • e01 t := rfl
@[simp] lemma e12_smul (g : G) (t : Triangle P) : e12 (g • t) = g • e12 t := rfl
@[simp] lemma e02_smul (g : G) (t : Triangle P) : e02 (g • t) = g • e02 t := rfl
end Triangle

lemma flat_triangle_translate {p : Q →* G} {f : P → G} (d : Gauge p f)
    (c : Edge P → Q)
    (heq : ∀ g e, c (g • e) = d.value g e.val.1 * c e * (d.value g e.val.2)⁻¹)
    (t : Triangle P) (ht : c t.e01 * c t.e12 = c t.e02) (g : G) :
    c (g • t).e01 * c (g • t).e12 = c (g • t).e02 := by
  simp only [Triangle.e01_smul,Triangle.e12_smul,Triangle.e02_smul,heq]
  change (d.value g t.val.1 * c t.e01 * (d.value g t.val.2.1)⁻¹) *
    (d.value g t.val.2.1 * c t.e12 * (d.value g t.val.2.2)⁻¹) =
      d.value g t.val.1 * c t.e02 * (d.value g t.val.2.2)⁻¹
  rw [← ht]
  group

noncomputable def cocycleOfFlat (F : Frames G P) (T : Frames G (Triangle P))
    {p : Q →* G} (d : Gauge p F.element) (c : Edge P → Q)
    (heq : ∀ g e, c (g • e) = d.value g e.val.1 * c e * (d.value g e.val.2)⁻¹)
    (hdiag : ∀ i, c (Edge.diag (F.rep i)) = 1)
    (htri : ∀ i, c (T.rep i).e01 * c (T.rep i).e12 = c (T.rep i).e02) : Cocycle P Q where
  edge h := c ⟨(_, _),h⟩
  refl x := by
    change c (Edge.diag x) = 1
    rw [← F.frame x,Edge.diag_smul,heq,hdiag]
    change d.value _ (F.rep _) * 1 * (d.value _ (F.rep _))⁻¹ = 1
    group
  comp {x y z} h k := by
    let t : Triangle P := ⟨(x,y,z),h,k⟩
    change c t.e01 * c t.e12 = c t.e02
    rw [← T.frame t]
    exact flat_triangle_translate d c heq _ (htri _) _

lemma rawEdge_map (F : Frames G P) (E : Frames G (Edge P))
    {p : Q →* G} (d : Gauge p F.element) (L : E.Index → Q)
    (q : Q →* R) (p' : R →* G) (hp' : p'.comp q = p) (e : Edge P) :
    rawEdge F E (d.map q p' hp') (fun i => q (L i)) e = q (rawEdge F E d L e) := by
  simp only [rawEdge,edgeTransport,Gauge.map,map_mul,map_inv]
end ActionTransport

end

end OAI
