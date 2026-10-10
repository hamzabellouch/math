import Mathlib
import OAI.Algebra.GroupRing.MapRestrict

namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.GraphQuotient
open SimpleGraph
variable {V W : Type} (G : SimpleGraph V) (H : SimpleGraph W) (q : V→W)
    (hq : ∀ v w,G.Adj v w→q v=q w ∨ H.Adj (q v) (q w))
include hq in
lemma reachable {v w : V} (h : G.Reachable v w) : H.Reachable (q v) (q w) := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => exact Reachable.rfl
  | @cons v u w h p ih =>
    rcases hq v u h with h|h
    · exact h ▸ ih
    · exact h.reachable.trans ih

include hq in
lemma connected (hs : Function.Surjective q) (hc : G.Connected) : H.Connected := by
  have : Nonempty W := hc.nonempty.map q
  refine ⟨fun v w=>?_⟩
  obtain ⟨v,rfl⟩ := hs v
  obtain ⟨w,rfl⟩ := hs w
  exact reachable G H q hq (hc v w)

include hq in
lemma distance_sub (hc : G.Connected) (hcH : H.Connected) (root : V) (N : ℕ)
    (hb : ∀ v,G.dist v root≤N→q v=q root) (v : V) :
    H.dist (q v) (q root)≤G.dist v root-N := by
  generalize hn : G.dist v root=n
  induction n using Nat.strong_induction_on generalizing v with
  | h n ih =>
    by_cases hv : G.dist v root≤N
    · rw [hb v hv,dist_self]
      exact Nat.zero_le _
    · have hv' : v≠root := by rintro rfl;simp only [dist_self] at hv;omega
      obtain ⟨u,hu,hd⟩ := BFSTree.exists_parent G hc root v hv'
      have hi := ih (G.dist u root) (by omega) u rfl
      rcases hq v u hu with he|he
      · rw [he]
        omega
      · have hh := hcH.dist_triangle (u:=q v) (v:=q u) (w:=q root)
        rw [H.dist_eq_one_iff_adj.mpr he] at hh
        omega
end TorsionFreeZeroDivisors.GraphQuotient

namespace TorsionFreeZeroDivisors.PlanarMap

section
open scoped Classical
open PermutationCycles MapEuler
variable {V : Type} (G : SimpleGraph V)
/-- A concrete finite rotation map, with its exact Euler equality and an
isomorphism to the represented simple graph. Loops and parallel darts are
allowed; no abstract planar-minor or separator hypotheses are used. -/
structure Model where
  Dart : Type
  [finiteDart : Fintype Dart]
  rotation : Equiv.Perm Dart
  pairing : Equiv.Perm Dart
  involutive : Function.Involutive pairing
  genus : GenusZero rotation pairing
  iso : graph rotation pairing involutive ≃g G
attribute [instance] Model.finiteDart
variable {G}

def Model.induced (M : Model G) (S : Set V) : Model (G.induce S) where
  Dart := {x : M.Dart // M.iso (cycle M.rotation x)∈S}
  rotation := MapRestrict.rotation M.rotation {v | M.iso v∈S}
  pairing := MapRestrict.pairing M.rotation M.pairing M.involutive {v | M.iso v∈S}
  involutive := MapRestrict.pairing_involutive M.rotation M.pairing M.involutive {v | M.iso v∈S}
  genus := MapRestrict.induced_genusZero M.rotation M.pairing M.involutive {v | M.iso v∈S} M.genus
  iso := (MapRestrict.graphIso M.rotation M.pairing M.involutive {v | M.iso v∈S}).trans
    (M.iso.induce ⟨fun _ h=>h,M.iso.injective.injOn,fun v hv=>by
      refine ⟨M.iso.symm v,?_,M.iso.apply_symm_apply v⟩
      change M.iso (M.iso.symm v)∈S
      simpa only [M.iso.apply_symm_apply] using hv⟩)

/-- Sharp radius separation transported along the actual graph isomorphism. -/
theorem Model.radius_separator (M : Model G) (hc : G.Connected) (root : V) (r : ℕ)
    (hr : ∀ v,G.dist root v≤r) (active : Finset V) :
    ∃ cut side : Finset V,root∈cut ∧ cut.card≤2*r+1 ∧ (cut.erase root).card≤2*r ∧
      3*(active.filter (fun v=>v∉cut ∧ v∈side)).card≤2*active.card ∧
      3*(active.filter (fun v=>v∉cut ∧ v∉side)).card≤2*active.card ∧
      ∀ v w,v∉cut→w∉cut→G.Adj v w→(v∈side↔w∈side) := by
  let e := M.iso.toEquiv
  let A := active.map e.symm.toEmbedding
  obtain ⟨C,D,hrC,hC,hCe,h₁,h₂,hsep⟩ := MapEuler.radius_separator M.rotation M.pairing
    M.involutive M.genus (M.iso.connected_iff.mpr hc) (e.symm root) r (by
      intro v
      obtain ⟨p,hp⟩ := hc.exists_walk_length_eq_dist root (e v)
      have hh := (graph M.rotation M.pairing M.involutive).dist_le (p.map M.iso.symm.toHom)
      change (graph M.rotation M.pairing M.involutive).dist (e.symm root) (e.symm (e v))≤(p.map M.iso.symm.toHom).length at hh
      rw [e.symm_apply_apply,SimpleGraph.Walk.length_map,hp] at hh
      exact hh.trans (hr (e v))) A
  let cut := C.map e.toEmbedding
  let side := D.map e.toEmbedding
  have hcut (v : V) : v∈cut↔e.symm v∈C := by simp only [cut,Finset.mem_map_equiv]
  have hside (v : V) : v∈side↔e.symm v∈D := by simp only [side,Finset.mem_map_equiv]
  have hroot : root∈cut := (hcut root).mpr hrC
  have hcard : cut.card=C.card := Finset.card_map _
  have hfilter (p : Cycle M.rotation→Prop) [DecidablePred p] :
      (active.filter (fun v=>p (e.symm v))).card=(A.filter p).card := by
    rw [←Finset.card_map (f:=e.symm.toEmbedding)]
    congr 1
    ext v
    simp only [Finset.mem_map,Finset.mem_filter]
    constructor
    · rintro ⟨x,⟨hx,hp⟩,rfl⟩
      exact ⟨Finset.mem_map.mpr ⟨x,hx,rfl⟩,hp⟩
    · rintro ⟨hv,hp⟩
      obtain ⟨x,hx,rfl⟩ := Finset.mem_map.mp hv
      exact ⟨x,⟨hx,hp⟩,rfl⟩
  refine ⟨cut,side,hroot,by omega,?_,?_,?_,?_⟩
  · rw [Finset.card_erase_of_mem hroot,hcard,←Finset.card_erase_of_mem hrC]
    exact hCe
  · have he : active.filter (fun v=>v∉cut ∧ v∈side)=active.filter (fun v=>e.symm v∉C ∧ e.symm v∈D) := by
      ext v;simp only [Finset.mem_filter,hcut,hside]
    rw [he,hfilter (fun v=>v∉C ∧ v∈D)]
    simpa only [A,Finset.card_map] using h₁
  · have he : active.filter (fun v=>v∉cut ∧ v∉side)=active.filter (fun v=>e.symm v∉C ∧ e.symm v∉D) := by
      ext v;simp only [Finset.mem_filter,hcut,hside]
    rw [he,hfilter (fun v=>v∉C ∧ v∉D)]
    simpa only [A,Finset.card_map] using h₂
  · intro v w hv hw he
    rw [hside,hside]
    exact hsep (e.symm v) (e.symm w) (fun h=>hv ((hcut v).mpr h))
      (fun h=>hw ((hcut w).mpr h)) (M.iso.symm.toHom.map_adj he)

end

open scoped Classical
open PermutationCycles MapEuler
variable {V : Type} (G : SimpleGraph V) (B : Set V)
structure Contraction where
  Vertex : Type
  [finiteVertex : Fintype Vertex]
  graph : SimpleGraph Vertex
  model : Model graph
  quotient : V→Vertex
  surjective : Function.Surjective quotient
  eq_iff : ∀ v w,quotient v=quotient w↔v=w ∨ (v∈B ∧ w∈B)
  adj : ∀ v w,G.Adj v w→quotient v=quotient w ∨ graph.Adj (quotient v) (quotient w)
  lift_adj : ∀ v w,graph.Adj v w→∃ x y,G.Adj x y ∧ quotient x=v ∧ quotient y=w
attribute [instance] Contraction.finiteVertex
variable {G B}

/-- A connected induced set is contracted by choosing its literal spanning
submatching and replacing the rotations by the contour permutation. -/
def Model.contract (M : Model G) (hB : (G.induce B).Connected) : Contraction G B := by
  let S : Set (Cycle M.rotation) := {v | M.iso v∈B}
  let s := MapRestrict.rotation M.rotation S
  let a := MapRestrict.pairing M.rotation M.pairing M.involutive S
  let hi := MapRestrict.pairing_involutive M.rotation M.pairing M.involutive S
  have hc : (graph s a hi).Connected := ((M.induced B).iso.connected_iff).mpr hB
  let T := hc.exists_isTree_le.choose
  have hT : T≤graph s a hi := hc.exists_isTree_le.choose_spec.1
  have ht : T.IsTree := hc.exists_isTree_le.choose_spec.2
  let ρ := MapContract.rotation M.rotation M.pairing M.involutive S T hT
  let γ := MapContract.pairing M.rotation M.pairing M.involutive S T hT
  let hγ := MapContract.pairing_involutive M.rotation M.pairing M.involutive S T hT
  let q := MapContract.quotient M.rotation M.pairing M.involutive S T hT M.genus ht
  refine { Vertex := Cycle ρ
           graph := graph ρ γ hγ
           model := {
             Dart := M.Dart
             rotation := ρ
             pairing := γ
             involutive := hγ
             genus := MapContract.genusZero M.rotation M.pairing M.involutive S T hT M.genus
             iso := .refl }
           quotient := fun v=>q (M.iso.symm v)
           surjective := (MapContract.quotient_surjective M.rotation M.pairing M.involutive S T hT M.genus ht).comp M.iso.symm.surjective
           eq_iff := ?_
           adj := ?_
           lift_adj := ?_ }
  · intro v w
    rw [MapContract.quotient_eq_iff]
    simp only [S,Set.mem_ofPred_eq,M.iso.apply_symm_apply,M.iso.symm.injective.eq_iff]
  · intro v w h
    exact MapContract.quotient_adj M.rotation M.pairing M.involutive S T hT M.genus ht (M.iso.symm.toHom.map_adj h)
  · intro v w h
    obtain ⟨x,y,hxy,hx,hy⟩ := MapContract.adj_lift M.rotation M.pairing M.involutive S T hT M.genus ht h
    exact ⟨M.iso x,M.iso y,M.iso.toHom.map_adj hxy,by simpa only [M.iso.symm_apply_apply] using hx,by simpa only [M.iso.symm_apply_apply] using hy⟩

end TorsionFreeZeroDivisors.PlanarMap

namespace TorsionFreeZeroDivisors.CutTransfer
open scoped Classical
variable {V W : Type} [Fintype V] [DecidableEq W] (G : SimpleGraph V) (H : SimpleGraph W)
    (A : Finset V) (f : V→W)

theorem pullback (hinj : Set.InjOn f A)
    (hmap : ∀ v∈A,∀ w∈A,G.Adj v w→f v=f w ∨ H.Adj (f v) (f w))
    (C D budget : Finset W) (K : ℕ) (hcost : budget.card≤K)
    (hbudget : ∀ v∈A,f v∈C→f v∈budget)
    (h₁ : 3*((A.image f).filter (fun v=>v∉C ∧ v∈D)).card≤2*(A.image f).card)
    (h₂ : 3*((A.image f).filter (fun v=>v∉C ∧ v∉D)).card≤2*(A.image f).card)
    (hsep : ∀ v w,v∉C→w∉C→H.Adj v w→(v∈D↔w∈D)) :
    ∃ cut side : Finset V,cut⊆A ∧ cut.card≤K ∧
      3*(A.filter (fun v=>v∉cut ∧ v∈side)).card≤2*A.card ∧
      3*(A.filter (fun v=>v∉cut ∧ v∉side)).card≤2*A.card ∧
      ∀ v∈A,∀ w∈A,v∉cut→w∉cut→G.Adj v w→(v∈side↔w∈side) := by
  let cut := A.filter (fun v=>f v∈C)
  let side := Finset.univ.filter (fun v=>f v∈D)
  have hsub : cut⊆A := Finset.filter_subset _ _
  have hcut {v : V} (hv : v∈A) : v∈cut↔f v∈C := by simp only [cut,Finset.mem_filter,hv,true_and]
  have hside (v : V) : v∈side↔f v∈D := by simp only [side,Finset.mem_filter,Finset.mem_univ,true_and]
  have hcard : (A.image f).card=A.card := Finset.card_image_of_injOn hinj
  have hfilter (p : W→Prop) [DecidablePred p] :
      ((A.image f).filter p).card=(A.filter (fun v=>p (f v))).card := by
    rw [Finset.filter_image]
    exact Finset.card_image_of_injOn (hinj.mono (Finset.filter_subset _ _))
  have hfirst : (A.image f).filter (fun v=>v∉C ∧ v∈D) =
      (A.filter (fun v=>v∉cut ∧ v∈side)).image f := by
    rw [Finset.filter_image]
    congr 1
    apply Finset.filter_congr
    intro v hv
    simp only [hcut hv,hside]
  have hsecond : (A.image f).filter (fun v=>v∉C ∧ v∉D) =
      (A.filter (fun v=>v∉cut ∧ v∉side)).image f := by
    rw [Finset.filter_image]
    congr 1
    apply Finset.filter_congr
    intro v hv
    simp only [hcut hv,hside]
  have himage : cut.image f⊆budget := by
    intro v hv
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hv
    exact hbudget x (hsub hx) ((hcut (hsub hx)).mp hx)
  refine ⟨cut,side,hsub,?_,?_,?_,?_⟩
  · have he : (cut.image f).card=cut.card := Finset.card_image_of_injOn (hinj.mono hsub)
    rw [←he]
    exact (Finset.card_le_card himage).trans hcost
  · rw [hfirst,Finset.card_image_of_injOn (hinj.mono (Finset.filter_subset _ _)),hcard] at h₁
    exact h₁
  · rw [hsecond,Finset.card_image_of_injOn (hinj.mono (Finset.filter_subset _ _)),hcard] at h₂
    exact h₂
  · intro v hv w hw hvC hwC he
    rw [hside,hside]
    rcases hmap v hv w hw he with h|h
    · rw [h]
    · exact hsep (f v) (f w) (fun h=>hvC ((hcut hv).mpr h)) (fun h=>hwC ((hcut hw).mpr h)) h
end TorsionFreeZeroDivisors.CutTransfer

namespace TorsionFreeZeroDivisors.PlanarMap
open scoped Classical
open SimpleGraph
variable {V : Type} [Fintype V] {G : SimpleGraph V}

/-- Root-saving radius separation after literal connected lower-ball
contraction. Only vertices of `active` are charged or retained. -/
theorem Model.annular_separator (M : Model G) (hc : G.Connected) (root : V)
    (lo hi : ℕ) (active : Finset V)
    (hA : ∀ v∈active,lo<G.dist v root ∧ G.dist v root≤hi) :
    ∃ cut side : Finset V,cut⊆active ∧ cut.card≤2*(hi-lo) ∧
      3*(active.filter (fun v=>v∉cut ∧ v∈side)).card≤2*active.card ∧
      3*(active.filter (fun v=>v∉cut ∧ v∉side)).card≤2*active.card ∧
      ∀ v∈active,∀ w∈active,v∉cut→w∉cut→G.Adj v w→(v∈side↔w∈side) := by
  let S := GraphBall.vertices G root hi
  let H := G.induce S
  let r : S := GraphBall.rootVertex G root hi
  have hH : H.Connected := GraphBall.connected G hc root hi
  let B := GraphBall.vertices H r lo
  let J := (M.induced S).contract (GraphBall.connected H hH r lo)
  let q := J.quotient
  have hJ : J.graph.Connected := GraphQuotient.connected H J.graph q J.adj J.surjective hH
  have hcollapse (v : S) (hv : H.dist v r≤lo) : q v=q r :=
    (J.eq_iff v r).mpr (Or.inr ⟨hv,by change H.dist r r≤lo;simp only [SimpleGraph.dist_self];omega⟩)
  have hdist (v : S) : J.graph.dist (q v) (q r)≤G.dist v.val root-lo := by
    have h := GraphQuotient.distance_sub H J.graph q J.adj hH hJ r lo hcollapse v
    have he : H.dist v r=G.dist v.val root := GraphBall.dist_root G hc root hi v
    rwa [he] at h
  have hr (w : J.Vertex) : J.graph.dist (q r) w≤hi-lo := by
    obtain ⟨v,rfl⟩ := J.surjective w
    rw [SimpleGraph.dist_comm]
    exact (hdist v).trans (Nat.sub_le_sub_right v.property lo)
  let f : V→J.Vertex := fun v=>if hv:v∈S then q ⟨v,hv⟩ else q r
  have hf (v : V) (hv : v∈S) : f v=q ⟨v,hv⟩ := dite_eq_left hv
  have hAS {v : V} (hv : v∈active) : v∈S := (hA v hv).2
  have hout (v : V) (hv : v∈active) : (⟨v,hAS hv⟩ : S)∉B := by
    change ¬H.dist ⟨v,hAS hv⟩ r≤lo
    rw [GraphBall.dist_root G hc root hi]
    exact Nat.not_le.mpr (hA v hv).1
  have hinj : Set.InjOn f active := by
    intro v hv w hw he
    rw [hf v (hAS hv),hf w (hAS hw)] at he
    rcases (J.eq_iff _ _).mp he with he|he
    · exact congrArg Subtype.val he
    · exact (hout v hv he.1).elim
  have hroot (v : V) (hv : v∈active) : f v≠q r := by
    intro he
    rw [hf v (hAS hv)] at he
    rcases (J.eq_iff _ _).mp he with he|he
    · have hd : H.dist (⟨v,hAS hv⟩ : S) r=0 := by rw [he,SimpleGraph.dist_self]
      have hh : (⟨v,hAS hv⟩ : S)∈B := by change H.dist _ r≤lo;omega
      exact hout v hv hh
    · exact hout v hv he.1
  have hmap : ∀ v∈active,∀ w∈active,G.Adj v w→f v=f w ∨ J.graph.Adj (f v) (f w) := by
    intro v hv w hw he
    rw [hf v (hAS hv),hf w (hAS hw)]
    exact J.adj ⟨v,hAS hv⟩ ⟨w,hAS hw⟩ he
  obtain ⟨C,D,_,_,hCe,h₁,h₂,hsep⟩ := J.model.radius_separator hJ (q r) (hi-lo) hr (active.image f)
  exact CutTransfer.pullback G J.graph active f hinj hmap C D (C.erase (q r)) (2*(hi-lo)) hCe
    (fun v hv h=>Finset.mem_erase.mpr ⟨hroot v hv,h⟩) h₁ h₂ hsep

/-- The uncontracted alternative, needed when the selected lower level is
negative. Its extra root vertex fits strictly within the level-gap budget. -/
theorem Model.ball_separator (M : Model G) (hc : G.Connected) (root : V)
    (hi : ℕ) (active : Finset V) (hA : ∀ v∈active,G.dist v root≤hi) :
    ∃ cut side : Finset V,cut⊆active ∧ cut.card≤2*hi+1 ∧
      3*(active.filter (fun v=>v∉cut ∧ v∈side)).card≤2*active.card ∧
      3*(active.filter (fun v=>v∉cut ∧ v∉side)).card≤2*active.card ∧
      ∀ v∈active,∀ w∈active,v∉cut→w∉cut→G.Adj v w→(v∈side↔w∈side) := by
  let S := GraphBall.vertices G root hi
  let : DecidableEq S := Classical.decEq S
  let H := G.induce S
  let r : S := GraphBall.rootVertex G root hi
  have hH : H.Connected := GraphBall.connected G hc root hi
  let f : V→S := fun v=>if hv:v∈S then ⟨v,hv⟩ else r
  have hf (v : V) (hv : v∈S) : f v=⟨v,hv⟩ := dite_eq_left hv
  have hinj : Set.InjOn f active := by
    intro v hv w hw he
    rw [hf v (hA v hv),hf w (hA w hw)] at he
    exact congrArg Subtype.val he
  have hmap : ∀ v∈active,∀ w∈active,G.Adj v w→f v=f w ∨ H.Adj (f v) (f w) := by
    intro v hv w hw he
    rw [hf v (hA v hv),hf w (hA w hw)]
    exact Or.inr he
  have hr (v : S) : H.dist r v≤hi := by
    rw [SimpleGraph.dist_comm,GraphBall.dist_root G hc root hi]
    exact v.property
  obtain ⟨C,D,_,hC,_,h₁,h₂,hsep⟩ := (M.induced S).radius_separator hH r hi hr (active.image f)
  exact CutTransfer.pullback G H active f hinj hmap C D C (2*hi+1) hC (fun _ _ h=>h) h₁ h₂ hsep

end TorsionFreeZeroDivisors.PlanarMap

/-!
Sharp level-selection arithmetic for the planar-separator dependency.  The
profile is the actual number of vertices on each integer BFS level.  No planar
separator is assumed or concluded here: the bounded-radius geometric step is
separate.
-/
namespace TorsionFreeZeroDivisors.SeparatorLevels
open scoped BigOperators

private theorem twice_sum_succ (h : ℕ) :
    (∑ k ∈ Finset.range h, 2*(k+1)) = h*(h+1) := by
  induction h with
  | zero => simp
  | succ h ih => rw [Finset.sum_range_succ,ih]; ring

/-- The exact discrete triangle under a minimum level cost. -/
theorem triangular_bound (m : ℕ) (c : ℕ → ℕ)
    (hc : ∀ k < m/2, m ≤ c k + 2*(k+1)) :
    m^2 ≤ 4*(∑ k ∈ Finset.range (m/2), c k) + 2*m := by
  have hs : (m/2)*m ≤ (∑ k ∈ Finset.range (m/2),c k)+(m/2)*(m/2+1) := by
    have hh := Finset.sum_le_sum (s:=Finset.range (m/2))
      (fun k hk => hc k (Finset.mem_range.mp hk))
    simpa only [Finset.sum_add_distrib,twice_sum_succ,Finset.sum_const,
      Finset.card_range,smul_eq_mul] using hh
  have hr := Nat.mod_add_div m 2
  have hr' := Nat.mod_lt m (by decide : 0<2)
  have : m%2=0 ∨ m%2=1 := by omega
  rcases this with he | he <;> rw [he] at hr <;> nlinarith

theorem exists_minimum (f : ℕ → ℕ) : ∃ k, ∀ j, f k ≤ f j := by
  obtain ⟨m,⟨k,hk⟩,hm⟩ := Nat.lt_wfRel.wf.has_min (Set.range f) ⟨f 0,0,rfl⟩
  refine ⟨k,fun j => ?_⟩
  have hh := hm (f j) ⟨j,rfl⟩
  change ¬ f j < m at hh
  rw [hk]
  omega

/-- A nonnegative integer profile with total mass at most `N` has two levels
whose combined width plus twice their separation is at most `sqrt(8*N)`.
The center level is counted only once in the mass estimate. -/
theorem select (a : ℤ → ℕ) (N : ℕ) (center : ℤ)
    (mass : ∀ s : Finset ℤ, ∑ z ∈ s,a z ≤ N) :
    ∃ kL kR : ℕ,
      (a (center-kL) + a (center+kR) + 2*(kL+kR) : ℝ) ≤
        2*Real.sqrt 2*Real.sqrt N := by
  classical
  obtain ⟨kL,hL⟩ := exists_minimum (fun k=>a (center-k)+2*k)
  obtain ⟨kR,hR⟩ := exists_minimum (fun k=>a (center+k)+2*k)
  let A := a (center-kL)+2*kL
  let B := a (center+kR)+2*kR
  have hA : A ≤ a center := by
    simpa only [sub_zero,Nat.cast_zero,mul_zero,add_zero] using hL 0
  have hB : B ≤ a center := by
    simpa only [add_zero,Nat.cast_zero,mul_zero] using hR 0
  have tA := triangular_bound A (fun k=>a (center-(k+1:ℕ)))
    (fun k _ => hL (k+1))
  have tB := triangular_bound B (fun k=>a (center+(k+1:ℕ)))
    (fun k _ => hR (k+1))
  let left := (Finset.range (A/2)).image (fun k:ℕ=>center-(k+1:ℕ))
  let right := (Finset.range (B/2)).image (fun k:ℕ=>center+(k+1:ℕ))
  have hl : ∀ z ∈ left,z<center := by
    intro z hz
    obtain ⟨k,_,rfl⟩ := Finset.mem_image.mp hz
    omega
  have hr : ∀ z ∈ right,center<z := by
    intro z hz
    obtain ⟨k,_,rfl⟩ := Finset.mem_image.mp hz
    omega
  have hlr : Disjoint left right := by
    apply Finset.disjoint_left.mpr
    intro z hzl hzr
    have := hl z hzl
    have := hr z hzr
    omega
  have hc : center ∉ left ∪ right := by
    intro hh
    rcases Finset.mem_union.mp hh with hh|hh
    · exact (lt_irrefl center) (hl center hh)
    · exact (lt_irrefl center) (hr center hh)
  have sal : ∑ z ∈ left,a z = ∑ k ∈ Finset.range (A/2),a (center-(k+1:ℕ)) := by
    apply Finset.sum_image
    intro x _ y _ he
    change center-(x+1:ℕ)=center-(y+1:ℕ) at he
    omega
  have sar : ∑ z ∈ right,a z = ∑ k ∈ Finset.range (B/2),a (center+(k+1:ℕ)) := by
    apply Finset.sum_image
    intro x _ y _ he
    change center+(x+1:ℕ)=center+(y+1:ℕ) at he
    omega
  have hmass := mass (insert center (left ∪ right))
  rw [Finset.sum_insert hc,Finset.sum_union hlr,sal,sar] at hmass
  have hs : A^2+B^2 ≤ 4*N := by nlinarith
  have hs' : (A:ℝ)^2+(B:ℝ)^2 ≤ 4*(N:ℝ) := by exact_mod_cast hs
  have hab : ((A:ℝ)+(B:ℝ))^2 ≤ 8*(N:ℝ) := by nlinarith [sq_nonneg ((A:ℝ)-B)]
  have sqn := Real.sq_sqrt (show (0:ℝ)≤N by positivity)
  have sq2 := Real.sq_sqrt (show (0:ℝ)≤2 by norm_num)
  have hp : (2*Real.sqrt 2*Real.sqrt N)^2=8*(N:ℝ) := by
    calc
      _ = 4*(Real.sqrt 2)^2*(Real.sqrt N)^2 := by ring
      _ = _ := by rw [sqn,sq2]; ring
  have hfinal : (A:ℝ)+B ≤ 2*Real.sqrt 2*Real.sqrt N := by
    apply (sq_le_sq₀ (by positivity) (by positivity)).mp
    rw [hp]
    exact hab
  refine ⟨kL,kR,?_⟩
  convert hfinal using 1
  dsimp [A,B]
  push_cast
  ring

end TorsionFreeZeroDivisors.SeparatorLevels

end

end OAI
