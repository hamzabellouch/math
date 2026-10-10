import Mathlib
import OAI.Combinatorics.StripMass.SidePaths
import OAI.Combinatorics.StripMass.NorthMass

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip
noncomputable section
open scoped Classical BigOperators

 
def raiseTriangle (v : Triangle) : Triangle := (v.1,v.2.1+1,v.2.2)

lemma raiseTriangle_injective : Function.Injective raiseTriangle := by
  rintro ⟨i,j,b⟩ ⟨k,l,c⟩ h
  simp only [raiseTriangle,Prod.mk.injEq,Nat.add_right_cancel_iff] at h
  exact Prod.ext h.1 (Prod.ext h.2.1 h.2.2)

lemma adjacent_raise (v w : Triangle) :
    adjacent (raiseTriangle v) (raiseTriangle w) ↔ adjacent v w := by
  simp only [adjacent,upDownAdjacent,raiseTriangle,Nat.add_right_cancel_iff]

lemma PathBetween.raise {H : ℕ} {a b : Triangle} {p : List Triangle}
    (hp : PathBetween H a b p) :
    PathBetween (H+1) (raiseTriangle a) (raiseTriangle b) (p.map raiseTriangle) := by
  refine ⟨?_,?_,hp.2.2.1.map raiseTriangle_injective,?_,?_⟩
  · rw [List.head?_map,hp.1]; rfl
  · rw [List.getLast?_map,hp.2.1]; rfl
  · exact (List.isChain_map _).mpr (hp.2.2.2.1.imp (fun v w h=>(adjacent_raise v w).mpr h))
  · intro v hv
    obtain ⟨w,hw,rfl⟩:=List.mem_map.mp hv
    exact Nat.succ_lt_succ (hp.2.2.2.2 w hw)

lemma PathBetween.prepend_vertex {H : ℕ} {a b v : Triangle} {p : List Triangle}
    (hp : PathBetween H a b p) (hv : v.2.1<H) (hn : v∉p) (hva : adjacent v a) :
    PathBetween H v b (v::p) := by
  refine ⟨rfl,?_,List.nodup_cons.mpr ⟨hn,hp.2.2.1⟩,?_,?_⟩
  · have hne : p≠[] := by intro h; simpa only [h,List.getLast?_nil,reduceCtorEq] using hp.2.1
    simp only [List.getLast?_cons,hp.2.1,Option.getD_some]
  · apply List.isChain_cons.mpr
    refine ⟨?_,hp.2.2.2.1⟩
    intro y hy
    have he : a=y := by simpa only [hp.1,Option.mem_some_iff] using hy
    exact he ▸ hva
  · intro w hw
    rcases List.mem_cons.mp hw with rfl|hw
    · exact hv
    · exact hp.2.2.2.2 w hw

 

def prepareBridge (p : List Triangle) : List Triangle :=
  up 0 0 :: down 0 0 :: p.map raiseTriangle

lemma prepareBridge_injective : Function.Injective prepareBridge := by
  intro p q h
  exact List.map_injective_iff.mpr raiseTriangle_injective ((List.cons.inj (List.cons.inj h).2).2)

lemma prepareBridge_spec {H : ℕ} (hH : 1≤H) {k : ℤ} {p : List Triangle}
    (hp : IsPath H (down k (H-1)) p) :
    IsPath (H+1) (down k H) (prepareBridge p) := by
  have hh := (show PathBetween H (up 0 0) (down k (H-1)) p from hp).raise
  have he : raiseTriangle (down k (H-1))=down k H := by
    have he : H-1+1=H := by omega
    simp only [raiseTriangle,down,he]
  rw [he] at hh
  have hn (b : Bool) : (0,0,b) ∉ p.map raiseTriangle := by
    intro h
    obtain ⟨v,_,hv⟩:=List.mem_map.mp h
    have hx:=congrArg (fun x : Triangle=>x.2.1) hv
    change v.2.1+1=0 at hx
    omega
  have hu : up (0:ℤ) 0 ≠ down 0 0 := by decide
  exact (hh.prepend_vertex (by change 0<H+1; omega) (hn false)
    (by simp [adjacent,upDownAdjacent,raiseTriangle,up])).prepend_vertex
      (by change 0<H+1; omega) (by simpa only [List.mem_cons,up,down,Prod.mk.injEq,Bool.true_eq_false,and_false,
        false_or] using (hn true))
      (by simp [adjacent,upDownAdjacent,up])

@[simp] lemma prepareBridge_length (p : List Triangle) :
    (prepareBridge p).length=p.length+2 := by simp [prepareBridge]

lemma adjacent_up_other_column {i : ℤ} {j : ℕ} {w : Triangle}
    (h : adjacent (up i j) w) (hne : w.1≠i) : w=down (i-1) j := by
  rcases w with ⟨k,l,b⟩
  cases b <;> simp [adjacent,upDownAdjacent,up,down] at h ⊢
  all_goals omega

 

lemma exists_rightmost_down {H : ℕ} {k : ℤ} {p : List Triangle}
    (hp : IsPath H (down k (H-1)) p) (hzero : down 0 0∈p) :
    ∃ M : ℤ, ∃ j : ℕ, down M j∈p ∧ 0≤M ∧ ∀ v∈p,v.1≤M := by
  let F:=p.toFinset.image Prod.fst
  have h0 : (0:ℤ)∈F := Finset.mem_image.mpr ⟨down 0 0,List.mem_toFinset.mpr hzero,rfl⟩
  have hne : F.Nonempty:=⟨0,h0⟩
  let M:=F.max' hne
  have hM (v : Triangle) (hv : v∈p) : v.1≤M :=
    Finset.le_max' _ _ (Finset.mem_image.mpr ⟨v,List.mem_toFinset.mpr hv,rfl⟩)
  have hM0 : 0≤M := Finset.le_max' F 0 h0
  by_contra hh
  have hn (j : ℕ) : down M j∉p := by
    intro h; exact hh ⟨M,j,h,hM0,hM⟩
  have hMp : ∃v∈p,v.1=M := by
    obtain ⟨v,hv,he⟩:=Finset.mem_image.mp (Finset.max'_mem F hne)
    exact ⟨v,List.mem_toFinset.mp hv,he⟩
  obtain ⟨⟨i,j,b⟩,hv,hi⟩:=hMp
  change i=M at hi
  subst i
  cases b with
  | false => exact hn j hv
  | true =>
    obtain ⟨a,ha,hv⟩:=List.getElem_of_mem hv
    have hfirst : p[0]'(by omega)=up 0 0 := by
      simpa only [List.head?_eq_getElem?,List.getElem?_eq_getElem (by omega : 0<p.length),
        Option.some.injEq] using hp.1
    have hlast : p[p.length-1]'(by omega)=down k (H-1) := by
      simpa only [List.getLast?_eq_getElem?,List.getElem?_eq_getElem (by omega : p.length-1<p.length),
        Option.some.injEq] using hp.2.1
    have haz : a≠0 := by
      intro hz; subst a
      have he := hfirst.symm.trans hv
      have hcol:=congrArg Prod.fst he
      change 0=M at hcol
      exact hn 0 (hcol ▸ hzero)
    have hat : a+1<p.length := by
      by_contra ht
      have he : a=p.length-1 := by omega
      have hb := hlast.symm.trans (by simpa only [he] using hv)
      have hb':=congrArg (fun v : Triangle=>v.2.2) hb
      contradiction
    have ha' : a-1+1=a := by omega
    have hc:=List.isChain_iff_getElem.mp hp.2.2.2.1
    have hprev : adjacent (up M j) p[a-1] := by
      have he:=adjacent_symmetric.symm _ _ (hc (a-1) (by omega))
      simpa only [ha',hv,up] using he
    have hnext : adjacent (up M j) p[a+1] := by simpa only [hv,up] using hc a hat
    have other {w : Triangle} (hw : w∈p) (had : adjacent (up M j) w) : w=down (M-1) j := by
      apply adjacent_up_other_column had
      intro he
      have hb : w.2.2=false := by
        rcases had with h|h
        · exact h.2.1
        · exact (by have he := h.2.1; change true=false at he; contradiction)
      have hw' : w=down M w.2.1 := by
        rcases w with ⟨i,l,b⟩
        exact Prod.ext he (Prod.ext rfl hb)
      exact hn w.2.1 (hw' ▸ hw)
    have he := (other (List.getElem_mem _) hprev).trans (other (List.getElem_mem _) hnext).symm
    have hi := hp.2.2.1.getElem_inj_iff.mp he
    omega

 
def ladderVertex (i : ℤ) (r : ℕ) : Triangle := (i,r/2,r%2=0)

lemma ladderVertex_injective (i : ℤ) : Function.Injective (ladderVertex i) := by
  intro a b h
  have hr:=congrArg (fun v : Triangle=>v.2.1) h
  have hp:=congrArg (fun v : Triangle=>v.2.2) h
  simp only [ladderVertex] at hr hp
  have ha:=Nat.mod_lt a (by omega : 0<2)
  have hb:=Nat.mod_lt b (by omega : 0<2)
  simp only [decide_eq_decide] at hp
  omega

lemma ladderVertex_adjacent (i : ℤ) (r : ℕ) :
    adjacent (ladderVertex i r) (ladderVertex i (r+1)) := by
  have hmod:=Nat.mod_lt r (by omega : 0<2)
  by_cases he : r%2=0
  · have he' : (r+1)%2≠0 := by omega
    have hd : (r+1)/2=r/2 := by omega
    simp [ladderVertex,he,he',hd,adjacent,upDownAdjacent]
  · have he' : (r+1)%2=0 := by omega
    have hd : (r+1)/2=r/2+1 := by omega
    simp [ladderVertex,he,he',hd,adjacent,upDownAdjacent]

lemma exists_column_connector (H : ℕ) (i : ℤ) (j l : ℕ) (hj : j<H) (hl : l<H) :
    ∃ p : List Triangle, PathBetween H (up i j) (down i l) p ∧
      (∀ v∈p,v.1=i) ∧ p.length≤2*H := by
  let a : Fin (2*H):=⟨2*j,by omega⟩
  let b : Fin (2*H):=⟨2*l+1,by omega⟩
  obtain ⟨w,hw⟩:=((SimpleGraph.pathGraph_preconnected (2*H)) a b).exists_isPath
  let f : Fin (2*H)→Triangle:=fun r=>ladderVertex i r.val
  have hf : Function.Injective f := (ladderVertex_injective i).comp Fin.val_injective
  refine ⟨w.support.map f,⟨?_,?_,hw.support_nodup.map hf,?_,?_⟩,?_,?_⟩
  · simp only [List.head?_map,List.head?_eq_some_head w.support_ne_nil,w.head_support,Option.map_some]
    simp [f,a,ladderVertex,up]
  · simp only [List.getLast?_map,List.getLast?_eq_some_getLast w.support_ne_nil,w.getLast_support,Option.map_some]
    simp only [f,b,ladderVertex,down,Option.some.injEq,Prod.mk.injEq,true_and]
    have he : (2*l+1)/2=l := by omega
    have hm : (2*l+1)%2≠0 := by omega
    simp only [he,hm,decide_false,and_self]
  · apply (List.isChain_map _).mpr
    apply w.isChain_adj_support.imp
    intro v w h
    have hh:=SimpleGraph.pathGraph_adj.mp h
    rcases hh with hh|hh
    · change adjacent (ladderVertex i v.val) (ladderVertex i w.val)
      rw [←hh]
      exact ladderVertex_adjacent i _
    · change adjacent (ladderVertex i v.val) (ladderVertex i w.val)
      rw [←hh]
      exact adjacent_symmetric.symm _ _ (ladderVertex_adjacent i _)
  · intro v hv
    obtain ⟨r,_,rfl⟩:=List.mem_map.mp hv
    change r.val/2<H
    have :=r.isLt
    omega
  · intro v hv
    obtain ⟨r,_,rfl⟩:=List.mem_map.mp hv
    rfl
  · rw [List.length_map]
    have := List.Nodup.length_le_card hw.support_nodup
    simpa only [Fintype.card_fin] using this


 

 


lemma PathBetween.append {H : ℕ} {a b c d : Triangle} {p q : List Triangle}
    (hp : PathBetween H a b p) (hq : PathBetween H c d q)
    (hd : List.Disjoint p q) (hbc : adjacent b c) :
    PathBetween H a d (p++q) := by
  refine ⟨?_,?_,List.nodup_append.mpr ⟨hp.2.2.1,hq.2.2.1,?_⟩,?_,?_⟩
  · rw [List.head?_append,hp.1]; rfl
  · rw [List.getLast?_append,hq.2.1]; rfl
  · intro x hx y hy he
    exact List.disjoint_left.mp hd hx (he ▸ hy)
  · apply List.isChain_append.mpr
    refine ⟨hp.2.2.2.1,hq.2.2.2.1,?_⟩
    intro x hx y hy
    have he : b=x := by simpa only [hp.2.1,Option.mem_some_iff] using hx
    have he' : c=y := by simpa only [hq.1,Option.mem_some_iff] using hy
    exact he ▸ he' ▸ hbc
  · intro v hv
    rcases List.mem_append.mp hv with hv|hv
    · exact hp.2.2.2.2 v hv
    · exact hq.2.2.2.2 v hv

lemma PathBetween.split {H : ℕ} {a b v : Triangle} {p : List Triangle}
    (hp : PathBetween H a b p) (hv : v∈p) :
    ∃ r t, PathBetween H a v r ∧ PathBetween H v b t ∧
      p=r++t.tail ∧ (∀w∈r,w∈p) ∧ (∀w∈t,w∈p) := by
  obtain ⟨x,y,rfl⟩:=List.append_of_mem hv
  have hpre : x++[v] <+: x++v::y := ⟨y,by simp only [List.append_assoc,List.singleton_append]⟩
  have hsuf : v::y <:+ x++v::y := List.suffix_append _ _
  have hmem₁ : ∀w∈x++[v],w∈x++v::y:=fun _ h=>hpre.sublist.subset h
  have hmem₂ : ∀w∈v::y,w∈x++v::y:=fun _ h=>hsuf.sublist.subset h
  refine ⟨x++[v],v::y,⟨?_,by simp,hp.2.2.1.sublist hpre.sublist,
    hp.2.2.2.1.prefix hpre,fun w hw=>hp.2.2.2.2 w (hmem₁ w hw)⟩,
    ⟨rfl,?_,hp.2.2.1.sublist hsuf.sublist,hp.2.2.2.1.suffix hsuf,
      fun w hw=>hp.2.2.2.2 w (hmem₂ w hw)⟩,?_,hmem₁,hmem₂⟩
  · have he : (x++[v]).head?=(x++v::y).head? := by cases x <;> rfl
    exact he.trans hp.1
  · have he:=hp.2.1
    rw [List.getLast?_append_of_ne_nil x (by simp)] at he
    exact he
  · simp only [List.tail_cons,List.append_assoc,List.singleton_append]

 

structure BridgeCut (H : ℕ) (k : ℤ) (p : List Triangle) where
  column : ℤ
  row : ℕ
  left : List Triangle
  right : List Triangle
  column_nonneg : 0≤column
  row_lt : row<H
  left_path : PathBetween H (up 0 0) (down column row) left
  right_path : PathBetween H (down column row) (down k (H-1)) right
  left_le : ∀v∈left,v.1≤column
  right_le : ∀v∈right,v.1≤column
  reconstruct : p=left++right.tail

lemma exists_bridgeCut {H : ℕ} {k : ℤ} {p : List Triangle}
    (hp : IsPath H (down k (H-1)) p) (hzero : down 0 0∈p) :
    Nonempty (BridgeCut H k p) := by
  obtain ⟨M,j,hv,hM,hmax⟩:=exists_rightmost_down hp hzero
  obtain ⟨r,t,hr,ht,he,hm₁,hm₂⟩:=
    (show PathBetween H (up 0 0) (down k (H-1)) p from hp).split hv
  exact ⟨⟨M,j,r,t,hM,hp.2.2.2.2 _ hv,hr,ht,
    fun v hv=>hmax v (hm₁ v hv),fun v hv=>hmax v (hm₂ v hv),he⟩⟩

namespace BridgeCut
section TraceRealizations
variable {H : ℕ} {k : ℤ} {p : List Triangle}

lemma height_pos (D : BridgeCut H k p) : 0<H := by have :=D.row_lt; omega

lemma end_le (D : BridgeCut H k p) : k≤D.column :=
  D.right_le _ (List.mem_of_mem_getLast? (by rw [D.right_path.2.1]; rfl))

lemma right_ne_nil (D : BridgeCut H k p) : D.right≠[] := by
  intro he
  have hh:=D.right_path.1
  rw [he] at hh
  contradiction

 

def move (D : BridgeCut H k p) (v : Triangle) : Triangle :=
  translateTriangle (2*D.column+2) (rotateTriangle H v)

lemma move_col (D : BridgeCut H k p) {v : Triangle} (hv : v.2.1<H) :
    (D.move v).1=2*D.column+2-v.1 := by simp [move,translateTriangle,rotateTriangle,hv,sub_eq_add_neg]

lemma move_injective (D : BridgeCut H k p) : Function.Injective D.move :=
  (translateTriangle_injective _).comp (rotateTriangle_involutive H).injective

lemma moved_path (D : BridgeCut H k p) :
    PathBetween H (up (D.column+2) (H-1-D.row)) (up (2*D.column+2-k) 0)
      (D.right.map D.move) := by
  change PathBetween H _ _ (D.right.map (fun v=>translateTriangle (2*D.column+2) (rotateTriangle H v)))
  have hh:=(D.right_path.rotate).translate (2*D.column+2)
  simpa only [rotateTriangle_down _ _ D.row_lt,
    rotateTriangle_down _ _ (by have :=D.height_pos; omega : H-1<H),
    Nat.sub_self,translateTriangle_up,List.map_map,Function.comp_def,
    show 2*D.column+2+-D.column=D.column+2 by ring,
    show 2*D.column+2+-k=2*D.column+2-k by ring,move] using hh

lemma moved_ge (D : BridgeCut H k p) : ∀v∈D.right.map D.move,D.column+2≤v.1 := by
  intro v hv
  obtain ⟨w,hw,rfl⟩:=List.mem_map.mp hv
  rw [D.move_col (D.right_path.2.2.2.2 w hw)]
  have :=D.right_le w hw
  omega

lemma connector_exists (D : BridgeCut H k p) :
    ∃ q : List Triangle, PathBetween H (up (D.column+1) D.row)
        (down (D.column+1) (H-1-D.row)) q ∧
      (∀v∈q,v.1=D.column+1) ∧ q.length≤2*H :=
  exists_column_connector H (D.column+1) D.row (H-1-D.row) D.row_lt
    (by have :=D.row_lt; omega)

def connector (D : BridgeCut H k p) : List Triangle := D.connector_exists.choose

lemma connector_spec (D : BridgeCut H k p) :
    PathBetween H (up (D.column+1) D.row) (down (D.column+1) (H-1-D.row)) D.connector ∧
      (∀v∈D.connector,v.1=D.column+1) ∧ D.connector.length≤2*H := D.connector_exists.choose_spec

 
def arch (D : BridgeCut H k p) : List Triangle := D.left++D.connector++D.right.map D.move

lemma arch_path (D : BridgeCut H k p) :
    IsPath H (up (2*D.column+2-k) 0) D.arch := by
  have hc:=D.connector_spec
  have hl : PathBetween H (up 0 0) (down (D.column+1) (H-1-D.row)) (D.left++D.connector) := by
    apply D.left_path.append hc.1
    · apply List.disjoint_left.mpr
      intro v hv hv'
      have h₁:=D.left_le v hv
      have h₂:=hc.2.1 v hv'
      omega
    · simp [adjacent,upDownAdjacent,up,down]
  apply hl.append D.moved_path
  · apply List.disjoint_left.mpr
    intro v hv hv'
    have hg:=D.moved_ge v hv'
    rcases List.mem_append.mp hv with hv|hv
    · have := D.left_le v hv; omega
    · have :=hc.2.1 v hv; omega
  · simp [adjacent,upDownAdjacent,up,down]
    omega

lemma arch_length (D : BridgeCut H k p) : D.arch.length≤p.length+(2*H+1) := by
  have he:=congrArg List.length D.reconstruct
  have hc:=D.connector_spec.2.2
  have hn : 0<D.right.length := List.length_pos_iff.mpr D.right_ne_nil
  simp only [List.length_append,List.length_tail] at he
  simp only [arch,List.length_append,List.length_map]
  omega

 

lemma arch_filter_left (D : BridgeCut H k p) :
    D.arch.filter (fun v=>decide (v.1≤D.column))=D.left := by
  have hl : D.left.filter (fun v=>decide (v.1≤D.column))=D.left :=
    List.filter_eq_self.mpr (fun v hv=>by simpa using D.left_le v hv)
  have hc : D.connector.filter (fun v=>decide (v.1≤D.column))=[] := by
    apply List.filter_eq_nil_iff.mpr
    intro v hv
    have :=D.connector_spec.2.1 v hv
    simp only [decide_eq_true_eq]
    omega
  have hr : (D.right.map D.move).filter (fun v=>decide (v.1≤D.column))=[] := by
    apply List.filter_eq_nil_iff.mpr
    intro v hv
    have :=D.moved_ge v hv
    simp only [decide_eq_true_eq]
    omega
  simp only [arch,List.filter_append,hl,hc,hr,List.append_nil]

lemma arch_filter_right (D : BridgeCut H k p) :
    D.arch.filter (fun v=>decide (D.column+2≤v.1))=D.right.map D.move := by
  have hl : D.left.filter (fun v=>decide (D.column+2≤v.1))=[] := by
    apply List.filter_eq_nil_iff.mpr
    intro v hv
    have :=D.left_le v hv
    simp only [decide_eq_true_eq]
    omega
  have hc : D.connector.filter (fun v=>decide (D.column+2≤v.1))=[] := by
    apply List.filter_eq_nil_iff.mpr
    intro v hv
    have :=D.connector_spec.2.1 v hv
    simp only [decide_eq_true_eq]
    omega
  have hr : (D.right.map D.move).filter (fun v=>decide (D.column+2≤v.1))=D.right.map D.move :=
    List.filter_eq_self.mpr (fun v hv=>by simpa using D.moved_ge v hv)
  simp only [arch,List.filter_append,hl,hc,hr,List.nil_append]

end TraceRealizations

 

 


lemma recover {H : ℕ} {k l : ℤ} {p q : List Triangle}
    (D : BridgeCut H k p) (E : BridgeCut H l q)
    (hcol : D.column=E.column) (ha : D.arch=E.arch) : p=q := by
  have hl : D.left=E.left := by
    rw [←D.arch_filter_left,ha,hcol,E.arch_filter_left]
  have hr : D.right.map D.move=E.right.map E.move := by
    rw [←D.arch_filter_right,ha,hcol,E.arch_filter_right]
  have he : E.move=D.move := by funext v; simp only [move,hcol]
  rw [he] at hr
  have hr' := List.map_injective_iff.mpr D.move_injective hr
  rw [D.reconstruct,E.reconstruct,hl,hr']
end BridgeCut

 
def BridgePath (N : ℕ) := {x : ℤ×List Triangle // IsPath N (down x.1 (N-1)) x.2}

namespace BridgePath
variable {N : ℕ}

def cut (hN : 1≤N) (x : BridgePath N) :
    BridgeCut (N+1) x.val.1 (prepareBridge x.val.2) := by
  apply Classical.choice
  apply exists_bridgeCut (by simpa only [Nat.add_sub_cancel] using prepareBridge_spec hN x.property)
  simp [prepareBridge]

 

def toCutArch (hN : 1≤N) (x : BridgePath N) : (ℕ×ℕ)×List Triangle :=
  let D:=x.cut hN
  ((D.column.toNat,(D.column+1-x.val.1).toNat),D.arch.map (translateTriangle (-D.column)))

lemma toCutArch_injective (hN : 1≤N) : Function.Injective (toCutArch hN) := by
  intro x y he
  have hm : (x.cut hN).column=(y.cut hN).column := by
    have hh:=congrArg (fun z : (ℕ×ℕ)×List Triangle=>z.1.1) he
    change (x.cut hN).column.toNat=(y.cut hN).column.toNat at hh
    have h₁:=(x.cut hN).column_nonneg
    have h₂:=(y.cut hN).column_nonneg
    omega
  have ha : (x.cut hN).arch=(y.cut hN).arch := by
    have hh:=congrArg Prod.snd he
    change (x.cut hN).arch.map (translateTriangle (-(x.cut hN).column))=
      (y.cut hN).arch.map (translateTriangle (-(y.cut hN).column)) at hh
    rw [hm] at hh
    exact List.map_injective_iff.mpr (translateTriangle_injective _) hh
  have hp := prepareBridge_injective ((x.cut hN).recover (y.cut hN) hm ha)
  apply Subtype.ext
  apply Prod.ext ?_ hp
  have hx:=x.property.2.1
  have hy:=y.property.2.1
  rw [hp,hy] at hx
  exact (congrArg Prod.fst (Option.some.inj hx)).symm

lemma toCutArch_path (hN : 1≤N) (x : BridgePath N) :
    PathBetween (N+1) (up (-((toCutArch hN x).1.1:ℤ)) 0)
      (up (((toCutArch hN x).1.2:ℤ)+1) 0) (toCutArch hN x).2 := by
  let D:=x.cut hN
  have hM : (D.column.toNat:ℤ)=D.column := Int.toNat_of_nonneg D.column_nonneg
  have he : ((D.column+1-x.val.1).toNat:ℤ)=D.column+1-x.val.1 :=
    Int.toNat_of_nonneg (by have :=D.end_le; omega)
  have hh:=(show PathBetween (N+1) (up 0 0) (up (2*D.column+2-x.val.1) 0) D.arch from
    D.arch_path).translate (-D.column)
  change PathBetween _ (up (-(D.column.toNat:ℤ)) 0)
    (up (((D.column+1-x.val.1).toNat:ℤ)+1) 0) (D.arch.map (translateTriangle (-D.column)))
  simpa only [translateTriangle_up,hM,he,add_zero,
    show -D.column+(2*D.column+2-x.val.1)=D.column+1-x.val.1+1 by ring] using hh

lemma rho_le_one : rho≤1 := by nlinarith [rho_pos,rho_sq_lt_one]

lemma toCutArch_weight_bound (hN : 1≤N) (x : BridgePath N) :
    rho^(2*(N+1)+3)*rho^x.val.2.length ≤ cutArchWeight (N+1) (toCutArch hN x) := by
  have hp:=toCutArch_path hN x
  rw [cutArchWeight,betweenArchWeight,ite_eq_left ⟨by omega,hp⟩,←pow_add]
  apply pow_le_pow_of_le_one rho_pos.le rho_le_one
  have hl:=(x.cut hN).arch_length
  simp only [prepareBridge_length] at hl
  change ((x.cut hN).arch.map _).length≤_
  rw [List.length_map]
  omega

 

theorem summable_weight (hN : 1≤N) : Summable (fun x : BridgePath N=>rho^x.val.2.length) := by
  have ht := (cutArchWeight_summable_iff (N+1) (archWeight_summable (by omega))).mpr
    (moment_summable (by omega))
  have hs:=ht.comp_injective (toCutArch_injective hN)
  have hb : Summable (fun x : BridgePath N=>rho^(2*(N+1)+3)*rho^x.val.2.length) :=
    Summable.of_nonneg_of_le (fun _=>by positivity [rho_pos]) (toCutArch_weight_bound hN) hs
  exact (summable_mul_left_iff (pow_ne_zero _ rho_pos.ne')).mp hb
end BridgePath

theorem summable_bridgeWeight {N : ℕ} (hN : 1≤N) :
    Summable (fun x : ℤ×List Triangle=>bridgeWeight N x.1 x.2) := by
  have hh:= (summable_subtype_iff_indicator
    (f:=fun x : ℤ×List Triangle=>rho^x.2.length)
    (s:={x : ℤ×List Triangle | IsPath N (down x.1 (N-1)) x.2})).mp
      (BridgePath.summable_weight hN)
  apply hh.congr
  intro x
  dsimp [Set.indicator]
  unfold bridgeWeight
  split_ifs <;> simp_all

 

theorem stripSumsFinite {N : ℕ} (hN : 1≤N) : StripSumsFinite N := by
  have hb:=(summable_prod_of_nonneg (fun x : ℤ×List Triangle=>bridgeWeight_nonneg N x.1 x.2)).mp
    (summable_bridgeWeight hN)
  exact ⟨archWeight_summable hN,hb.1,summable_K_of_moment (moment_summable hN),hb.2,moment_summable hN⟩

end
end CriticalStrip

end OAI
