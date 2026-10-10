import OAI.Computability.MeanPayoff.FiniteIteration

namespace OAI

section

namespace MeanPayoff.TreeDevice.Certified
open BinaryData Code
local infixl:80 " ≫ₚ " => Code.comp
local infixr:70 " ⋏ₚ " => Code.pair

namespace Size
variable {α β : Type} [Encoding α] [Encoding β]
theorem fst (x : α×β) : treeSize (encode x.1)≤treeSize (encode x) := by
  change _≤treeSize (product encode encode x)
  simp only [product,treeSize_pair]
  omega
theorem snd (x : α×β) : treeSize (encode x.2)≤treeSize (encode x) := by
  change _≤treeSize (product encode encode x)
  simp only [product,treeSize_pair]
  omega
theorem mem {xs : List α} {x : α} (hx : x∈xs) : treeSize (encode x)≤treeSize (encode xs) := by
  induction xs with
  | nil => simp at hx
  | cons a xs ih =>
    change _≤treeSize (listTree encode (a::xs))
    rw [listTree,treeSize_pair]
    rcases List.mem_cons.mp hx with rfl | hx
    · omega
    · have := ih hx; change _≤treeSize (listTree encode xs) at this; omega
theorem length (xs : List α) : xs.length≤treeSize (encode xs) := by
  change _≤treeSize (listTree encode xs)
  rw [listTree_size]
  omega
end Size

namespace Array

def Bounded (xs : List W) (N : ℕ) : Prop := ∀ w∈xs, w.digits.length≤N

theorem bounded_size (xs : List W) : Bounded xs (treeSize (encode xs)) := by
  intro w hw
  exact (digits_le_wordSize w).trans (Size.mem hw)

theorem size_bound {xs : List W} {N : ℕ} (h : Bounded xs N) :
    treeSize (encode xs)≤xs.length*(4*N+6)+1 := by
  induction xs with
  | nil => change 1≤0*(4*N+6)+1; omega
  | cons w ws ih =>
    have hw := wordSize_bound w
    have hn := h w (by simp)
    have ht := ih (fun v hv => h v (by simp [hv]))
    change treeSize (listTree wordData (w::ws))≤_
    rw [listTree,treeSize_pair,List.length_cons]
    change treeSize (listTree wordData ws)≤_ at ht
    nlinarith

theorem bounded_zip {xs ys : List W} {N : ℕ} (hx : Bounded xs N) (hy : Bounded ys N)
    (f : Code (W×W) W) (hf : ∀ z, f z=z.1 ∨ f z=z.2) :
    Bounded (zip zero zero f (xs,ys)) N := by
  change Bounded (Zip.zip f.eval zero xs ys) N
  induction xs generalizing ys with
  | nil => simp [Zip.zip,Bounded]
  | cons a as ih =>
    cases ys with
    | nil =>
      simp only [Zip.zip,List.headD_nil,List.tail_nil]
      intro w hw
      rcases List.mem_cons.mp hw with rfl | hw
      · rcases hf (a,zero) with he | he
        · rw [he]; exact hx a (by simp)
        · rw [he]; exact Nat.zero_le _
      · exact ih (fun w hw => hx w (by simp [hw])) (ys:=[]) (by simp [Bounded]) w hw
    | cons b bs =>
      simp only [Zip.zip,List.headD_cons,List.tail_cons]
      intro w hw
      rcases List.mem_cons.mp hw with rfl | hw
      · rcases hf (a,b) with he | he
        · rw [he]; exact hx a (by simp)
        · rw [he]; exact hy b (by simp)
      · exact ih (fun w hw => hx w (by simp [hw])) (ys:=bs)
          (fun w hw => hy w (by simp [hw])) w hw

theorem zip_length {α β γ : Type} (f : α×β→γ) (b : β) (xs : List α) (ys : List β) :
    (Zip.zip f b xs ys).length=xs.length := by
  induction xs generalizing ys with
  | nil => rfl
  | cons a as ih => cases ys <;> simp [Zip.zip,ih]
end Array

namespace RawBasic
abbrev Arena := List Graph.Vertex
abbrev Env := Arena × RawBox.Data
abbrev Acc := Env × List W

noncomputable def graph : Code (List W × Arena) (List W) :=
  ⟨fun z => z.2.map (fun v => Graph.vertex (z.1,v)),Graph.device,Graph.polynomial⟩
noncomputable def next : Code Acc (List W) :=
  ((fst ≫ₚ snd) ⋏ₚ ((snd ⋏ₚ (fst ≫ₚ fst)) ≫ₚ graph)) ≫ₚ RawBox.clip
noncomputable def advance : Code (Acc × Unit) Acc :=
  (fst ≫ₚ fst) ⋏ₚ (fst ≫ₚ next)

def ArenaBounded (g : Arena) (N : ℕ) : Prop :=
  ∀ v∈g, ∀ e∈v.2.1::v.2.2, e.2.digits.length≤N

theorem arenaBounded_size (g : Arena) : ArenaBounded g (treeSize (encode g)) := by
  intro v hv e he
  have hg := Size.mem hv
  have hv' := Size.snd v
  have he' : treeSize (encode e)≤treeSize (encode v.2) := by
    rcases List.mem_cons.mp he with rfl | he
    · exact Size.fst _
    · exact (Size.mem he).trans (Size.snd _)
  exact (digits_le_wordSize e.2).trans ((Size.snd e).trans (he'.trans (hv'.trans hg)))

theorem lookup_bound {xs : List W} {N : ℕ} (h : Array.Bounded xs N) (c : Count) :
    (Graph.lookup (xs,c)).digits.length≤N := by
  unfold Graph.lookup
  generalize hd : xs.drop c.length=ys
  cases ys with
  | nil => exact Nat.zero_le _
  | cons w ws =>
    apply h
    have hh : w∈xs.drop c.length := by rw [hd]; simp
    exact List.mem_of_mem_drop hh

theorem vertex_bound {xs : List W} {P Q : ℕ} (h : Array.Bounded xs P) (v : Graph.Vertex)
    (hv : ∀ e∈v.2.1::v.2.2, e.2.digits.length≤Q) :
    (Graph.vertex (xs,v)).digits.length≤P+Q+1 := by
  have he (e : Graph.Edge) (he : e∈v.2.1::v.2.2) :
      (Add.sumPair (Graph.edgePair (xs,e))).digits.length≤P+Q+1 := by
    have hp := lookup_bound h e.1
    have hq := hv e he
    change (Word.add (e.2,Graph.lookup (xs,e.1))).digits.length≤_
    rw [Word.add_length]
    omega
  have hm (f : W×W→W) (hf : ∀ z, f z=z.1 ∨ f z=z.2) :
      (Fold.fold f (Add.sumPair (Graph.batch (xs,v.2)).1)
        ((Graph.batch (xs,v.2)).2.map Add.sumPair)).digits.length≤P+Q+1 := by
    have H := EdgeScan.fold_mem f hf (Add.sumPair (Graph.batch (xs,v.2)).1)
      ((Graph.batch (xs,v.2)).2.map Add.sumPair)
    rcases List.mem_cons.mp H with hh | hh
    · rw [hh]; exact he v.2.1 (by simp)
    · obtain ⟨e,he',hh⟩ := List.mem_map.mp hh
      obtain ⟨e,hem,rfl⟩ := List.mem_map.mp he'
      rw [←hh]
      exact he e (List.mem_cons_of_mem _ hem)
  unfold Graph.vertex
  split
  · exact hm Order.high EdgeScan.high_mem
  · exact hm Order.low EdgeScan.low_mem

theorem graph_bound {xs : List W} {g : Arena} {P Q : ℕ}
    (h : Array.Bounded xs P) (hg : ArenaBounded g Q) :
    Array.Bounded (graph (xs,g)) (P+Q+1) := by
  intro w hw
  obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hw
  exact vertex_bound h v (hg v hv)

theorem clip_bound {b : RawBox.Data} {xs : List W} {N : ℕ}
    (ha : Array.Bounded b.2.1 N) (hb : Array.Bounded b.2.2 N) (hx : Array.Bounded xs N) :
    Array.Bounded (RawBox.clip (b,xs)) N := by
  exact Array.bounded_zip hb (Array.bounded_zip ha hx Word.max EdgeScan.high_mem)
    Word.min EdgeScan.low_mem

theorem next_bound {e : Env} {xs : List W} {N k : ℕ}
    (hg : ArenaBounded e.1 N) (ha : Array.Bounded e.2.2.1 N) (hb : Array.Bounded e.2.2.2 N)
    (hx : Array.Bounded xs (N+k*(N+1))) :
    Array.Bounded (next (e,xs)) (N+(k+1)*(N+1)) := by
  apply clip_bound
  · intro w hw; have := ha w hw; omega
  · intro w hw; have := hb w hw; omega
  · have hh := graph_bound hx hg
    intro w hw
    have := hh w hw
    simp only [Nat.add_mul,Nat.one_mul]
    omega

theorem next_length (e : Env) (xs : List W) : (next (e,xs)).length=e.2.2.2.length :=
  Array.zip_length _ _ _ _

theorem fold_layout (e : Env) (xs : List W) (cs : Count) :
    (Fold.fold advance.eval (e,xs) cs).1=e ∧
    (Fold.fold advance.eval (e,xs) cs).2.length=if cs=[] then xs.length else e.2.2.2.length := by
  induction cs generalizing xs with
  | nil => simp [Fold.fold]
  | cons u cs ih =>
    change (Fold.fold advance.eval (e,next (e,xs)) cs).1=e ∧ _
    have hh := ih (next (e,xs))
    refine ⟨hh.1,?_⟩
    change (Fold.fold advance.eval (e,next (e,xs)) cs).2.length=_
    rw [hh.2,next_length]
    simp

theorem fold_bound (s : Acc) (cs : Count) (N : ℕ)
    (hg : ArenaBounded s.1.1 N) (ha : Array.Bounded s.1.2.2.1 N)
    (hb : Array.Bounded s.1.2.2.2 N) (hx : Array.Bounded s.2 N) :
    (Fold.fold advance.eval s cs).1=s.1 ∧
    (Fold.fold advance.eval s cs).2.length ≤ s.2.length+s.1.2.2.2.length ∧
    Array.Bounded (Fold.fold advance.eval s cs).2 (N+cs.length*(N+1)) := by
  have main (e : Env) (xs : List W) (cs : Count) (k : ℕ)
      (hg : ArenaBounded e.1 N) (ha : Array.Bounded e.2.2.1 N) (hb : Array.Bounded e.2.2.2 N)
      (hx : Array.Bounded xs (N+k*(N+1))) :
      Array.Bounded (Fold.fold advance.eval (e,xs) cs).2 (N+(k+cs.length)*(N+1)) := by
    induction cs generalizing xs k with
    | nil => simpa [Fold.fold] using hx
    | cons u cs ih =>
      change Array.Bounded (Fold.fold advance.eval (e,next (e,xs)) cs).2 _
      have hh := ih (next (e,xs)) (k+1) (next_bound hg ha hb hx)
      simpa only [List.length_cons,show k+1+cs.length=k+(cs.length+1) by omega] using hh
  have hl := fold_layout s.1 s.2 cs
  refine ⟨hl.1,?_,?_⟩
  · rw [hl.2]; split <;> omega
  · simpa using main s.1 s.2 cs 0 hg ha hb (by simpa using hx)

theorem prefix_size (s : Acc) (cs : Count) (k : ℕ) (hk : k≤cs.length) :
    treeSize (encode (Fold.fold advance.eval s (cs.take k))) ≤
      50*(treeSize (encode (s,cs))+1)^3 := by
  let N := treeSize (encode (s,cs))+1
  have hs : treeSize (encode s)≤N := (Size.fst (s,cs)).trans (Nat.le_succ _)
  have he : treeSize (encode s.1)≤N := (Size.fst s).trans hs
  have hx : treeSize (encode s.2)≤N := (Size.snd s).trans hs
  have hg : treeSize (encode s.1.1)≤N := (Size.fst s.1).trans he
  have hb : treeSize (encode s.1.2)≤N := (Size.snd s.1).trans he
  have hab : treeSize (encode s.1.2.2)≤N := (Size.snd s.1.2).trans hb
  have ha : treeSize (encode s.1.2.2.1)≤N := (Size.fst s.1.2.2).trans hab
  have hb' : treeSize (encode s.1.2.2.2)≤N := (Size.snd s.1.2.2).trans hab
  have hl : (cs.take k).length≤N :=
    (List.length_take_le _ _).trans (hk.trans ((Size.length cs).trans ((Size.snd (s,cs)).trans (Nat.le_succ _))))
  have hh := fold_bound s (cs.take k) N
    (fun v hv e he => (arenaBounded_size _ v hv e he).trans hg)
    (fun w hw => (Array.bounded_size _ w hw).trans ha)
    (fun w hw => (Array.bounded_size _ w hw).trans hb')
    (fun w hw => (Array.bounded_size _ w hw).trans hx)
  have ho := Array.size_bound hh.2.2
  have hn : (Fold.fold advance.eval s (cs.take k)).2.length≤2*N := by
    have hx' := (Size.length s.2).trans hx
    have hb'' := (Size.length s.1.2.2.2).trans hb'
    omega
  have hm : N+(cs.take k).length*(N+1)≤N+N*(N+1) := by gcongr
  have ho' : treeSize (encode (Fold.fold advance.eval s (cs.take k)).2) ≤
      2*N*(4*(N+N*(N+1))+6)+1 := by
    apply ho.trans
    gcongr
  change treeSize (product encode encode (Fold.fold advance.eval s (cs.take k)))≤50*N^3
  rw [product,treeSize_pair,hh.1]
  have hpos : 1≤N := Nat.le_add_left _ _
  have h2 : N≤N*N := Nat.le_mul_self N
  have h3 : N*N≤N*N*N := Nat.mul_le_mul_right N h2
  nlinarith

noncomputable def loop : Code (Acc × Count) Acc := foldPrefix advance 50 3 prefix_size
noncomputable def solve : Code (Env × Count) (List W) :=
  (((fst ⋏ₚ (fst ≫ₚ snd ≫ₚ RawBox.lower)) ⋏ₚ snd) ≫ₚ loop) ≫ₚ snd

theorem next_rep (G : Game) {B : ℕ} {I : SolveBox G.n B} {b : RawBox.Data}
    (hb : RawBox.Rep I b) (w : Fin G.m→W) (hw : ∀ e, (w e).val=transformed G e)
    {v : Fin G.n→ℤ} {xs : List W} (hx : VectorRep v xs) :
    VectorRep (boxStep (operator G) I.a I.b v) (next ((Graph.codeVertices G w,b),xs)) := by
  apply RawBox.clip_rep hb
  obtain ⟨ws,rfl,hws⟩ := hx
  refine ⟨fun i => Graph.vertex (Graph.codePot ws,Graph.codeVertex G w i),?_,?_⟩
  · exact List.map_ofFn
  · intro i
    rw [Graph.codeVertex_exact G ws w hw]
    congr 2
    exact funext hws

theorem loop_rep (G : Game) {B : ℕ} {I : SolveBox G.n B} {b : RawBox.Data}
    (hb : RawBox.Rep I b) (w : Fin G.m→W) (hw : ∀ e, (w e).val=transformed G e)
    {v : Fin G.n→ℤ} {xs : List W} (hx : VectorRep v xs) (cs : Count) :
    VectorRep ((boxStep (operator G) I.a I.b)^[cs.length] v)
      (loop (((Graph.codeVertices G w,b),xs),cs)).2 := by
  change VectorRep _ (Fold.fold advance.eval ((Graph.codeVertices G w,b),xs) cs).2
  induction cs generalizing v xs with
  | nil => exact hx
  | cons u cs ih =>
    change VectorRep _ (Fold.fold advance.eval ((Graph.codeVertices G w,b),next ((Graph.codeVertices G w,b),xs)) cs).2
    rw [List.length_cons,Function.iterate_succ_apply]
    exact ih (next_rep G hb w hw hx)

theorem solve_rep (G : Game) {B : ℕ} {I : SolveBox G.n B} {b : RawBox.Data}
    (hb : RawBox.Rep I b) (w : Fin G.m→W) (hw : ∀ e, (w e).val=transformed G e)
    (cs : Count) (hc : G.n*I.width≤cs.length) :
    VectorRep (I.exactVector G).val (solve ((Graph.codeVertices G w,b),cs)) := by
  have hh := loop_rep G hb w hw hb.lower cs
  rw [I.iterate_exact G cs.length hc] at hh
  exact hh
end RawBasic
end MeanPayoff.TreeDevice.Certified
end

end OAI
