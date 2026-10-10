import OAI.Computability.Superstring.ThreadSupport

namespace OAI

namespace Superstring.WalkCode
open BitCode Hierarchical
variable {α : Type}

abbrev Walk (α : Type) := List (List α)

def Edge (s t : List α) : Prop :=
  (∃ a, t = s ++ [a]) ∨ ∃ a, s = a :: t

def Valid (V : Set (List α)) (P : Walk α) : Prop :=
  P ≠ [] ∧ (∀ w ∈ P, w ∈ V) ∧ P.IsChain Edge

def cost (P : Walk α) : ℕ :=
  (P.zip P.tail).countP (fun q => decide (q.1.length < q.2.length))

def join (P Q : Walk α) : Walk α := P ++ Q.tail

def Visits (P : Walk α) (w : List α) : Prop := w ∈ P

namespace Path

def points {V : Set (List α)} : {s t : List α} → Hierarchical.Path V s t → Walk α
  | _, _, .nil s _ => [s]
  | _, _, .up s a _ _ => [s,s ++ [a]]
  | _, _, .down a s _ _ => [a :: s,s]
  | _, _, .trans P Q => join (points P) (points Q)

end Path

@[simp] theorem join_cons (s : List α) (P : Walk α) (t : List α) (Q : Walk α) :
    join (s::P) (t::Q) = s :: (P ++ Q) := rfl

@[simp] theorem cost_nil : cost ([] : Walk α) = 0 := rfl
@[simp] theorem cost_singleton (s : List α) : cost [s] = 0 := rfl
@[simp] theorem cost_cons_cons (s t : List α) (P : Walk α) :
    cost (s::t::P) = (if s.length < t.length then 1 else 0) + cost (t::P) := by
  simp only [cost, List.tail_cons, List.zip_cons_cons, List.countP_cons, decide_eq_true_eq]
  split <;> omega

@[simp] theorem cost_join (P Q : Walk α) (u : List α)
    (hp : P.getLast? = some u) (hq : Q.head? = some u) :
    cost (join P Q) = cost P + cost Q := by
  induction P with
  | nil => simp at hp
  | cons a P ih =>
    cases P with
    | nil =>
      have ha : a = u := by simpa using hp
      cases Q with
      | nil => simp at hq
      | cons b Q =>
        have hb : b = u := by simpa using hq
        subst a; subst b
        simp only [join_cons, List.nil_append, cost_singleton, Nat.zero_add]
    | cons b P =>
      have hh : (b :: P).getLast? = some u := by simpa using hp
      have ht := ih hh
      change cost (a :: (b :: P ++ Q.tail)) = _
      change cost (a :: b :: (P ++ Q.tail)) = _
      rw [cost_cons_cons]
      change (if a.length < b.length then 1 else 0) + cost (join (b::P) Q) = _
      rw [ht, cost_cons_cons]
      omega

 theorem cost_eq_edges {P : Walk α} : cost P ≤ P.length := by
  exact (List.countP_le_length).trans (by simp [List.length_zip])

 theorem valid_nil {V : Set (List α)} (s : List α) (hs : s ∈ V) : Valid V [s] := by
  exact ⟨by simp, by simpa using hs, by simp⟩

 theorem valid_step {V : Set (List α)} {s t : List α}
    (hs : s ∈ V) (ht : t ∈ V) (he : Edge s t) : Valid V [s,t] := by
  exact ⟨by simp, by simp only [List.mem_cons, List.not_mem_nil, or_false]; intro w h; rcases h with rfl|rfl <;> assumption,
    by simpa using he⟩

 theorem edge_path {V : Set (List α)} {s t : List α}
    (hs : s ∈ V) (ht : t ∈ V) (he : Edge s t) :
    ∃ P : Hierarchical.Path V s t, Path.points P = [s,t] ∧
      P.cost = (if s.length < t.length then 1 else 0) ∧
      ∀ w, P.Visits w ↔ w = s ∨ w = t := by
  rcases he with ⟨a,rfl⟩ | ⟨a,rfl⟩
  · exact ⟨.up s a hs ht, rfl, by simp [Hierarchical.Path.cost], by intro w; rfl⟩
  · exact ⟨.down a t hs ht, rfl, by simp [Hierarchical.Path.cost], by intro w; rfl⟩

 theorem realize {V : Set (List α)} {s : List α} {P : Walk α}
    (hv : Valid V (s::P)) :
    ∃ t, ∃ Q : Hierarchical.Path V s t, (s::P).getLast? = some t ∧
      Path.points Q = s::P ∧ Q.cost = cost (s::P) ∧
      ∀ w, Q.Visits w ↔ w ∈ s::P := by
  induction P generalizing s with
  | nil =>
    refine ⟨s,.nil s (hv.2.1 s (by simp)),rfl,rfl,rfl,?_⟩
    intro w
    simp only [Hierarchical.Path.Visits, List.mem_singleton]
  | cons t P ih =>
    have hchain := List.isChain_cons_cons.mp hv.2.2
    have ht : Valid V (t::P) := ⟨by simp, fun w hw => hv.2.1 w (List.mem_cons_of_mem _ hw), hchain.2⟩
    obtain ⟨u,Q,hl,hQ,hcQ,hvQ⟩ := ih ht
    obtain ⟨R,hR,hcR,hvR⟩ := edge_path (hv.2.1 s (by simp)) (hv.2.1 t (by simp)) hchain.1
    refine ⟨u,R.trans Q,?_,?_,?_,?_⟩
    · simpa using hl
    · simp only [Path.points, hR,hQ,join_cons,List.cons_append,List.nil_append]
    · simp only [Hierarchical.Path.cost_trans,hcR,hcQ,cost_cons_cons]
    · intro w
      simp only [Hierarchical.Path.Visits,hvR,hvQ,List.mem_cons]
      tauto

end Superstring.WalkCode

namespace Superstring.WalkCode
open BitCode Hierarchical
variable {α : Type}

 theorem mem_join {P Q : Walk α} {u w : List α}
    (hp : P.getLast? = some u) (hq : Q.head? = some u) :
    w ∈ join P Q ↔ w ∈ P ∨ w ∈ Q := by
  cases Q with
  | nil => simp at hq
  | cons x Q =>
    have hx : x = u := by simpa using hq
    subst x
    have hu : u ∈ P := List.mem_of_getLast? hp
    simp only [join,List.tail_cons,List.mem_append,List.mem_cons]
    constructor
    · intro h; rcases h with h|h
      · exact Or.inl h
      · exact Or.inr (Or.inr h)
    · intro h; rcases h with h|rfl|h
      · exact Or.inl h
      · exact Or.inl hu
      · exact Or.inr h

 theorem valid_join {V : Set (List α)} {P Q : Walk α} {u : List α}
    (hP : Valid V P) (hQ : Valid V Q)
    (hp : P.getLast? = some u) (hq : Q.head? = some u) : Valid V (join P Q) := by
  refine ⟨?_,?_,?_⟩
  · intro he
    exact hP.1 (List.append_eq_nil_iff.mp he).1
  · intro w hw
    rcases (mem_join hp hq).mp hw with hw|hw
    · exact hP.2.1 _ hw
    · exact hQ.2.1 _ hw
  · apply hP.2.2.append hQ.2.2.tail
    intro x hx y hy
    have hx' : x = u := by
      have hh : u = x := by simpa only [hp,Option.mem_some_iff] using hx
      exact hh.symm
    subst x
    cases Q with
    | nil => simp at hq
    | cons a Q =>
      have ha : a = u := by simpa using hq
      subst a
      exact (List.isChain_cons.mp hQ.2.2).1 y hy

@[simp] theorem head_join {P Q : Walk α} (hP : P ≠ []) :
    (join P Q).head? = P.head? := by
  cases P with
  | nil => contradiction
  | cons s P => rfl

@[simp] theorem last_join {P Q : Walk α} {u : List α}
    (hp : P.getLast? = some u) (hq : Q.head? = some u) :
    (join P Q).getLast? = Q.getLast? := by
  cases Q with
  | nil => simp at hq
  | cons a Q =>
    cases Q with
    | nil =>
      have ha : a = u := by simpa using hq
      subst a
      simpa only [join,List.tail_cons,List.append_nil,List.getLast?_singleton] using hp
    | cons b Q =>
      simp only [join,List.tail_cons,List.getLast?_append]
      rw [List.getLast?_eq_some_getLast (by simp)]
      rfl

 theorem points_spec {V : Set (List α)} {s t : List α} (P : Hierarchical.Path V s t) :
    Valid V (Path.points P) ∧ (Path.points P).head? = some s ∧
      (Path.points P).getLast? = some t ∧ cost (Path.points P) = P.cost ∧
      ∀ w, w ∈ Path.points P ↔ P.Visits w := by
  induction P with
  | nil s hs =>
    exact ⟨valid_nil s hs,rfl,rfl,rfl,by intro w; simp [Path.points,Hierarchical.Path.Visits]⟩
  | up s a hs ht =>
    exact ⟨valid_step hs ht (Or.inl ⟨a,rfl⟩),rfl,rfl,
      by simp [Path.points,Hierarchical.Path.cost],by intro w; simp [Path.points,Hierarchical.Path.Visits]⟩
  | down a s hs ht =>
    exact ⟨valid_step hs ht (Or.inr ⟨a,rfl⟩),rfl,rfl,
      by simp [Path.points,Hierarchical.Path.cost],by intro w; simp [Path.points,Hierarchical.Path.Visits]⟩
  | trans P Q ihP ihQ =>
    refine ⟨valid_join ihP.1 ihQ.1 ihP.2.2.1 ihQ.2.1,?_,?_,?_,?_⟩
    · exact (head_join ihP.1.1).trans ihP.2.1
    · exact (last_join ihP.2.2.1 ihQ.2.1).trans ihQ.2.2.1
    · change cost (join (Path.points P) (Path.points Q)) = _
      rw [cost_join _ _ _ ihP.2.2.1 ihQ.2.1,ihP.2.2.2.1,ihQ.2.2.2.1]
      rfl
    · intro w
      change w ∈ join (Path.points P) (Path.points Q) ↔ _
      rw [mem_join ihP.2.2.1 ihQ.2.1,ihP.2.2.2.2,ihQ.2.2.2.2]
      rfl

 theorem length_cost {V : Set (List α)} {s : List α} {P : Walk α}
    (hv : Valid V (s::P)) :
    P.length + ((s::P).getLast?.getD []).length = 2 * cost (s::P) + s.length := by
  induction P generalizing s with
  | nil => simp
  | cons t P ih =>
    have he := List.isChain_cons_cons.mp hv.2.2
    have ht : Valid V (t::P) := ⟨by simp,fun w hw => hv.2.1 w (List.mem_cons_of_mem _ hw),he.2⟩
    have hi := ih ht
    simp only [List.length_cons,cost_cons_cons]
    have hl : (s :: t :: P).getLast? = (t :: P).getLast? := by simp
    rw [hl]
    rcases he.1 with ⟨a,rfl⟩|⟨a,rfl⟩
    · simp only [List.length_append,List.length_singleton] at hi ⊢
      rw [ite_eq_left (by omega)]
      omega
    · simp only [List.length_cons] at hi ⊢
      rw [ite_eq_right (by omega)]
      omega

variable [Coded α]

@[fun_prop] theorem poly_join : Poly (fun q : Walk α × Walk α => join q.1 q.2) := by
  unfold join
  fun_prop

@[fun_prop] theorem poly_zip : Poly (fun p : Walk α × Walk α => p.1.zip p.2) := by
  have h : Poly (fun p : Walk α × Walk α =>
      (List.range (min p.1.length p.2.length)).map
        (fun i => (p.1[i]?.getD [], p.2[i]?.getD []))) := by
    apply BitCode.Poly.mapFn (f := fun q : (Walk α × Walk α) × ℕ =>
      (q.1.1[q.2]?.getD [], q.1.2[q.2]?.getD []))
    · exact ((BitCode.Poly.getD ([] : List α)).comp
          (f := fun q : (Walk α × Walk α) × ℕ => (q.1.1,q.2)) (by fun_prop)).pair
        ((BitCode.Poly.getD ([] : List α)).comp
          (f := fun q : (Walk α × Walk α) × ℕ => (q.1.2,q.2)) (by fun_prop))
    · fun_prop
  convert h using 1
  funext p
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [List.getElem_zip,List.getElem_map,List.getElem_range]
    have hi1 : i < p.1.length := (lt_min_iff.mp (by simpa using h1)).1
    have hi2 : i < p.2.length := (lt_min_iff.mp (by simpa using h1)).2
    simp only [List.getElem?_eq_getElem hi1,List.getElem?_eq_getElem hi2,Option.getD_some]

@[fun_prop] theorem poly_cost : Poly (fun P : Walk α => cost P) := by
  have h : Poly (fun P : Walk α =>
      ((P.zip P.tail).filter (fun q => decide (q.1.length < q.2.length))).length) := by
    apply BitCode.Poly.length.comp
    apply BitCode.Poly.filterFn (p := fun q : Walk α × (List α × List α) =>
      decide (q.2.1.length < q.2.2.length))
    · fun_prop
    · fun_prop
  simpa only [cost,List.countP_eq_length_filter] using h

end Superstring.WalkCode


namespace Superstring.WalkCode
open BitCode Hierarchical
variable {α : Type}

def delete (a b : List α) : Walk α :=
  (List.range (a.length+1)).map (fun i => (a++b).drop i)

def append (a b : List α) : Walk α :=
  (List.range (b.length+1)).map (fun i => a++b.take i)

def gap (w : List α) : Walk α := [[]] ++ w.flatMap (fun a => [[a],[]])

@[simp] theorem delete_nil (b : List α) : delete [] b = [b] := by simp [delete]
@[simp] theorem delete_cons (a : α) (as b : List α) :
    delete (a::as) b = (a::(as++b)) :: delete as b := by
  simp only [delete,List.length_cons,List.range_succ_eq_map,List.map_cons,List.map_map,
    List.cons_append,List.drop_zero,List.drop_succ_cons,Function.comp_def]

@[simp] theorem append_nil (a : List α) : append a [] = [a] := by simp [append]
@[simp] theorem append_cons (a : List α) (b : α) (bs : List α) :
    append a (b::bs) = a :: append (a++[b]) bs := by
  simp only [append,List.length_cons,List.range_succ_eq_map,List.map_cons,List.map_map,
    List.take_zero,List.append_nil,List.take_succ_cons,Function.comp_def]
  simp only [List.append_assoc,List.singleton_append]

@[simp] theorem gap_nil : gap ([] : List α) = [[]] := rfl
@[simp] theorem gap_cons (a : α) (as : List α) :
    gap (a::as) = [] :: [a] :: gap as := by rfl

 theorem points_copy {V : Set (List α)} {s t s' t' : List α}
    (P : Hierarchical.Path V s t) (hs : s = s') (ht : t = t') :
    Path.points (P.copy hs ht) = Path.points P := by subst s'; subst t'; rfl

 theorem points_delete {V : Set (List α)} (closed : SubstringClosed V)
    (a b : List α) (h : a++b ∈ V) :
    Path.points (Hierarchical.Path.deletePrefix closed a b h) = delete a b := by
  induction a with
  | nil => simp [Hierarchical.Path.deletePrefix,Path.points]
  | cons a as ih =>
    simp only [Hierarchical.Path.deletePrefix,Path.points,ih,delete_cons]
    have hhead : (delete as b).head? = some (as++b) := by
      unfold delete
      rw [List.range_succ_eq_map]
      simp only [List.map_cons,List.drop_zero,List.head?_cons]
    cases he : delete as b with
    | nil => simp [he] at hhead
    | cons x xs =>
      have hx : x = as++b := by simpa [he] using hhead
      simp [join,hx]

 theorem points_append {V : Set (List α)} (closed : SubstringClosed V)
    (a b : List α) (h : a++b ∈ V) :
    Path.points (Hierarchical.Path.appendSuffix closed a b h) = append a b := by
  induction b generalizing a with
  | nil => simp [Hierarchical.Path.appendSuffix,points_copy,Path.points]
  | cons b bs ih =>
    simp only [Hierarchical.Path.appendSuffix,points_copy,Path.points,ih,append_cons]
    unfold join
    have hhead : (append (a++[b]) bs).head? = some (a++[b]) := by
      rw [← ih _ (by simpa only [List.append_assoc,List.singleton_append] using h)]
      exact (points_spec _).2.1
    cases he : append (a++[b]) bs with
    | nil => simp [he] at hhead
    | cons x xs =>
      have hx : x = a++[b] := by simpa [he] using hhead
      simp [hx]

 theorem points_gap {V : Set (List α)} (h0 : ([] : List α) ∈ V)
    (w : List α) (h : ∀ a ∈ w, [a] ∈ V) :
    Path.points (Hierarchical.Path.readGap h0 w h) = gap w := by
  induction w with
  | nil => rfl
  | cons a as ih => simp [Hierarchical.Path.readGap,Path.points,ih,join,gap]

 theorem delete_spec {V : Set (List α)} (closed : SubstringClosed V)
    (a b : List α) (h : a++b ∈ V) :
    Valid V (delete a b) ∧ (delete a b).head? = some (a++b) ∧
      (delete a b).getLast? = some b ∧ cost (delete a b) = 0 := by
  have hh := points_spec (Hierarchical.Path.deletePrefix closed a b h)
  rw [points_delete] at hh
  exact ⟨hh.1,hh.2.1,hh.2.2.1,hh.2.2.2.1.trans (Hierarchical.Path.cost_deletePrefix ..)⟩

 theorem append_spec {V : Set (List α)} (closed : SubstringClosed V)
    (a b : List α) (h : a++b ∈ V) :
    Valid V (append a b) ∧ (append a b).head? = some a ∧
      (append a b).getLast? = some (a++b) ∧ cost (append a b) = b.length := by
  have hh := points_spec (Hierarchical.Path.appendSuffix closed a b h)
  rw [points_append] at hh
  exact ⟨hh.1,hh.2.1,hh.2.2.1,hh.2.2.2.1.trans (Hierarchical.Path.cost_appendSuffix ..)⟩

 theorem gap_spec {V : Set (List α)} (h0 : ([] : List α) ∈ V)
    (w : List α) (h : ∀ a ∈ w, [a] ∈ V) :
    Valid V (gap w) ∧ (gap w).head? = some [] ∧
      (gap w).getLast? = some [] ∧ cost (gap w) = w.length := by
  have hh := points_spec (Hierarchical.Path.readGap h0 w h)
  rw [points_gap] at hh
  exact ⟨hh.1,hh.2.1,hh.2.2.1,hh.2.2.2.1.trans (Hierarchical.Path.cost_readGap ..)⟩

 theorem mem_delete (a b : List α) (i : ℕ) (hi : i ≤ a.length) :
    (a++b).drop i ∈ delete a b := by
  exact List.mem_map.mpr ⟨i,List.mem_range.mpr (by omega),rfl⟩

 theorem mem_append (a b : List α) (i : ℕ) (hi : i ≤ b.length) :
    a++b.take i ∈ append a b := by
  exact List.mem_map.mpr ⟨i,List.mem_range.mpr (by omega),rfl⟩

variable [Coded α]

@[fun_prop] theorem poly_delete : Poly (fun q : List α × List α => delete q.1 q.2) := by
  unfold delete
  exact BitCode.Poly.mapFn
    (f := fun q : (List α × List α) × ℕ => (q.1.1++q.1.2).drop q.2)
    (by fun_prop) (by fun_prop)

@[fun_prop] theorem poly_append : Poly (fun q : List α × List α => append q.1 q.2) := by
  unfold append
  exact BitCode.Poly.mapFn
    (f := fun q : (List α × List α) × ℕ => q.1.1++q.1.2.take q.2)
    (by fun_prop) (by fun_prop)

@[fun_prop] theorem poly_gap : Poly (gap : List α → Walk α) := by
  have hm : Poly (fun w : List α => w.map (fun a => [[a],[]])) :=
    BitCode.Poly.map (show Poly (fun a : α => [[a],[]]) from by fun_prop)
  have hf := BitCode.Poly.flatten.comp hm
  have ha : Poly (fun w : List α => [[]] ++ (w.map (fun a => [[a],[]])).flatten) := by
    fun_prop
  exact ha

end Superstring.WalkCode


namespace Superstring.WalkCode
open BitCode Hierarchical
variable {α : Type}

def Runs (V : Set (List α)) (s t : List α) (P : Walk α) : Prop :=
  Valid V P ∧ P.head? = some s ∧ P.getLast? = some t

 theorem runs_join {V : Set (List α)} {s t u : List α} {P Q : Walk α}
    (hp : Runs V s t P) (hq : Runs V t u Q) : Runs V s u (join P Q) :=
  ⟨valid_join hp.1 hq.1 hp.2.2 hq.2.1,
    (head_join hp.1.1).trans hp.2.1,(last_join hp.2.2 hq.2.1).trans hq.2.2⟩

 theorem runs_points {V : Set (List α)} {s t : List α} (P : Hierarchical.Path V s t) :
    Runs V s t (Path.points P) := by
  have h := points_spec P
  exact ⟨h.1,h.2.1,h.2.2.1⟩

 theorem take_drop_join (P : Walk α) {i : ℕ} (_hi : i < P.length) :
    join (P.take (i+1)) (P.drop i) = P := by
  simp only [join,List.tail_drop]
  exact List.take_append_drop _ _

 theorem split_runs {V : Set (List α)} {s t : List α} {P : Walk α}
    (hp : Runs V s t P) {i : ℕ} (hi : i < P.length) :
    Runs V s P[i] (P.take (i+1)) ∧ Runs V P[i] t (P.drop i) := by
  have ht : P.take (i+1) ≠ [] := List.length_pos_iff.mp (by simp only [List.length_take]; omega)
  have hd : P.drop i ≠ [] := List.length_pos_iff.mp (by simp only [List.length_drop]; omega)
  have htake : Valid V (P.take (i+1)) :=
    ⟨ht,fun w hw => hp.1.2.1 w (List.mem_of_mem_take hw),hp.1.2.2.take _⟩
  have hdrop : Valid V (P.drop i) :=
    ⟨hd,fun w hw => hp.1.2.1 w (List.mem_of_mem_drop hw),hp.1.2.2.drop _⟩
  refine ⟨⟨htake,?_,?_⟩,⟨hdrop,?_,?_⟩⟩
  · simpa only [List.head?_take,ite_eq_right (by omega : i+1 ≠ 0)] using hp.2.1
  · simp only [List.getLast?_take,ite_eq_right (by omega : i+1 ≠ 0),Nat.add_sub_cancel,
      List.getElem?_eq_getElem hi,Option.some_or]
  · simp [List.head?_drop,List.getElem?_eq_getElem hi]
  · simpa only [List.getLast?_drop,ite_eq_right (by omega : ¬P.length ≤ i)] using hp.2.2

def rotate (P : Walk α) (i : ℕ) : Walk α := join (P.drop i) (P.take (i+1))

 theorem rotate_spec {V : Set (List α)} {s : List α} {P : Walk α}
    (hp : Runs V s s P) {i : ℕ} (hi : i < P.length) :
    Runs V P[i] P[i] (rotate P i) ∧ cost (rotate P i) = cost P ∧
      ∀ w, w ∈ rotate P i ↔ w ∈ P := by
  obtain ⟨hA,hB⟩ := split_runs hp hi
  refine ⟨runs_join hB hA,?_,?_⟩
  · unfold rotate
    rw [cost_join _ _ _ hB.2.2 hA.2.1]
    have hh := cost_join _ _ _ hA.2.2 hB.2.1
    rw [take_drop_join P hi] at hh
    omega
  · intro w
    unfold rotate
    rw [mem_join hB.2.2 hA.2.1]
    have hh := @mem_join α (P.take (i+1)) (P.drop i) P[i] w hA.2.2 hB.2.1
    rw [take_drop_join P hi] at hh
    tauto

def insertAt (P Q : Walk α) (i : ℕ) : Walk α :=
  join (join (P.take (i+1)) Q) (P.drop i)

 theorem insertAt_spec {V : Set (List α)} {s t : List α} {P Q : Walk α}
    (hp : Runs V s t P) {i : ℕ} (hi : i < P.length)
    (hq : Runs V P[i] P[i] Q) :
    Runs V s t (insertAt P Q i) ∧ cost (insertAt P Q i) = cost P + cost Q ∧
      ∀ w, w ∈ insertAt P Q i ↔ w ∈ P ∨ w ∈ Q := by
  obtain ⟨hA,hB⟩ := split_runs hp hi
  have hAQ := runs_join hA hq
  refine ⟨runs_join hAQ hB,?_,?_⟩
  · unfold insertAt
    rw [cost_join _ _ _ hAQ.2.2 hB.2.1,cost_join _ _ _ hA.2.2 hq.2.1]
    have hh := cost_join _ _ _ hA.2.2 hB.2.1
    rw [take_drop_join P hi] at hh
    omega
  · intro w
    unfold insertAt
    rw [mem_join hAQ.2.2 hB.2.1,mem_join hA.2.2 hq.2.1]
    have hh := @mem_join α (P.take (i+1)) (P.drop i) P[i] w hA.2.2 hB.2.1
    rw [take_drop_join P hi] at hh
    tauto

variable [Coded α]
@[fun_prop] theorem poly_rotate : Poly (fun q : Walk α × ℕ => rotate q.1 q.2) := by
  unfold rotate
  fun_prop
@[fun_prop] theorem poly_insertAt : Poly (fun q : Walk α × Walk α × ℕ =>
    insertAt q.1 q.2.1 q.2.2) := by
  unfold insertAt
  fun_prop

end Superstring.WalkCode


namespace Superstring.WalkCode
open BitCode Hierarchical
variable {α : Type} [DecidableEq α]

def locate (P : Walk α) (w : List α) : ℕ :=
  ThreadArray.first P.length (fun i => equal (P[i]?.getD []) w)

def meeting (P Q : Walk α) : ℕ :=
  ThreadArray.first P.length (fun i => member (P[i]?.getD []) Q)

def splice (P Q : Walk α) : Walk α :=
  let i := meeting P Q
  let j := locate Q (P[i]?.getD [])
  insertAt P (rotate Q j) i

 theorem locate_spec {P : Walk α} {w : List α} (hw : w ∈ P) :
    locate P w < P.length ∧ P[locate P w]?.getD [] = w := by
  obtain ⟨i,hi,he⟩ := List.getElem_of_mem hw
  have hex : ∃ i < P.length, equal (P[i]?.getD []) w = true := by
    exact ⟨i,hi,by simp [List.getElem?_eq_getElem hi,he,equal]⟩
  have hh := ThreadArray.first_spec hex
  exact ⟨hh.1, of_decide_eq_true hh.2.1⟩

 theorem meeting_spec {P Q : Walk α} (h : ∃ w, w ∈ P ∧ w ∈ Q) :
    meeting P Q < P.length ∧ P[meeting P Q]?.getD [] ∈ Q := by
  obtain ⟨w,hwP,hwQ⟩ := h
  obtain ⟨i,hi,he⟩ := List.getElem_of_mem hwP
  have hex : ∃ i < P.length, member (P[i]?.getD []) Q = true := by
    exact ⟨i,hi,by simp [List.getElem?_eq_getElem hi,he,hwQ]⟩
  have hh := ThreadArray.first_spec hex
  exact ⟨hh.1,(member_eq ..).mp hh.2.1⟩

 theorem splice_spec {V : Set (List α)} {s t u : List α} {P Q : Walk α}
    (hp : Runs V s t P) (hq : Runs V u u Q) (hm : ∃ w, w ∈ P ∧ w ∈ Q) :
    Runs V s t (splice P Q) ∧ cost (splice P Q) = cost P + cost Q ∧
      ∀ w, w ∈ splice P Q ↔ w ∈ P ∨ w ∈ Q := by
  obtain ⟨hi,hm⟩ := meeting_spec hm
  obtain ⟨hj,he⟩ := locate_spec hm
  have he' : Q[locate Q (P[meeting P Q]?.getD [])] = P[meeting P Q] := by
    rw [List.getElem?_eq_getElem hj,Option.getD_some] at he
    simpa only [List.getElem?_eq_getElem hi,Option.getD_some] using he
  obtain ⟨hr,hc,hv⟩ := rotate_spec hq hj
  rw [he'] at hr
  obtain ⟨hR,hRc,hRv⟩ := insertAt_spec hp hi hr
  exact ⟨hR,by simpa only [splice,hc] using hRc,by intro w; simpa only [splice,hv] using hRv w⟩

variable [Coded α]
@[fun_prop] theorem poly_locate : Poly (fun q : Walk α × List α => locate q.1 q.2) := by
  unfold locate ThreadArray.first
  exact (BitCode.Poly.headD 0).comp (BitCode.Poly.filterFn
    (p := fun q : (Walk α × List α) × ℕ => equal (q.1.1[q.2]?.getD []) q.1.2)
    (BitCode.Poly.equal.comp (((BitCode.Poly.getD ([] : List α)).comp
      (f := fun q : (Walk α × List α) × ℕ => (q.1.1,q.2)) (by fun_prop)).pair (by fun_prop))) (by fun_prop))
@[fun_prop] theorem poly_meeting : Poly (fun q : Walk α × Walk α => meeting q.1 q.2) := by
  unfold meeting ThreadArray.first
  exact (BitCode.Poly.headD 0).comp (BitCode.Poly.filterFn
    (p := fun q : (Walk α × Walk α) × ℕ => member (q.1.1[q.2]?.getD []) q.1.2)
    (BitCode.Poly.member.comp (((BitCode.Poly.getD ([] : List α)).comp
      (f := fun q : (Walk α × Walk α) × ℕ => (q.1.1,q.2)) (by fun_prop)).pair (by fun_prop))) (by fun_prop))
@[fun_prop] theorem poly_splice : Poly (fun q : Walk α × Walk α => splice q.1 q.2) := by
  have hh : Poly (fun q : Walk α × Walk α => q.1[meeting q.1 q.2]?.getD []) :=
    (BitCode.Poly.getD ([] : List α)).comp (BitCode.Poly.fst.pair poly_meeting)
  unfold splice
  dsimp only
  fun_prop

 omit [DecidableEq α] in
 theorem size_join (P Q : Walk α) : bitSize (join P Q) ≤ bitSize P + bitSize Q := by
  have hh := bitSize_append P Q.tail
  have ht := bitSize_sublist (List.tail_sublist Q)
  unfold join
  omega

 omit [DecidableEq α] in
 theorem size_rotate (P : Walk α) (i : ℕ) : bitSize (rotate P i) ≤ 2 * bitSize P := by
  have hh := size_join (P.drop i) (P.take (i+1))
  have hd := bitSize_sublist (List.drop_sublist i P)
  have ht := bitSize_sublist (List.take_sublist (i+1) P)
  unfold rotate
  omega

 omit [DecidableEq α] in
 theorem size_insertAt (P Q : Walk α) (i : ℕ) :
    bitSize (insertAt P Q i) ≤ bitSize P + bitSize Q := by
  have he : insertAt P Q i = (P.take (i+1) ++ Q.tail) ++ P.drop (i+1) := by
    simp only [insertAt,join,List.tail_drop]
  rw [he]
  have h1 := bitSize_append (P.take (i+1)) Q.tail
  have h2 := bitSize_append (P.take (i+1) ++ Q.tail) (P.drop (i+1))
  have h3 := bitSize_append (P.take (i+1)) (P.drop (i+1))
  rw [List.take_append_drop] at h3
  have ht := bitSize_sublist (List.tail_sublist Q)
  omega
 theorem size_splice (P Q : Walk α) : bitSize (splice P Q) ≤ bitSize P + 2 * bitSize Q := by
  exact (size_insertAt _ _ _).trans (Nat.add_le_add_left (size_rotate _ _) _)

 def fill (P : Walk α) (Qs : List (Walk α)) : Walk α := Qs.foldl splice P
@[fun_prop] theorem poly_fill : Poly (fun q : Walk α × List (Walk α) => fill q.1 q.2) := by
  have hs : ∀ P Q : Walk α, bitSize (splice P Q) ≤ bitSize P +
      (2 * Polynomial.X : Polynomial ℕ).eval (bitSize Q) := by
    intro P Q
    simpa only [Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X] using size_splice P Q
  exact (BitCode.Poly.foldl_additive poly_splice (2 * Polynomial.X) hs).comp
    (BitCode.Poly.snd.pair BitCode.Poly.fst)

omit [Coded α] in
 theorem fill_spec {V : Set (List α)} {s t : List α} (P : Walk α) (Qs : List (Walk α))
    (hp : Runs V s t P) (hq : ∀ Q ∈ Qs, ∃ u, Runs V u u Q)
    (hm : ∀ Q ∈ Qs, ∃ w, w ∈ P ∧ w ∈ Q) :
    Runs V s t (fill P Qs) ∧ cost (fill P Qs) = cost P + (Qs.map cost).sum ∧
      ∀ w, w ∈ fill P Qs ↔ w ∈ P ∨ ∃ Q ∈ Qs, w ∈ Q := by
  induction Qs generalizing P with
  | nil => exact ⟨hp,by simp [fill],by simp [fill]⟩
  | cons Q Qs ih =>
    obtain ⟨u,hu⟩ := hq Q (by simp)
    obtain ⟨hr,hc,hv⟩ := splice_spec hp hu (hm Q (by simp))
    obtain ⟨hR,hC,hV⟩ := ih (splice P Q) hr
      (fun R hR => hq R (List.mem_cons_of_mem _ hR)) (by
        intro R hR
        obtain ⟨w,hw,hwR⟩ := hm R (List.mem_cons_of_mem _ hR)
        exact ⟨w,(hv w).mpr (Or.inl hw),hwR⟩)
    refine ⟨hR,?_,?_⟩
    · change cost (fill (splice P Q) Qs) = _
      rw [hC,hc,List.map_cons,List.sum_cons]
      omega
    · intro w
      change w ∈ fill (splice P Q) Qs ↔ _
      rw [hV,hv]
      simp only [List.mem_cons,or_and_right,exists_or,exists_eq_left]
      tauto
end Superstring.WalkCode

end OAI
