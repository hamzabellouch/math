import OAI.Computability.Superstring.GroupBridge

namespace OAI

namespace Superstring.CollectionCode
open BitCode Hierarchical LayerArray WalkCode
variable {α : Type} [Inhabited α] [DecidableEq α]
abbrev Env (α : Type) := (List (GroupData α) × List ℕ) × ℕ
def data (X : Env α) (g : ℕ) : GroupData α := X.1.1[g]?.getD ([],[])
def gs (X : Env α) : List ℕ := X.1.2
def stride (X : Env α) : ℕ := X.2
def owner (X : Env α) (i : ℕ) : ℕ := i / stride X
def idx (X : Env α) (i : ℕ) : ℕ := i % stride X
def layer (X : Env α) (i : ℕ) : List α × List ℕ :=
  ((data X (owner X i)).1,exits (data X (owner X i)) (idx X i))
def book (X : Env α) : UpperCode.Book α := (List.range (X.1.1.length*stride X)).map (layer X)
def ids (X : Env α) : List ℕ := (gs X).flatMap (fun g =>
  (List.range (data X g).2.length).map (fun i => g*stride X+i))
def per (X : Env α) (g : ℕ) : ℕ := (data X g).1.length
def phase [LinearOrder α] (X : Env α) (g : ℕ) : ℤ := RotationCode.phase (data X g).1
def contents (X : Env α) : List (Walk α) := (book X).map (fun d => content d.1 d.2)
def ls (X : Env α) : ℕ → Walk α := BlockClose.lookup (contents X)

omit [Inhabited α] [DecidableEq α] in
theorem owner_encode (X : Env α) (g i : ℕ) (hi : i < stride X) : owner X (g*stride X+i) = g := by
  have hp : 0 < stride X := by omega
  simp only [owner,Nat.add_mul_div_right i g hp,add_comm (g*stride X) i]
  rw [Nat.div_eq_of_lt hi,zero_add]
omit [Inhabited α] [DecidableEq α] in
theorem idx_encode (X : Env α) (g i : ℕ) (hi : i < stride X) : idx X (g*stride X+i) = i := by
  unfold idx
  rw [Nat.add_mod,Nat.mul_mod_left,zero_add,Nat.mod_eq_of_lt hi,Nat.mod_eq_of_lt hi]

omit [Inhabited α] [DecidableEq α] in
theorem lookup_encode (X : Env α) (g i : ℕ) (hg : g < X.1.1.length) (hi : i < stride X) :
    UpperCode.lookup (book X) (g*stride X+i) = ((data X g).1,exits (data X g) i) := by
  have hb : g*stride X+i < X.1.1.length*stride X := by nlinarith
  simp only [UpperCode.lookup,book,List.getElem?_map,List.getElem?_range hb,
    Option.map_some,Option.getD_some,layer,owner_encode X g i hi,idx_encode X g i hi]

omit [DecidableEq α] in
theorem ls_encode (X : Env α) (g i : ℕ) (hg : g < X.1.1.length) (hi : i < stride X) :
    ls X (g*stride X+i) = content (data X g).1 (exits (data X g) i) := by
  have hb : g*stride X+i < X.1.1.length*stride X := by nlinarith
  simp only [ls,BlockClose.lookup,contents,book,List.getElem?_map,List.getElem?_range hb,
    Option.map_some,Option.getD_some,layer,owner_encode X g i hi,idx_encode X g i hi]

omit [Inhabited α] [DecidableEq α] in
theorem encode_injective (X : Env α) {g h i j : ℕ} (hi : i < stride X) (hj : j < stride X)
    (he : g*stride X+i = h*stride X+j) : g = h ∧ i = j := by
  exact ⟨by have := congrArg (owner X) he; simpa only [owner_encode X g i hi,owner_encode X h j hj] using this,
    by have := congrArg (idx X) he; simpa only [idx_encode X g i hi,idx_encode X h j hj] using this⟩

variable [Coded α]
omit [Inhabited α] [DecidableEq α] in
@[fun_prop] theorem poly_data : Poly (fun q : Env α × ℕ => data q.1 q.2) := by
  unfold data
  exact (BitCode.Poly.getD ([],[])).comp (f := fun q : Env α × ℕ => (q.1.1.1,q.2)) (by fun_prop)
omit [Inhabited α] [DecidableEq α] in
@[fun_prop] theorem poly_owner : Poly (fun q : Env α × ℕ => owner q.1 q.2) := by unfold owner stride; fun_prop
omit [Inhabited α] [DecidableEq α] in
@[fun_prop] theorem poly_idx : Poly (fun q : Env α × ℕ => idx q.1 q.2) := by unfold idx stride; fun_prop
omit [Inhabited α] [DecidableEq α] in
@[fun_prop] theorem poly_layer : Poly (fun q : Env α × ℕ => layer q.1 q.2) := by unfold layer; fun_prop
omit [Inhabited α] [DecidableEq α] in
@[fun_prop] theorem poly_book : Poly (fun X : Env α => book X) := by
  unfold book stride
  exact BitCode.Poly.mapFn poly_layer (by fun_prop)
omit [Inhabited α] [DecidableEq α] in
@[fun_prop] theorem poly_ids : Poly (fun X : Env α => ids X) := by
  unfold ids gs stride
  apply BitCode.Poly.flatMapFn (f := fun q : Env α × ℕ =>
    (List.range (data q.1 q.2).2.length).map (fun i => q.2*q.1.2+i))
  · exact BitCode.Poly.mapFn (f := fun q : (Env α × ℕ) × ℕ => q.1.2*q.1.1.2+q.2) (by fun_prop) (by fun_prop)
  · fun_prop
omit [Inhabited α] [DecidableEq α] in
@[fun_prop] theorem poly_per : Poly (fun q : Env α × ℕ => per q.1 q.2) := by unfold per; fun_prop
omit [DecidableEq α] in
@[fun_prop] theorem poly_contents : Poly (fun X : Env α => contents X) := by
  unfold contents
  exact BitCode.Poly.mapFn (f := fun q : Env α × (List α × List ℕ) => content q.2.1 q.2.2) (by fun_prop) poly_book
variable [LinearOrder α]
omit [DecidableEq α] in
@[fun_prop] theorem poly_phase (hlt : Poly (fun q : α × α => decide (q.1<q.2))) :
    Poly (fun q : Env α × ℕ => phase q.1 q.2) := by
  unfold phase
  exact BitCode.Poly.natCastInt.comp ((RotationCode.poly_phase hlt).comp (by fun_prop))
end Superstring.CollectionCode


namespace Superstring.CollectionCode
open BitCode Hierarchical LayerArray WalkCode
variable {α G : Type} [Inhabited α] [LinearOrder α] {V : Set (List α)}

noncomputable def rank (X : Env α) (g : ℕ) : Lex (ℕ → α) :=
  forward (PeriodWord.text (data X g).1) (phase X g)


structure Model (X : Env α) (C : LayerCollection V G) where
  group : G → ℕ
  group_inj : Function.Injective group
  groups : ∀ j, j ∈ gs X ↔ ∃ g, group g = j
  nodup : (gs X).Nodup
  bound : ∀ g, group g < X.1.1.length
  size : ∀ g, (data X (group g)).2.length = C.size g
  capacity : ∀ g, C.size g ≤ stride X
  rep : ∀ (g) (i : Fin (C.size g)), Represents (data X (group g)).1
    (exits (data X (group g)) i.val) (C.layer g i)
  phase_eq : ∀ g, phase X (group g) = C.distinguished g

namespace Model
variable {X : Env α} {C : LayerCollection V G} (h : Model X C)
def encode (i : C.Id) : ℕ := h.group i.1*stride X+i.2.val

include h
theorem local_lt (g : G) (i : Fin (C.size g)) : i.val < stride X := lt_of_lt_of_le i.isLt (h.capacity g)
@[simp] theorem owner_eq (i : C.Id) : owner X (h.encode i) = h.group i.1 :=
  owner_encode X _ _ (h.local_lt ..)
@[simp] theorem idx_eq (i : C.Id) : idx X (h.encode i) = i.2.val := idx_encode X _ _ (h.local_lt ..)

theorem encode_inj : Function.Injective h.encode := by
  intro i j he
  obtain ⟨i,k⟩ := i
  obtain ⟨j,l⟩ := j
  obtain ⟨hg,hi⟩ := encode_injective X (h.local_lt i k) (h.local_lt j l) he
  have hg' : i = j := h.group_inj hg
  subst j
  exact Sigma.mk.inj_iff.mpr ⟨rfl,heq_of_eq (Fin.ext hi)⟩

theorem id_mem (i : C.Id) : h.encode i ∈ ids X := by
  apply List.mem_flatMap.mpr
  refine ⟨h.group i.1,(h.groups _).mpr ⟨i.1,rfl⟩,List.mem_map.mpr ⟨i.2.val,?_,rfl⟩⟩
  rw [List.mem_range,h.size]
  exact i.2.isLt

theorem mem_ids (j : ℕ) : j ∈ ids X ↔ ∃ i, h.encode i = j := by
  constructor
  · intro hj
    obtain ⟨g,hg,hj⟩ := List.mem_flatMap.mp hj
    obtain ⟨a,rfl⟩ := (h.groups g).mp hg
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hj
    have hi' : i < C.size a := by simpa only [List.mem_range,h.size] using hi
    exact ⟨⟨a,⟨i,hi'⟩⟩,rfl⟩
  · rintro ⟨i,rfl⟩
    exact h.id_mem i

theorem book_rep (i : C.Id) : Represents (UpperCode.lookup (book X) (h.encode i)).1
    (UpperCode.lookup (book X) (h.encode i)).2 (C.layerAt i) := by
  rw [encode,lookup_encode X _ _ (h.bound _) (h.local_lt ..)]
  exact h.rep ..

theorem content_iff (i : C.Id) (w : List α) : w ∈ ls X (h.encode i) ↔ w ∈ (C.layerAt i).Content := by
  rw [encode,ls_encode X _ _ (h.bound _) (h.local_lt ..)]
  exact mem_content (h.rep i.1 i.2) (C.positive i.1) (C.periodic i.1) w

@[simp] theorem per_eq (g : G) : per X (h.group g) = C.period g :=
  (h.rep g ⟨0,C.nonempty g⟩).length_eq
@[simp] theorem text_eq (g : G) : PeriodWord.text (data X (h.group g)).1 = C.text g :=
  (h.rep g ⟨0,C.nonempty g⟩).text_eq
@[simp] theorem rank_eq (g : G) : rank X (h.group g) = C.rank g := by
  simp only [rank,h.text_eq,h.phase_eq,LayerCollection.rank]

def natIndex (_h : Model X C) (g : G) (i : ℕ) : Fin (C.size g) :=
  ⟨min i (C.size g-1),by have := C.nonempty g; omega⟩
def natLayer (g : G) (i : ℕ) : Layer V (C.text g) (C.period g) := C.layer g (h.natIndex g i)
@[simp] theorem natIndex_val (g : G) {i : ℕ} (hi : i < C.size g) : (h.natIndex g i).val = i := by
  exact Nat.min_eq_left (by omega)
@[simp] theorem natLayer_fin (g : G) (i : Fin (C.size g)) : h.natLayer g i.val = C.layer g i := by
  unfold natLayer
  congr 1
  exact Fin.ext (h.natIndex_val g i.isLt)
theorem nat_rep (g : G) {i : ℕ} (hi : i < C.size g) :
    Represents (data X (h.group g)).1 (exits (data X (h.group g)) i) (h.natLayer g i) := by
  simpa only [natLayer,h.natIndex_val g hi] using h.rep g (h.natIndex g i)
theorem nat_order (g : G) {i j : ℕ} (hij : i ≤ j) (x : ℤ) :
    (h.natLayer g i).z x ≤ (h.natLayer g j).z x := by
  apply C.ordered
  change min i _ ≤ min j _
  omega

theorem rank_shift (g : G) (d : C.Id) (r : ℤ)
    (hr : rank X (owner X (h.encode d)) ≤ rank X (h.group g)) :
    ∀ x, forward (fun x => C.text d.1 (x+r)) x ≤ forward (C.text g) (C.distinguished g) := by
  rw [h.owner_eq,h.rank_eq,h.rank_eq] at hr
  intro x
  rw [forward_shift]
  exact (C.distinguished_max d.1 (x+r)).trans hr
end Model
end Superstring.CollectionCode


namespace Superstring.CollectionCode
open BitCode Hierarchical LayerArray WalkCode BlockClose
variable {α G : Type} [Inhabited α] [LinearOrder α] {V : Set (List α)}

def hard (X : Env α) (g cut : ℕ) (v : UpperCode.Param) : DistributeCode.Result α :=
  let D := data X g
  DistributeCode.record D g v.2.1 (g*stride X) (UpperCode.upper D.2.length cut)
    (D.2.length-v.1) (D.2.length-1) (RecordCode.start v.2.2) (RecordCode.stop v.2.2) (phase X g)

namespace Model
variable {X : Env α} {C : LayerCollection V G} (h : Model X C)

theorem hard_spec (closed : SubstringClosed V) (g : G) (cut : ℕ) (v : UpperCode.Param)
    (hcut : cut < C.size g) (hv : v.2.1 ∈ ids X)
    (ht : UpperCode.test (data X (h.group g)) (book X) cut (phase X (h.group g)) v = true)
    (hf : UpperCode.foreign (data X (h.group g)) (book X) v = true) :
    let o := hard X (h.group g) cut v
    Runs V [] [] o.1 ∧ DistributeCode.budget o (C.period g) ≤ 2*((C.size g-cut)*C.period g) ∧
      (∀ b ∈ o.2.1, ValidBlock V (ids X) (ls X) (owner X) (per X) (rank X) b) ∧
      (∀ i : Fin (C.size g), cut ≤ i.val →
        (∀ w ∈ ls X (h.encode ⟨g,i⟩), w ∈ o.1) ∨
        (∃ b ∈ o.2.1, h.encode ⟨g,i⟩ ∈ b.members) ∨ i.val ∈ o.2.2) ∧
      o.2.2.Sublist (UpperCode.upper (C.size g) cut) ∧
      ∃ (d : C.Id) (R : (C.layerAt d).Record (C.text g)), h.encode d = v.2.1 ∧
        R.offset = RecordCode.offset v.2.2 ∧ R.start = RecordCode.start v.2.2 ∧ R.stop = RecordCode.stop v.2.2 ∧
        C.text g ≠ (fun x => C.text d.1 (x+R.offset)) ∧
        ∀ i ∈ o.2.2, R.start+C.period g < (h.natLayer g i).first R.start ∧
          (h.natLayer g i).last R.start < R.stop-C.period g := by
  obtain ⟨d,hd⟩ := (h.mem_ids v.2.1).mp hv
  unfold UpperCode.test at ht
  unfold UpperCode.foreign at hf
  rw [← hd] at ht hf
  simp only [Bool.and_eq_true,less,lessEq,decide_eq_true_eq,
    h.size,h.phase_eq] at ht
  obtain ⟨⟨⟨⟨⟨⟨⟨hk,hkn⟩,hr⟩,hat⟩,htb⟩,hH⟩,hsharp⟩,hfirst⟩ := ht
  let D := data X (h.group g)
  have hp : D.1.length = C.period g := h.per_eq g
  let R := RecordCode.checkedRecord (h.text_eq g) (h.book_rep d) v.2.2 hr
  have hne : C.text g ≠ fun x => C.text d.1 (x+R.offset) := by
    have hh := (PeriodWord.different_iff D.1 (UpperCode.lookup (book X) (h.encode d)).1
      (RecordCode.offset v.2.2) (by rw [hp]; exact C.positive g)
      (by rw [(h.book_rep d).length_eq]; exact C.positive d.1)).mp hf
    simpa only [D,h.text_eq,(h.book_rep d).text_eq,R,RecordCode.checkedRecord] using hh
  let I := UpperCode.upper (C.size g) cut
  let lo := C.size g-v.1
  let hi := C.size g-1
  have hilo : lo ≤ hi := by dsimp [lo,hi]; omega
  have hm (i : ℕ) : i ∈ I ↔ cut ≤ i ∧ i < C.size g := UpperCode.mem_upper _ _ _
  have hlo : lo ∈ I := (hm _).mpr (by dsimp [lo]; omega)
  have hhi : hi ∈ I := (hm _).mpr (by dsimp [hi]; omega)
  have hlen : (I.filter (fun i => lessEq lo i)).length = v.1 := by
    rw [UpperCode.upper_filter (show cut ≤ lo from by dsimp [lo]; omega)]
    simp only [UpperCode.length_upper]
    dsimp only [lo]
    omega
  have hrep : ∀ i ∈ I, Represents D.1 (exits D i) (h.natLayer g i) :=
    fun i hi' => h.nat_rep g ((hm i).mp hi').2
  have hexit (i : ℕ) (hi' : i ∈ I) (x : ℤ) : GeoCode.exit (exits D i) x = (h.natLayer g i).z x :=
    congrFun (hrep i hi').exit_eq x
  have hh := DistributeCode.record_spec (h.natLayer g) (C.layerAt d) hrep closed
    (C.positive g) (C.positive d.1) (C.periodic g) (C.periodic d.1) (C.letters closed g)
    R hne (C.distinguished g) hat htb (C.distinguished_max g) hlo hhi hilo
    (fun i _ hil x => h.nat_order g hil x)
    (fun i hi' x => h.nat_order g (by have := (hm i).mp hi'; dsimp [hi]; omega) x)
    (by
      intro i hi' hil
      have hiF : i ∈ (UpperCode.upper (C.size g) cut).filter (fun i => decide (i < C.size g-v.1)) :=
        List.mem_filter.mpr ⟨hi',by simpa only [decide_eq_true_eq] using hil⟩
      have hh := of_decide_eq_true (List.all_eq_true.mp hfirst i hiF)
      change (h.natLayer g i).z (R.start-1) ≤ R.stop
      rw [← hexit i hi']
      exact hh)
    (by
      change (h.natLayer g hi).z (C.distinguished g-1) ≤ _
      rw [← hexit hi hhi,hlen,← hp]
      exact hH)
    (by
      change (h.natLayer g hi).z (C.distinguished g-1)-(h.natLayer g lo).z (C.distinguished g) ≤ _
      rw [← hexit hi hhi,← hexit lo hlo,hlen,← hp]
      exact hsharp)
    (ids X) (ls X) (owner X) (per X) (rank X) (h.per_eq g) (h.id_mem d)
    (by intro i hi'; exact owner_encode X _ _ (lt_of_lt_of_le ((hm i).mp hi').2 (h.capacity g)))
    (by rw [h.owner_eq,h.per_eq]) (h.rank_shift g d R.offset)
    ((h.content_iff d _).mpr ⟨R.start+R.offset,R.stop+R.offset,R.first_le,R.le_last,R.word_eq⟩)
    (by
      intro i hi' w hw
      let j : Fin (C.size g) := ⟨i,((hm i).mp hi').2⟩
      have hh := (h.content_iff ⟨g,j⟩ w).mp hw
      change w ∈ (C.layer g j).Content at hh
      have he : h.natLayer g i = C.layer g j := h.natLayer_fin g j
      rw [he]
      exact hh)
  dsimp only at hh ⊢
  have he : hard X (h.group g) cut v = DistributeCode.record D (h.group g) (h.encode d)
      (h.group g*stride X) I lo hi R.start R.stop (C.distinguished g) := by
    simp only [hard,h.size,h.phase_eq,hd,D,I,lo,hi,R,RecordCode.checkedRecord]
  rw [he]
  refine ⟨hh.1,?_,hh.2.2.1,?_,hh.2.2.2.2.1,d,R,hd,rfl,rfl,rfl,hne,hh.2.2.2.2.2⟩
  · simpa only [I,UpperCode.length_upper] using hh.2.1
  · intro i hi'
    exact hh.2.2.2.1 i.val ((hm i.val).mpr ⟨hi',i.isLt⟩)
end Model
end Superstring.CollectionCode


namespace Superstring.BitCode.Poly
variable {α β : Type} [Coded α] [Coded β] [Inhabited α] [Inhabited β]
@[fun_prop] theorem zip : Poly (fun p : List α × List β => p.1.zip p.2) := by
  have h : Poly (fun p : List α × List β =>
      (List.range (Min.min p.1.length p.2.length)).map
        (fun i => (p.1[i]?.getD default, p.2[i]?.getD default))) := by
    apply mapFn (f := fun q : (List α × List β) × ℕ =>
      (q.1.1[q.2]?.getD default, q.1.2[q.2]?.getD default))
    · exact ((getD default).comp
          (f := fun q : (List α × List β) × ℕ => (q.1.1,q.2)) (by fun_prop)).pair
        ((getD default).comp
          (f := fun q : (List α × List β) × ℕ => (q.1.2,q.2)) (by fun_prop))
    · fun_prop
  convert h using 1
  funext p
  apply List.ext_getElem
  · simp
  · intro i hi hi'
    have h₁ : i < p.1.length := by simp only [List.length_zip] at hi; omega
    have h₂ : i < p.2.length := by simp only [List.length_zip] at hi; omega
    simp only [List.getElem_zip,List.getElem_map,List.getElem_range,
      List.getElem?_eq_getElem h₁,List.getElem?_eq_getElem h₂,Option.getD_some]
end Superstring.BitCode.Poly
namespace Superstring.WindowCode
open Hierarchical WalkCode BitCode
variable {α : Type}
abbrev Window := ℤ × ℤ
def ordered (u v : Window) : Prop := u.1 ≤ v.1 ∧ u.2 ≤ v.2
def routeList (A : ℤ → α) (u : Window) (W : List Window) : Walk α :=
  [textWord A u.1 u.2] ++ (((u::W).zip W).flatMap fun q =>
    (route A q.1.1 q.1.2 q.2.1 q.2.2).tail)

theorem routeList_nil (A : ℤ → α) (u : Window) : routeList A u [] = [textWord A u.1 u.2] := rfl

theorem routeList_cons (A : ℤ → α) (u v : Window) (W : List Window)
    (hh : (route A u.1 u.2 v.1 v.2).head? = some (textWord A u.1 u.2)) :
    routeList A u (v::W) = join (route A u.1 u.2 v.1 v.2) (routeList A v W) := by
  unfold routeList
  simp only [List.zip_cons_cons,List.flatMap_cons,List.singleton_append,join,List.tail_cons]
  cases he : route A u.1 u.2 v.1 v.2 with
  | nil => simp [he] at hh
  | cons x xs =>
    have hx : x = textWord A u.1 u.2 := by simpa only [he,List.head?_cons,Option.some.injEq] using hh
    simp only [hx,List.tail_cons,List.cons_append]

theorem routeList_realizes {V : Set (List α)} (closed : SubstringClosed V)
    (A : ℤ → α) (letters : ∀ x, [A x] ∈ V) (u : Window) (W : List Window)
    (hchain : (u::W).Pairwise ordered)
    (hvalid : ∀ v ∈ u::W, v.1 ≤ v.2 ∧ textWord A v.1 v.2 ∈ V) :
    ∃ P : Hierarchical.Path V (textWord A u.1 u.2)
      (textWord A (W.getLastD u).1 (W.getLastD u).2),
      Path.points P = routeList A u W ∧ P.cost = ((W.getLastD u).2-u.2).toNat ∧
      ∀ v ∈ u::W, P.Visits (textWord A v.1 v.2) := by
  induction W generalizing u with
  | nil =>
    refine ⟨.nil _ (hvalid u (by simp)).2,rfl,?_,?_⟩
    · simp only [Hierarchical.Path.cost,List.getLastD_nil,sub_self,Int.toNat_zero]
    · intro v hv
      have he : v = u := List.mem_singleton.mp hv
      subst v
      exact Hierarchical.Path.visits_start _
  | cons v W ih =>
    obtain ⟨hfront,hrest⟩ := List.pairwise_cons.mp hchain
    have huv := hfront v (by simp)
    have hu := hvalid u (by simp)
    have hv := hvalid v (by simp)
    obtain ⟨P,hP,hcP,_,_⟩ := route_realizes closed A letters hu.1 hv.1 huv.1 huv.2 hu.2 hv.2
    obtain ⟨Q,hQ,hcQ,hvQ⟩ := ih v hrest (fun x hx => hvalid x (List.mem_cons_of_mem u hx))
    have hhead : (route A u.1 u.2 v.1 v.2).head? = some (textWord A u.1 u.2) := by
      rw [← hP]; exact (points_spec P).2.1
    have hlast : (v::W).getLastD u = W.getLastD v := by cases W <;> rfl
    have hend : v.2 ≤ (W.getLastD v).2 := by
      rcases List.mem_cons.mp (List.getLastD_mem_cons (l:=W) (a:=v)) with he | he
      · rw [he]
      · exact (List.pairwise_cons.mp hrest).1 _ he |>.2
    refine ⟨(P.trans Q).copy rfl (by rw [hlast]),?_,?_,?_⟩
    · rw [points_copy,Path.points,hP,hQ,routeList_cons A u v W hhead]
    · simp only [Hierarchical.Path.cost_copy,Hierarchical.Path.cost_trans,hcP,hcQ,hlast]
      have hh := huv.2
      omega
    · intro x hx
      apply (Hierarchical.Path.visits_copy ..).mpr
      rcases List.mem_cons.mp hx with rfl | hx
      · exact Or.inl (Hierarchical.Path.visits_start P)
      · exact Or.inr (hvQ x hx)

variable [Inhabited α] [Coded α]
@[fun_prop] theorem poly_routeList : Poly (fun q : List α × Window × List Window =>
    routeList (PeriodWord.text q.1) q.2.1 q.2.2) := by
  unfold routeList
  apply Poly.append.comp (f := fun q : List α × Window × List Window =>
    ([textWord (PeriodWord.text q.1) q.2.1.1 q.2.1.2],
      (((q.2.1::q.2.2).zip q.2.2).flatMap fun r =>
        (route (PeriodWord.text q.1) r.1.1 r.1.2 r.2.1 r.2.2).tail)))
  apply Poly.pair
  · simp_rw [← PeriodWord.window_eq]
    fun_prop
  · change Poly (fun q : List α × Window × List Window =>
      ((((q.2.1::q.2.2).zip q.2.2).map (fun r =>
        (route (PeriodWord.text q.1) r.1.1 r.1.2 r.2.1 r.2.2).tail))).flatten)
    apply Poly.flatten.comp
    apply Poly.mapFn (f := fun q : (List α × Window × List Window) × (Window × Window) =>
      (route (PeriodWord.text q.1.1) q.2.1.1 q.2.1.2 q.2.2.1 q.2.2.2).tail)
    · fun_prop
    · exact (BitCode.Poly.zip (α:=Window) (β:=Window)).comp
        (f := fun q : List α × Window × List Window => (q.2.1::q.2.2,q.2.2)) (by fun_prop)
end Superstring.WindowCode

end OAI
