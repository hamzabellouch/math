import OAI.Computability.Superstring.WalkCode

namespace OAI

namespace Superstring.ThreadArray
open BitCode Hierarchical
variable {α : Type} [Coded α] [DecidableEq α] [Inhabited α]

def aligned (K : Code α) (g : ℕ) : List ℕ :=
  (List.range K.1.length).filter (fun i => equal (key K i) (key K g))

@[fun_prop] theorem poly_aligned : Poly (fun q : Code α × ℕ => aligned q.1 q.2) := by
  unfold aligned
  exact BitCode.Poly.filterFn
    (p := fun q : (Code α × ℕ) × ℕ => equal (key q.1.1 q.2) (key q.1.1 q.1.2))
    (by fun_prop) (by fun_prop)

omit [Coded α] [DecidableEq α] [Inhabited α] in
theorem countP_range (n : ℕ) (P : ℕ → Bool) :
    (List.range n).countP P = (Finset.univ.filter (fun i : Fin n => P i.val)).card := by
  have he : List.range n = List.ofFn (fun i : Fin n => i.val) := by
    apply List.ext_getElem <;> simp
  rw [he, OrderStats.countP_ofFn, Finset.card_filter]

omit [Coded α] in
theorem aligned_length {K : Code α} {V : Set (List α)}
    {C : Threading V (Fin K.1.length)} (h : Represents K C) (g : Fin K.1.length) :
    (aligned K g.val).length = Fintype.card (C.Aligned (C.text g)) := by
  classical
  change (aligned K g.val).length = Fintype.card {i : Fin K.1.length // C.text i = C.text g}
  rw [Fintype.card_subtype]
  rw [aligned, ← List.countP_eq_length_filter, countP_range]
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro i _
  simp only [equal, decide_eq_true_eq, key_eq h, C.finiteKey_eq_iff]

omit [DecidableEq α] [Inhabited α] in
def atLength (K : Code α) (r i : ℕ) : ℕ :=
  ((K.1[ArrayPerm.power K.2 r i]?).getD []).length

omit [DecidableEq α] [Inhabited α] in
@[fun_prop] theorem poly_atLength : Poly (fun q : Code α × ℕ × ℕ => atLength q.1 q.2.1 q.2.2) := by
  unfold atLength
  exact BitCode.Poly.length.comp ((BitCode.Poly.getD ([] : List α)).comp
    (f := fun q : Code α × ℕ × ℕ => (q.1.1,ArrayPerm.power q.1.2 q.2.1 q.2.2)) (by fun_prop))

omit [Coded α] [DecidableEq α] [Inhabited α] in
theorem atLength_eq {K : Code α} {V : Set (List α)}
    {C : Threading V (Fin K.1.length)} (h : Represents K C) (r : ℕ) (i : Fin K.1.length) :
    atLength K r i.val = (C.word ((C.next ^ r) i)).length := by
  simp only [atLength, power_eq h, List.getElem?_eq_getElem (((C.next ^ r) i).isLt),
    Option.getD_some, ← h.word]

omit [DecidableEq α] [Inhabited α] in
theorem atLength_bound (K : Code α) (r i : ℕ) : atLength K r i ≤ bitSize K := by
  unfold atLength
  cases he : K.1[ArrayPerm.power K.2 r i]? with
  | none => simp
  | some w =>
    simp only [Option.getD_some]
    have hm : w ∈ K.1 := List.mem_of_getElem? he
    have hh := bitSize_mem hm
    have hl := length_le_bitSize w
    have hk : bitSize K = bitSize K.1 + bitSize K.2 := by cases K; exact bitSize_prod _ _
    omega

def rankLength (K : Code α) (g j r : ℕ) : ℕ :=
  first (bitSize K + 1) (fun l =>
    less j ((aligned K g).filter (fun i => lessEq (atLength K r i) l)).length)

@[fun_prop] theorem poly_rankLength : Poly (fun q : Code α × ℕ × ℕ × ℕ =>
    rankLength q.1 q.2.1 q.2.2.1 q.2.2.2) := by
  have hc : Poly (fun q : (Code α × ℕ × ℕ × ℕ) × ℕ =>
      ((aligned q.1.1 q.1.2.1).filter (fun i => lessEq (atLength q.1.1 q.1.2.2.2 i) q.2)).length) := by
    apply BitCode.Poly.length.comp
    exact BitCode.Poly.filterFn
      (p := fun q : ((Code α × ℕ × ℕ × ℕ) × ℕ) × ℕ =>
        lessEq (atLength q.1.1.1 q.1.1.2.2.2 q.2) q.1.2)
      (by fun_prop) (by fun_prop)
  unfold rankLength first
  exact (BitCode.Poly.headD 0).comp (BitCode.Poly.filterFn
    (p := fun q : (Code α × ℕ × ℕ × ℕ) × ℕ => less q.1.2.2.1
      ((aligned q.1.1 q.1.2.1).filter (fun i => lessEq (atLength q.1.1 q.1.2.2.2 i) q.2)).length)
    (by fun_prop) (by fun_prop))

noncomputable def lengthValues {K : Code α} {V : Set (List α)}
    (C : Threading V (Fin K.1.length)) (g : Fin K.1.length) (r : ℕ) :
    Fin (Fintype.card (C.Aligned (C.text g))) → ℕ :=
  fun j => (C.word ((C.next ^ r) (C.enumerate (C.text g) j).val)).length

omit [Coded α] in
theorem count_rank {K : Code α} {V : Set (List α)}
    {C : Threading V (Fin K.1.length)} (h : Represents K C)
    (g : Fin K.1.length) (r l : ℕ) :
    ((aligned K g.val).filter (fun i => lessEq (atLength K r i) l)).length =
      (Finset.univ.filter (fun j => lengthValues C g r j ≤ l)).card := by
  classical
  have he := Fintype.card_congr (Equiv.subtypeEquiv (C.enumerate (C.text g))
    (p := fun j => lengthValues C g r j ≤ l)
    (q := fun j => (C.word ((C.next ^ r) j.val)).length ≤ l) (fun _ => Iff.rfl))
  have he' := Fintype.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter
    (fun i : Fin K.1.length => C.text i = C.text g)
    (fun i => (C.word ((C.next ^ r) i)).length ≤ l))
  rw [Fintype.card_subtype] at he
  change Fintype.card {x : C.Aligned (C.text g) //
    (C.word ((C.next ^ r) x.val)).length ≤ l} = _ at he'
  rw [he,he',Fintype.card_subtype]
  rw [← List.countP_eq_length_filter, aligned, List.countP_filter, countP_range]
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro i _
  simp only [Bool.and_eq_true, lessEq, equal, decide_eq_true_eq, atLength_eq h,
    key_eq h, C.finiteKey_eq_iff, and_comm]

theorem rankLength_eq {K : Code α} {V : Set (List α)}
    {C : Threading V (Fin K.1.length)} (h : Represents K C)
    (g : Fin K.1.length) (j : Fin (Fintype.card (C.Aligned (C.text g)))) (r : ℕ) :
    rankLength K g.val j.val r = OrderStats.order (lengthValues C g r) j := by
  classical
  have hb : OrderStats.order (lengthValues C g r) j ≤ bitSize K := by
    obtain ⟨i, hi⟩ := OrderStats.order_mem (lengthValues C g r) j
    rw [← hi]
    change (C.word ((C.next ^ r) (C.enumerate (C.text g) i).val)).length ≤ _
    rw [← atLength_eq h]
    exact atLength_bound K r _
  have ht (l : ℕ) :
      less j.val ((aligned K g.val).filter (fun i => lessEq (atLength K r i) l)).length = true ↔
      OrderStats.order (lengthValues C g r) j ≤ l := by
    rw [count_rank h, less, decide_eq_true_eq, OrderStats.order_le_iff]
  have hs := first_spec (n := bitSize K+1)
    (P := fun l => less j.val ((aligned K g.val).filter (fun i => lessEq (atLength K r i) l)).length)
    ⟨OrderStats.order (lengthValues C g r) j, by omega, (ht _).mpr le_rfl⟩
  change rankLength K g.val j.val r < bitSize K+1 ∧ _ at hs
  exact le_antisymm (hs.2.2 _ (by omega) ((ht _).mpr le_rfl)) ((ht _).mp hs.2.1)

theorem sortedExit_eq_rank {K : Code α} {V : Set (List α)}
    {C : Threading V (Fin K.1.length)} (h : Represents K C)
    (g : Fin K.1.length) (j : Fin (Fintype.card (C.Aligned (C.text g)))) (r : ℕ) :
    C.sortedExit (C.text g) j (r : ℤ) = (r : ℤ) + rankLength K g.val j.val r := by
  rw [rankLength_eq h]
  have he : C.exits (C.text g) (r : ℤ) = fun i => (lengthValues C g r i : ℤ) + r := by
    funext i
    simp only [Threading.exits, lengthValues, zpow_natCast]
    omega
  change OrderStats.order (C.exits (C.text g) r) j = _
  rw [he, OrderStats.order_add, add_comm]
  congr 1
  have hh : OrderStats.order (fun i => (lengthValues C g r i : ℤ)) j =
      ((OrderStats.order (lengthValues C g r) j : ℕ) : ℤ) := by
    apply le_antisymm
    · rw [OrderStats.order_le_iff]
      convert (OrderStats.order_le_iff (lengthValues C g r) j _).mp le_rfl using 1
      simp only [Nat.cast_le]
    · obtain ⟨i,hi⟩ := OrderStats.order_mem (fun i => (lengthValues C g r i : ℤ)) j
      rw [← hi]
      norm_cast
      rw [OrderStats.order_le_iff]
      have hh := (OrderStats.order_le_iff (fun i => (lengthValues C g r i : ℤ)) j _).mp
        (le_of_eq hi.symm)
      simpa only [Nat.cast_le] using hh
  exact hh

end Superstring.ThreadArray

namespace Superstring.ThreadArray
open BitCode Hierarchical
variable {α : Type} [Coded α] [DecidableEq α] [Inhabited α]

def exit (K : Code α) (g j : ℕ) (x : ℤ) : ℤ :=
  x + rankLength K g j (x % (period K g : ℤ)).toNat

@[fun_prop] theorem poly_exit : Poly (fun q : Code α × ℕ × ℕ × ℤ =>
    exit q.1 q.2.1 q.2.2.1 q.2.2.2) := by
  have hm : Poly (fun q : Code α × ℕ × ℕ × ℤ =>
      (q.2.2.2 % (period q.1 q.2.1 : ℤ)).toNat) :=
    BitCode.Poly.modIntNat.comp (f := fun q : Code α × ℕ × ℕ × ℤ =>
      (q.2.2.2,period q.1 q.2.1)) (by fun_prop)
  unfold exit
  fun_prop

theorem exit_eq {K : Code α} {V : Set (List α)}
    {C : Threading V (Fin K.1.length)} (h : Represents K C) (closed : SubstringClosed V)
    (g : Fin K.1.length) (j : Fin (Fintype.card (C.Aligned (C.text g)))) (x : ℤ) :
    exit K g.val j.val x = (C.layer closed (period_spec h g).1.periodic j).z x := by
  let p := period K g.val
  let r := (x % (p : ℤ)).toNat
  have hp : 0 < p := (period_spec h g).1.positive
  have hr : (r : ℤ) = x % (p : ℤ) := Int.toNat_of_nonneg (Int.emod_nonneg x (by omega))
  have hx : x = (r : ℤ) + (x / (p : ℤ)) * p := by
    rw [hr]; exact (Int.emod_add_ediv_mul x p).symm
  have he := (C.layer closed (period_spec h g).1.periodic j).shift_int (x / p) r
  change C.sortedExit (C.text g) j ((r : ℤ) + (x / p) * p) =
    C.sortedExit (C.text g) j r + (x / p) * p at he
  rw [← hx, sortedExit_eq_rank h] at he
  change x + (rankLength K g.val j.val r : ℤ) = C.sortedExit (C.text g) j x
  omega

end Superstring.ThreadArray


namespace Superstring.WindowCode
open Hierarchical WalkCode
variable {α : Type}

def down (A : ℤ → α) (a b c : ℤ) : Walk α :=
  delete (textWord A a c) (textWord A c b)

def up (A : ℤ → α) (a b d : ℤ) : Walk α :=
  append (textWord A a b) (textWord A b d)

def route (A : ℤ → α) (a b c d : ℤ) : Walk α :=
  if c ≤ b then join (down A a b c) (up A c b d)
  else join (join (down A a b b) (gap (textWord A b c))) (up A c c d)

 theorem down_realizes {V : Set (List α)} (closed : SubstringClosed V)
    (A : ℤ → α) {a b c : ℤ} (hac : a ≤ c) (hcb : c ≤ b)
    (hw : textWord A a b ∈ V) :
    ∃ P : Hierarchical.Path V (textWord A a b) (textWord A c b),
      Path.points P = down A a b c ∧ P.cost = 0 ∧
      ∀ x, a ≤ x → x ≤ c → P.Visits (textWord A x b) := by
  have heq := textWord_append A hac hcb
  let D := Hierarchical.Path.deletePrefix closed (textWord A a c) (textWord A c b) (heq.symm ▸ hw)
  refine ⟨D.copy heq rfl,?_,by simp [D],?_⟩
  · simp only [points_copy,D,points_delete,down]
  · intro x hax hxc
    simp only [Hierarchical.Path.visits_copy]
    have heq' := textWord_append A hax hxc
    have hh : ∀ (u : List α) (h : u ++ textWord A c b ∈ V),
        u = textWord A a c →
        (Hierarchical.Path.deletePrefix closed u (textWord A c b) h).Visits (textWord A x b) →
        D.Visits (textWord A x b) := by
      intro u h he hv; subst u; exact hv
    apply hh _ _ heq'
    rw [← textWord_append A hxc hcb]
    exact Hierarchical.Path.deletePrefix_visits closed (textWord A a x)
      (textWord A x c) (textWord A c b) (by rw [heq',heq]; exact hw)

 theorem up_realizes {V : Set (List α)} (closed : SubstringClosed V)
    (A : ℤ → α) {a b d : ℤ} (hab : a ≤ b) (hbd : b ≤ d)
    (hw : textWord A a d ∈ V) :
    ∃ P : Hierarchical.Path V (textWord A a b) (textWord A a d),
      Path.points P = up A a b d ∧ P.cost = (d-b).toNat ∧
      ∀ y, b ≤ y → y ≤ d → P.Visits (textWord A a y) := by
  have heq := textWord_append A hab hbd
  let U := Hierarchical.Path.appendSuffix closed (textWord A a b) (textWord A b d) (heq.symm ▸ hw)
  refine ⟨U.copy rfl heq,?_,by simp [U],?_⟩
  · simp only [points_copy,U,points_append,up]
  · intro y hby hyd
    simp only [Hierarchical.Path.visits_copy]
    have heq' := textWord_append A hby hyd
    have hv := Hierarchical.Path.appendSuffix_visits closed (textWord A a b) (textWord A b y)
      (textWord A y d) (show textWord A a b ++ (textWord A b y ++ textWord A y d) ∈ V by
        rw [heq',heq]; exact hw)
    have hh : ∀ (b' : List α) (h : textWord A a b ++ b' ∈ V),
        b' = textWord A b d →
        (Hierarchical.Path.appendSuffix closed (textWord A a b) b' h).Visits (textWord A a y) →
        U.Visits (textWord A a y) := by
      intro b' h e hv'; subst b'; exact hv'
    apply hh _ _ heq'
    simpa only [textWord_append A hab hby] using hv

 theorem route_realizes {V : Set (List α)} (closed : SubstringClosed V)
    (A : ℤ → α) (letters : ∀ x, [A x] ∈ V)
    {a b c d : ℤ} (hab : a ≤ b) (hcd : c ≤ d) (hac : a ≤ c) (hbd : b ≤ d)
    (h₁ : textWord A a b ∈ V) (h₂ : textWord A c d ∈ V) :
    ∃ P : Hierarchical.Path V (textWord A a b) (textWord A c d),
      Path.points P = route A a b c d ∧ P.cost = (d-b).toNat ∧
      (∀ x, a ≤ x → x ≤ c → x ≤ b → P.Visits (textWord A x b)) ∧
      ∃ w, P.Visits w ∧ (w.length : ℤ) ≤ max 0 (b-c) := by
  by_cases hcb : c ≤ b
  · obtain ⟨D,hD,hDc,hDv⟩ := down_realizes closed A hac hcb h₁
    obtain ⟨U,hU,hUc,_⟩ := up_realizes closed A hcb hbd h₂
    refine ⟨D.trans U,?_,by simp [hDc,hUc],?_,textWord A c b,Or.inl (Hierarchical.Path.visits_end D),?_⟩
    · simp only [Path.points,hD,hU,route,ite_eq_left hcb]
    · exact fun x hax hxc _ => Or.inl (hDv x hax hxc)
    · simp only [length_textWord]; omega
  · have hbc : b ≤ c := by omega
    have h0 : ([] : List α) ∈ V := closed h₁ List.nil_infix
    obtain ⟨D,hD,hDc,hDv⟩ := down_realizes closed A hab le_rfl h₁
    obtain ⟨U,hU,hUc,_⟩ := up_realizes closed A (a := c) le_rfl hcd h₂
    let G := Hierarchical.Path.readGap h0 (textWord A b c) (by
      intro x hx
      obtain ⟨i,_,_,rfl⟩ := mem_textWord A hx
      exact letters i)
    let D' := D.copy rfl (textWord_self A b)
    let U' := U.copy (textWord_self A c) rfl
    refine ⟨(D'.trans G).trans U',?_,?_,?_,[],Or.inl (Or.inl (Hierarchical.Path.visits_end D')),by simp⟩
    · simp only [Path.points,D',U',points_copy,hD,hU,G,points_gap,route,ite_eq_right hcb]
    · simp only [Hierarchical.Path.cost_trans,D',U',Hierarchical.Path.cost_copy,hDc,hUc,
        G,Hierarchical.Path.cost_readGap,length_textWord]
      omega
    · intro x hax _ hxb
      exact Or.inl (Or.inl (by simpa [D'] using hDv x hax hxb))

end Superstring.WindowCode


namespace Superstring.BitCode.Poly
@[fun_prop] theorem leInt : Poly (fun q : ℤ × ℤ => decide (q.1 ≤ q.2)) := by
  have h : Poly (fun q : ℤ × ℤ => decide ((q.1-q.2).toNat = 0)) := by fun_prop
  convert h using 1
  funext q
  simp only [decide_eq_decide]
  omega
@[fun_prop] theorem ltInt : Poly (fun q : ℤ × ℤ => decide (q.1 < q.2)) := by
  have h : Poly (fun q : ℤ × ℤ => !(decide (q.2 ≤ q.1))) :=
    Poly.not.comp (leInt.comp (Poly.snd.pair Poly.fst))
  convert h using 1
  funext q
  by_cases hq : q.2 ≤ q.1
  · simp [hq,not_lt_of_ge hq]
  · simp [hq,lt_of_not_ge hq]
@[fun_prop] theorem maxInt : Poly (fun q : ℤ × ℤ => Max.max q.1 q.2) := by
  have h : Poly (fun q : ℤ × ℤ => if decide (q.1 ≤ q.2) then q.2 else q.1) := by fun_prop
  convert h using 1
  funext q
  by_cases hq : q.1 ≤ q.2
  · simp [hq]
  · simp [hq,max_eq_left (le_of_not_ge hq)]
@[fun_prop] theorem minInt : Poly (fun q : ℤ × ℤ => Min.min q.1 q.2) := by
  have h : Poly (fun q : ℤ × ℤ => if decide (q.1 ≤ q.2) then q.1 else q.2) := by fun_prop
  convert h using 1
  funext q
  by_cases hq : q.1 ≤ q.2
  · simp [hq]
  · simp [hq,min_eq_right (le_of_not_ge hq)]
end Superstring.BitCode.Poly

namespace Superstring.PeriodWord
open BitCode Hierarchical
variable {α : Type} [Inhabited α]

def text (U : List α) (x : ℤ) : α := U[(x % (U.length : ℤ)).toNat]?.getD default

def window (U : List α) (a b : ℤ) : List α :=
  (List.range (b-a).toNat).map (fun i : ℕ => text U (a + (i : ℤ)))

 theorem window_eq (U : List α) (a b : ℤ) : window U a b = textWord (text U) a b := by
  apply List.ext_getElem
  · simp only [window,textWord,List.length_map,List.length_range,List.length_ofFn]
  · intro i hi hi'
    simp only [window,textWord,List.getElem_map,List.getElem_range,List.getElem_ofFn]

 theorem periodic (U : List α) : Function.Periodic (text U) (U.length : ℤ) := by
  intro x
  simp [text]

 theorem eq_of_prefix (U : List α) (A : ℤ → α) (hp : 0 < U.length)
    (per : Function.Periodic A (U.length : ℤ))
    (h : ∀ i, (hi : i < U.length) → U[i] = A i) : text U = A := by
  funext x
  have hr : 0 ≤ x % (U.length : ℤ) := Int.emod_nonneg x (by omega)
  have hb : x % (U.length : ℤ) < U.length := Int.emod_lt_of_pos x (by omega)
  have hn : (x % (U.length : ℤ)).toNat < U.length := by omega
  simp only [text,List.getElem?_eq_getElem hn,Option.getD_some,h]
  rw [Int.toNat_of_nonneg hr]
  exact periodic_emod A U.length per x

variable [Coded α]
@[fun_prop] theorem poly_text : Poly (fun q : List α × ℤ => text q.1 q.2) := by
  unfold text
  exact (BitCode.Poly.getD default).comp
    (BitCode.Poly.fst.pair (BitCode.Poly.modIntNat.comp
      (f := fun q : List α × ℤ => (q.2,q.1.length)) (by fun_prop)))

@[fun_prop] theorem poly_window : Poly (fun q : List α × ℤ × ℤ => window q.1 q.2.1 q.2.2) := by
  unfold window
  exact BitCode.Poly.mapFn
    (f := fun q : (List α × ℤ × ℤ) × ℕ => text q.1.1 (q.1.2.1+q.2))
    (by fun_prop) (show Poly (fun q : List α × ℤ × ℤ => List.range (q.2.2-q.2.1).toNat) from by fun_prop)

@[fun_prop] theorem poly_textWord : Poly (fun q : List α × ℤ × ℤ =>
    textWord (text q.1) q.2.1 q.2.2) := by
  simpa only [window_eq] using (poly_window (α := α))

end Superstring.PeriodWord

end OAI
