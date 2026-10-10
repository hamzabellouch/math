import OAI.Computability.Superstring.FactoryPoly

namespace OAI

namespace Superstring.DistributeCode
open BitCode Hierarchical WalkCode LayerArray BlockClose
variable {α : Type} [Inhabited α] [DecidableEq α]
abbrev Result (α : Type) := Walk α × List (BlockClose.Block α) × List ℕ

def one (D : GroupData α) (src tar off i : ℕ) (a b : ℤ) : Result α :=
  if hasShort D i then (shortLoop D i,[],[])
  else if decide (b ≤ GeoCode.exit (exits D i) a+D.1.length) then
    ([[]],[BlockFactory.individual D src tar off i a b],[])
  else ([[]],[],[i])

def budget (o : Result α) (p : ℕ) : ℕ :=
  cost o.1+(o.2.1.map Block.reserve).sum+2*(o.2.2.length*p)
def combine (x y : Result α) : Result α :=
  (join x.1 y.1,x.2.1++y.2.1,x.2.2++y.2.2)
def many (D : GroupData α) (src tar off : ℕ) (I : List ℕ) (a b : ℤ) : Result α :=
  let os := I.map (fun i => one D src tar off i a b)
  (collect (os.map Prod.fst),os.flatMap (fun o => o.2.1),os.flatMap (fun o => o.2.2))

variable [LinearOrder α]
theorem one_spec {V : Set (List α)} {A B : ℤ → α} {p q : ℕ}
    (L : ℕ → Layer V A p) (T : Layer V B q) {D : GroupData α} {i src tar off : ℕ}
    (h : Represents D.1 (exits D i) (L i)) (closed : SubstringClosed V)
    (hp : 0 < p) (hq : 0 < q) (perA : Function.Periodic A (p : ℤ))
    (perB : Function.Periodic B (q : ℤ)) (letters : ∀ x, [A x] ∈ V)
    (R : T.Record A) (hne : A ≠ fun x => B (x+R.offset))
    (hf : (L i).first R.start ≤ R.stop)
    (ids : List ℕ) (ls : ℕ → Walk α) (owner periods : ℕ → ℕ) (rank : ℕ → Lex (ℕ → α))
    (hsrc : periods src = p) (htar : tar ∈ ids) (hown : owner (off+i) = src)
    (htper : periods (owner tar) = q)
    (hrec : textWord A R.start R.stop ∈ ls tar)
    (hlayers : ∀ w ∈ ls (off+i), w ∈ (L i).Content) :
    let o := one D src tar off i R.start R.stop
    Runs V [] [] o.1 ∧ budget o p ≤ 2*p ∧
      (∀ b ∈ o.2.1, ValidBlock V ids ls owner periods rank b) ∧
      ((∀ w ∈ ls (off+i), w ∈ o.1) ∨ (∃ b ∈ o.2.1, off+i ∈ b.members) ∨ i ∈ o.2.2) ∧
      o.2.2.Sublist [i] ∧
      ∀ j ∈ o.2.2, R.start+p < (L j).first R.start ∧ (L j).last R.start < R.stop-p := by
  dsimp only
  have h0 : ([] : List α) ∈ V := closed (letters 0) List.nil_infix
  have hroot : Runs V [] [] ([[]] : Walk α) := ⟨valid_nil [] h0,rfl,rfl⟩
  by_cases hs : hasShort D i = true
  · rw [one,ite_eq_left hs]
    obtain ⟨hr,hc,hv⟩ := shortLoop_spec L h closed hp perA hs
    exact ⟨hr,by simpa [budget] using hc,by simp,Or.inl (fun w hw => hv w (hlayers w hw)),by simp,by simp⟩
  · rw [one,ite_eq_right hs]
    by_cases ht : decide (R.stop ≤ GeoCode.exit (exits D i) R.start+D.1.length) = true
    · rw [ite_eq_left ht]
      have ht' : R.stop ≤ (L i).last R.start+p := by
        simpa only [h.exit_eq,h.length_eq,decide_eq_true_eq,Layer.last] using ht
      have hb := BlockFactory.individual_valid L T h closed hp hq perA perB letters R hne hf ht'
        ids ls owner periods rank hsrc htar hown htper
        (by intro he; rw [he,hsrc] at htper; exact htper) hrec hlayers
      refine ⟨hroot,?_,?_,Or.inr (Or.inl ⟨_,List.mem_singleton_self _,?_⟩),by simp,by simp⟩
      · simp [budget,BlockFactory.individual,BlockFactory.pack,Block.reserve,h.length_eq]
      · intro b hb'; have := List.mem_singleton.mp hb'; subst b; exact hb
      · simp [BlockFactory.individual,BlockFactory.pack,Block.members]
    · rw [ite_eq_right ht]
      have hn : ¬ (L i).HasShort p := fun hx => hs ((hasShort_eq h hp perA).mpr hx)
      have hl := (L i).first_long_of_not_short p hn R.start
      have ht' : (L i).last R.start+p < R.stop := by
        simp only [h.exit_eq,h.length_eq,decide_eq_true_eq] at ht
        change (L i).z R.start+p < R.stop
        omega
      refine ⟨hroot,by simp [budget],by simp,Or.inr (Or.inr (by simp)),List.Sublist.refl _,?_⟩
      intro j hj; have := List.mem_singleton.mp hj; subst j
      exact ⟨by omega,by omega⟩

omit [DecidableEq α] [Inhabited α] [LinearOrder α] in
theorem combine_budget (x y : Result α) (p : ℕ) {V : Set (List α)}
    (hx : Runs V [] [] x.1) (hy : Runs V [] [] y.1) :
    budget (combine x y) p = budget x p+budget y p := by
  simp only [budget,combine,cost_join _ _ _ hx.2.2 hy.2.1,List.map_append,List.sum_append,List.length_append]
  ring

omit [DecidableEq α] [Inhabited α] [LinearOrder α] in
theorem gather_budget {V : Set (List α)} (h0 : ([] : List α) ∈ V)
    (os : List (Result α)) (hr : ∀ o ∈ os, Runs V [] [] o.1) (p : ℕ) :
    budget (collect (os.map Prod.fst),os.flatMap (fun o => o.2.1),os.flatMap (fun o => o.2.2)) p =
      (os.map (fun o => budget o p)).sum := by
  have hh := collect_spec h0 (os.map Prod.fst) (by
    intro P hP; obtain ⟨o,ho,rfl⟩ := List.mem_map.mp hP; exact hr o ho)
  simp only [budget,hh.2.1,List.map_map]
  clear hh hr
  induction os with
  | nil => simp
  | cons o os ih =>
    simp only [List.map_cons,List.sum_cons,List.flatMap_cons,List.map_append,List.sum_append,
      List.length_append,Function.comp_apply,Nat.add_mul,Nat.mul_add]
    omega

omit [LinearOrder α] [Inhabited α] [DecidableEq α] in
theorem flatMap_sublist (I : List ℕ) (f : ℕ → List ℕ)
    (h : ∀ i ∈ I, (f i).Sublist [i]) : (I.flatMap f).Sublist I := by
  induction I with
  | nil => exact .refl _
  | cons i I ih =>
    simpa only [List.flatMap_cons,List.singleton_append] using
      (h i (List.mem_cons_self ..)).append (ih (fun j hj => h j (List.mem_cons_of_mem _ hj)))

theorem many_spec {V : Set (List α)} {A B : ℤ → α} {p q : ℕ}
    (L : ℕ → Layer V A p) (T : Layer V B q) {D : GroupData α} {I : List ℕ} {src tar off : ℕ}
    (h : ∀ i ∈ I, Represents D.1 (exits D i) (L i)) (closed : SubstringClosed V)
    (hp : 0 < p) (hq : 0 < q) (perA : Function.Periodic A (p : ℤ))
    (perB : Function.Periodic B (q : ℤ)) (letters : ∀ x, [A x] ∈ V)
    (R : T.Record A) (hne : A ≠ fun x => B (x+R.offset))
    (hf : ∀ i ∈ I, (L i).first R.start ≤ R.stop)
    (ids : List ℕ) (ls : ℕ → Walk α) (owner periods : ℕ → ℕ) (rank : ℕ → Lex (ℕ → α))
    (hsrc : periods src = p) (htar : tar ∈ ids) (hown : ∀ i ∈ I, owner (off+i) = src)
    (htper : periods (owner tar) = q) (hrec : textWord A R.start R.stop ∈ ls tar)
    (hlayers : ∀ i ∈ I, ∀ w ∈ ls (off+i), w ∈ (L i).Content) :
    let o := many D src tar off I R.start R.stop
    Runs V [] [] o.1 ∧ budget o p ≤ 2*(I.length*p) ∧
      (∀ b ∈ o.2.1, ValidBlock V ids ls owner periods rank b) ∧
      (∀ i ∈ I, (∀ w ∈ ls (off+i), w ∈ o.1) ∨ (∃ b ∈ o.2.1, off+i ∈ b.members) ∨ i ∈ o.2.2) ∧
      o.2.2.Sublist I ∧
      ∀ j ∈ o.2.2, R.start+p < (L j).first R.start ∧ (L j).last R.start < R.stop-p := by
  let f := fun i => one D src tar off i R.start R.stop
  have hh := fun i hi => one_spec L T (h i hi) closed hp hq perA perB letters R hne (hf i hi)
    ids ls owner periods rank hsrc htar (hown i hi) htper hrec (hlayers i hi)
  have h0 : ([] : List α) ∈ V := closed (letters 0) List.nil_infix
  have hr : ∀ o ∈ I.map f, Runs V [] [] o.1 := by
    intro o ho; obtain ⟨i,hi,rfl⟩ := List.mem_map.mp ho; exact (hh i hi).1
  have hc := collect_spec h0 ((I.map f).map Prod.fst) (by
    intro P hP; obtain ⟨o,ho,rfl⟩ := List.mem_map.mp hP; exact hr o ho)
  change Runs V [] [] (collect ((I.map f).map Prod.fst)) ∧ _
  refine ⟨hc.1,?_,?_,?_,?_,?_⟩
  · change budget (collect ((I.map f).map Prod.fst),(I.map f).flatMap (fun o => o.2.1),(I.map f).flatMap (fun o => o.2.2)) p ≤ _
    rw [gather_budget h0 (I.map f) hr p,List.map_map]
    have hb : (I.map (fun i => budget (f i) p)).sum ≤ (I.map (fun _ => 2*p)).sum :=
      List.sum_le_sum (fun i hi => (hh i hi).2.1)
    exact hb.trans_eq (by simp [List.sum_replicate]; ring)
  · intro b hb
    obtain ⟨o,ho,hb⟩ := List.mem_flatMap.mp hb
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp ho
    exact (hh i hi).2.2.1 b hb
  · intro i hi
    rcases (hh i hi).2.2.2.1 with hv|⟨b,hb,hm⟩|ha
    · exact Or.inl (fun w hw => hc.2.2 (f i).1 (List.mem_map.mpr ⟨f i,List.mem_map.mpr ⟨i,hi,rfl⟩,rfl⟩) w (hv w hw))
    · exact Or.inr (Or.inl ⟨b,List.mem_flatMap.mpr ⟨f i,List.mem_map.mpr ⟨i,hi,rfl⟩,hb⟩,hm⟩)
    · exact Or.inr (Or.inr (List.mem_flatMap.mpr ⟨f i,List.mem_map.mpr ⟨i,hi,rfl⟩,ha⟩))
  · change ((I.map f).flatMap _).Sublist I
    rw [List.flatMap_map]
    exact flatMap_sublist I _ (fun i hi => (hh i hi).2.2.2.2.1)
  · intro j hj
    obtain ⟨o,ho,hj⟩ := List.mem_flatMap.mp hj
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp ho
    exact (hh i hi).2.2.2.2.2 j hj

variable [Coded α]
instance codedResult : Coded (Result α) := codedProd
abbrev OneInput (α : Type) := (GroupData α × ℕ × ℕ × ℕ) × (ℕ × ℤ × ℤ)
instance codedOneInput : Coded (OneInput α) := codedProd
omit [LinearOrder α] in
@[fun_prop] theorem poly_one : Poly (fun q : OneInput α => one q.1.1 q.1.2.1 q.1.2.2.1 q.1.2.2.2 q.2.1 q.2.2.1 q.2.2.2) := by
  unfold one
  fun_prop
omit [LinearOrder α] [Inhabited α] [DecidableEq α] in
@[fun_prop] theorem poly_budget : Poly (fun q : Result α × ℕ => budget q.1 q.2) := by
  unfold budget
  have hs : Poly (fun q : Result α × ℕ => (q.1.2.1.map Block.reserve).sum) := poly_reserves.comp (by fun_prop)
  fun_prop
omit [LinearOrder α] in
@[fun_prop] theorem poly_many : Poly (fun q : (GroupData α × ℕ × ℕ × ℕ) × (List ℕ × ℤ × ℤ) =>
    many q.1.1 q.1.2.1 q.1.2.2.1 q.1.2.2.2 q.2.1 q.2.2.1 q.2.2.2) := by
  have hm : Poly (fun q : (GroupData α × ℕ × ℕ × ℕ) × (List ℕ × ℤ × ℤ) =>
      q.2.1.map (fun i => one q.1.1 q.1.2.1 q.1.2.2.1 q.1.2.2.2 i q.2.2.1 q.2.2.2)) := by
    exact BitCode.Poly.mapFn
      (f := fun q : ((GroupData α × ℕ × ℕ × ℕ) × (List ℕ × ℤ × ℤ)) × ℕ =>
        one q.1.1.1 q.1.1.2.1 q.1.1.2.2.1 q.1.1.2.2.2 q.2 q.1.2.2.1 q.1.2.2.2)
      (poly_one.comp (f := fun q : ((GroupData α × ℕ × ℕ × ℕ) × (List ℕ × ℤ × ℤ)) × ℕ =>
        (q.1.1,(q.2,q.1.2.2))) (by fun_prop)) (by fun_prop)
  unfold many
  have h1 : Poly (fun os : List (Result α) => collect (os.map Prod.fst)) :=
    poly_collect.comp (BitCode.Poly.mapFn (f := fun q : List (Result α) × Result α => q.2.1) (by fun_prop) (by fun_prop))
  have h2 : Poly (fun os : List (Result α) => os.flatMap (fun o => o.2.1)) :=
    BitCode.Poly.flatMapFn (f := fun q : List (Result α) × Result α => q.2.2.1) (by fun_prop) (by fun_prop)
  have h3 : Poly (fun os : List (Result α) => os.flatMap (fun o => o.2.2)) :=
    BitCode.Poly.flatMapFn (f := fun q : List (Result α) × Result α => q.2.2.2) (by fun_prop) (by fun_prop)
  exact (h1.pair (h2.pair h3)).comp hm
end Superstring.DistributeCode


namespace Superstring.LayerArray
open BitCode Hierarchical WalkCode
variable {α : Type} [Inhabited α] [DecidableEq α]
def belowLoop (D : GroupData α) (i : ℕ) (a b : ℤ) : Walk α :=
  if hasShort D i then shortLoop D i else individual D i a b
def below (D : GroupData α) (I : List ℕ) (P : Walk α) (a b : ℤ) : Walk α :=
  fill P (I.map (fun i => belowLoop D i a b))

theorem belowLoop_spec {V : Set (List α)} {A : ℤ → α} {p : ℕ}
    (L : ℕ → Layer V A p) {D : GroupData α} {i base : ℕ}
    (h : Represents D.1 (exits D i) (L i)) (closed : SubstringClosed V)
    (hp : 0 < p) (per : Function.Periodic A (p : ℤ)) (letters : ∀ x, [A x] ∈ V)
    {P : Walk α} (hP : Runs V [] [] P)
    (hcover : ∀ w ∈ (L base).Content, w ∈ P)
    (hbelow : ∀ x, (L i).z x ≤ (L base).z x)
    {a b : ℤ} (hbf : (L base).first a ≤ b) (hbl : b ≤ (L base).last a)
    (hlen : b-a < 2*p) :
    (∃ u, Runs V u u (belowLoop D i a b)) ∧ cost (belowLoop D i a b) ≤ 2*p ∧
      (∀ w ∈ (L i).Content, w ∈ belowLoop D i a b) ∧
      ∃ w, w ∈ P ∧ w ∈ belowLoop D i a b := by
  by_cases hs : hasShort D i = true
  · rw [belowLoop,ite_eq_left hs]
    obtain ⟨hr,hc,hv⟩ := shortLoop_spec L h closed hp per hs
    exact ⟨⟨[],hr⟩,hc,hv,[],List.mem_of_head? hP.2.1,List.mem_of_head? hr.2.1⟩
  · rw [belowLoop,ite_eq_right hs]
    have hn : ¬ (L i).HasShort p := fun hh => hs ((hasShort_eq h hp per).mpr hh)
    have hl := (L i).first_long_of_not_short p hn a
    have hf : (L i).first a ≤ b := (hbelow (a-1)).trans hbf
    have hfl := (L i).first_le_last a
    obtain ⟨hr,hc,hv,hw,_⟩ := individual_spec L h closed hp per letters p
      ((L base).start_le_first a |>.trans hbf) ((L base).actual a b hbf hbl) hf (by omega) (by omega)
    exact ⟨⟨_,hr⟩,hc.le,hv,_,hcover _ ⟨a,b,hbf,hbl,rfl⟩,hw⟩

theorem below_spec {V : Set (List α)} {A : ℤ → α} {p : ℕ}
    (L : ℕ → Layer V A p) {D : GroupData α} {I : List ℕ} {base : ℕ}
    (h : ∀ i ∈ I, Represents D.1 (exits D i) (L i)) (closed : SubstringClosed V)
    (hp : 0 < p) (per : Function.Periodic A (p : ℤ)) (letters : ∀ x, [A x] ∈ V)
    {P : Walk α} (hP : Runs V [] [] P)
    (hcover : ∀ w ∈ (L base).Content, w ∈ P)
    (hbelow : ∀ i ∈ I, ∀ x, (L i).z x ≤ (L base).z x)
    {a b : ℤ} (hbf : (L base).first a ≤ b) (hbl : b ≤ (L base).last a)
    (hlen : b-a < 2*p) :
    Runs V [] [] (below D I P a b) ∧ cost (below D I P a b) ≤ cost P+2*(I.length*p) ∧
      (∀ w ∈ P, w ∈ below D I P a b) ∧
      ∀ i ∈ I, ∀ w ∈ (L i).Content, w ∈ below D I P a b := by
  have hh := fun i hi => belowLoop_spec L (h i hi) closed hp per letters hP hcover (hbelow i hi) hbf hbl hlen
  obtain ⟨hr,hc,hv⟩ := fill_spec P (I.map (fun i => belowLoop D i a b)) hP
    (by intro Q hQ; obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hQ; exact (hh i hi).1)
    (by intro Q hQ; obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hQ; exact (hh i hi).2.2.2)
  refine ⟨hr,?_,fun w hw => (hv w).mpr (Or.inl hw),?_⟩
  · change cost (fill P _) ≤ _
    rw [hc,List.map_map]
    have hb := List.sum_le_sum (g := fun _ : ℕ => 2*p) (fun i hi => (hh i hi).2.1)
    have he : (I.map (fun _ => 2*p)).sum = 2*(I.length*p) := by simp [List.sum_replicate]; ring
    rw [he] at hb
    exact Nat.add_le_add_left hb _
  · intro i hi w hw
    exact (hv w).mpr (Or.inr ⟨_,List.mem_map.mpr ⟨i,hi,rfl⟩,(hh i hi).2.2.1 w hw⟩)

variable [Coded α]
@[fun_prop] theorem poly_belowLoop : Poly (fun q : GroupData α × ℕ × ℤ × ℤ =>
    belowLoop q.1 q.2.1 q.2.2.1 q.2.2.2) := by
  unfold belowLoop
  fun_prop
@[fun_prop] theorem poly_below : Poly (fun q : (GroupData α × List ℕ) × Walk α × ℤ × ℤ =>
    below q.1.1 q.1.2 q.2.1 q.2.2.1 q.2.2.2) := by
  unfold below
  have hm : Poly (fun q : (GroupData α × List ℕ) × Walk α × ℤ × ℤ =>
      q.1.2.map (fun i => belowLoop q.1.1 i q.2.2.1 q.2.2.2)) :=
    BitCode.Poly.mapFn (f := fun q : ((GroupData α × List ℕ) × Walk α × ℤ × ℤ) × ℕ =>
      belowLoop q.1.1.1 q.2 q.1.2.2.1 q.1.2.2.2) (by fun_prop) (by fun_prop)
  fun_prop
end Superstring.LayerArray


namespace Superstring.DistributeCode
open BitCode Hierarchical WalkCode LayerArray BlockClose
variable {α : Type} [Inhabited α] [DecidableEq α]
def record (D : GroupData α) (src tar off : ℕ) (I : List ℕ) (lo hi : ℕ) (a b t : ℤ) : Result α :=
  let J := I.filter (fun i => lessEq lo i)
  if decide (b ≤ GeoCode.exit (exits D lo) a+(J.length*D.1.length : ℕ)) then
    let o := many D src tar off (I.filter (fun i => !lessEq lo i)) a b
    (o.1,BlockFactory.collective D src tar off J lo hi a b t::o.2.1,o.2.2)
  else many D src tar off I a b

variable [LinearOrder α]
theorem record_spec {V : Set (List α)} {A B : ℤ → α} {p q : ℕ}
    (L : ℕ → Layer V A p) (T : Layer V B q) {D : GroupData α} {I : List ℕ} {src tar off lo hi : ℕ}
    (h : ∀ i ∈ I, Represents D.1 (exits D i) (L i)) (closed : SubstringClosed V)
    (hp : 0 < p) (hq : 0 < q) (perA : Function.Periodic A (p : ℤ))
    (perB : Function.Periodic B (q : ℤ)) (letters : ∀ x, [A x] ∈ V)
    (R : T.Record A) (hne : A ≠ fun x => B (x+R.offset))
    (t : ℤ) (hat : R.start ≤ t) (htb : t < R.stop)
    (hmax : ∀ x, forward A x ≤ forward A t)
    (hlo : lo ∈ I) (hhi : hi ∈ I) (hlohi : lo ≤ hi)
    (lower : ∀ i ∈ I, lo ≤ i → ∀ x, (L lo).z x ≤ (L i).z x)
    (upper : ∀ i ∈ I, ∀ x, (L i).z x ≤ (L hi).z x)
    (hfirst : ∀ i ∈ I, i < lo → (L i).first R.start ≤ R.stop)
    (hH : (L hi).first t ≤ R.stop+((I.filter (fun i => lessEq lo i)).length*p : ℕ))
    (hsharp : (L hi).first t-(L lo).last t ≤ (((I.filter (fun i => lessEq lo i)).length-1)*p : ℕ))
    (ids : List ℕ) (ls : ℕ → Walk α) (owner periods : ℕ → ℕ) (rank : ℕ → Lex (ℕ → α))
    (hsrc : periods src = p) (htar : tar ∈ ids) (hown : ∀ i ∈ I, owner (off+i) = src)
    (htper : periods (owner tar) = q)
    (hrank : rank (owner tar) ≤ rank src → ∀ x, forward (fun x => B (x+R.offset)) x ≤ forward A t)
    (hrec : textWord A R.start R.stop ∈ ls tar)
    (hlayers : ∀ i ∈ I, ∀ w ∈ ls (off+i), w ∈ (L i).Content) :
    let o := record D src tar off I lo hi R.start R.stop t
    Runs V [] [] o.1 ∧ budget o p ≤ 2*(I.length*p) ∧
      (∀ b ∈ o.2.1, ValidBlock V ids ls owner periods rank b) ∧
      (∀ i ∈ I, (∀ w ∈ ls (off+i), w ∈ o.1) ∨ (∃ b ∈ o.2.1, off+i ∈ b.members) ∨ i ∈ o.2.2) ∧
      o.2.2.Sublist I ∧
      ∀ j ∈ o.2.2, R.start+p < (L j).first R.start ∧ (L j).last R.start < R.stop-p := by
  let J := I.filter (fun i => lessEq lo i)
  let F := I.filter (fun i => !lessEq lo i)
  have hJ : ∀ i, i ∈ J ↔ i ∈ I ∧ lo ≤ i := by intro i; simp [J,lessEq]
  have hF : ∀ i, i ∈ F ↔ i ∈ I ∧ i < lo := by intro i; simp [F,lessEq]
  have hloJ : lo ∈ J := (hJ lo).mpr ⟨hlo,le_rfl⟩
  have hhiJ : hi ∈ J := (hJ hi).mpr ⟨hhi,hlohi⟩
  have hk : 0 < J.length := List.length_pos_of_mem hloJ
  have hgap := Processing.wide_band (L hi) (L lo) hp hk t hsharp R.start
  by_cases hc : decide (R.stop ≤ GeoCode.exit (exits D lo) R.start+(J.length*D.1.length : ℕ)) = true
  · change _ ∧ _
    simp only [record,show I.filter (fun i => lessEq lo i) = J from rfl,ite_eq_left hc]
    have hb : R.stop ≤ (L lo).last R.start+(J.length*p : ℕ) := by
      simpa only [(h lo hlo).exit_eq,(h lo hlo).length_eq,Layer.last,decide_eq_true_eq] using hc
    have hblock := BlockFactory.collective_valid L T (D:=D) (js:=J)
      (fun i hi => h i ((hJ i).mp hi).1) hloJ hhiJ
      (fun i hi => lower i ((hJ i).mp hi).1 ((hJ i).mp hi).2)
      (fun i hi => upper i ((hJ i).mp hi).1) closed hp hq perA perB letters R hne t hat htb
      hmax hH hgap hb hsharp ids ls owner periods rank hsrc htar
      (fun i hi => hown i ((hJ i).mp hi).1) htper
      (by intro he; rw [he,hsrc] at htper; exact htper) hrank hrec
      (fun i hi => hlayers i ((hJ i).mp hi).1)
    obtain ⟨hr,hbudget,hblocks,hcov,hs,hm⟩ := many_spec L T (D:=D) (I:=F)
      (fun i hi => h i ((hF i).mp hi).1) closed hp hq perA perB letters R hne
      (fun i hi => hfirst i ((hF i).mp hi).1 ((hF i).mp hi).2)
      ids ls owner periods rank hsrc htar (fun i hi => hown i ((hF i).mp hi).1) htper hrec
      (fun i hi => hlayers i ((hF i).mp hi).1)
    refine ⟨hr,?_,?_,?_,hs.trans (List.filter_sublist),hm⟩
    · have he : F.length+J.length = I.length := by
        simpa only [F,J,Nat.add_comm] using (List.length_eq_length_filter_add (l:=I) (fun i => lessEq lo i)).symm
      have hbsize : (BlockFactory.collective D src tar off J lo hi R.start R.stop t).reserve = 2*(J.length*p) := by
        simp only [BlockFactory.collective,BlockFactory.pack,Block.reserve,(h lo hlo).length_eq]
      change cost _ + ((_ :: _).map Block.reserve).sum + _ ≤ _
      simp only [List.map_cons,List.sum_cons,hbsize]
      change cost _ + _ + _ ≤ _ at hbudget
      have ha : 2*(I.length*p) = 2*(F.length*p)+2*(J.length*p) := by rw [← he]; ring
      dsimp only [F] at hbudget ha
      omega
    · intro b hb'
      rcases List.mem_cons.mp hb' with rfl|hb'
      · exact hblock
      · exact hblocks b hb'
    · intro i hi
      by_cases hj : lo ≤ i
      · exact Or.inr (Or.inl ⟨_,List.mem_cons_self ..,List.mem_map.mpr ⟨i,(hJ i).mpr ⟨hi,hj⟩,rfl⟩⟩)
      · rcases hcov i ((hF i).mpr ⟨hi,by omega⟩) with hv|⟨b,hb,hm⟩|ha
        · exact Or.inl hv
        · exact Or.inr (Or.inl ⟨b,List.mem_cons_of_mem _ hb,hm⟩)
        · exact Or.inr (Or.inr ha)
  · simp only [record,show I.filter (fun i => lessEq lo i) = J from rfl,ite_eq_right hc]
    apply many_spec L T h closed hp hq perA perB letters R hne _ ids ls owner periods rank hsrc htar hown htper hrec hlayers
    intro i hmem
    have hb : (L lo).last R.start+(J.length*p : ℕ) < R.stop := by
      simp only [(h lo hlo).exit_eq,(h lo hlo).length_eq,decide_eq_true_eq] at hc
      change (L lo).z R.start+_ < _
      omega
    have hu := upper i hmem (R.start-1)
    change (L i).first R.start ≤ (L hi).first R.start at hu
    omega

variable [Coded α]
abbrev RecordInput (α : Type) := (GroupData α × ℕ × ℕ × ℕ) × (List ℕ × ℕ × ℕ) × (ℤ × ℤ × ℤ)
instance codedRecordInput : Coded (RecordInput α) := codedProd
omit [LinearOrder α] in
@[fun_prop] theorem poly_record : Poly (fun q : RecordInput α =>
    record q.1.1 q.1.2.1 q.1.2.2.1 q.1.2.2.2 q.2.1.1 q.2.1.2.1 q.2.1.2.2 q.2.2.1 q.2.2.2.1 q.2.2.2.2) := by
  have hj : Poly (fun q : RecordInput α => q.2.1.1.filter (fun i => lessEq q.2.1.2.1 i)) :=
    BitCode.Poly.filterFn (p := fun q : RecordInput α × ℕ => lessEq q.1.2.1.2.1 q.2) (by fun_prop) (by fun_prop)
  have hf : Poly (fun q : RecordInput α => q.2.1.1.filter (fun i => !lessEq q.2.1.2.1 i)) :=
    BitCode.Poly.filterFn (p := fun q : RecordInput α × ℕ => !lessEq q.1.2.1.2.1 q.2) (by fun_prop) (by fun_prop)
  have hc : Poly (fun q : RecordInput α => BlockFactory.collective q.1.1 q.1.2.1 q.1.2.2.1 q.1.2.2.2
      (q.2.1.1.filter (fun i => lessEq q.2.1.2.1 i)) q.2.1.2.1 q.2.1.2.2 q.2.2.1 q.2.2.2.1 q.2.2.2.2) :=
    BlockFactory.poly_collective.comp (f := fun q : RecordInput α =>
      (q.1,((q.2.1.1.filter (fun i => lessEq q.2.1.2.1 i)),q.2.1.2),q.2.2)) (by fun_prop)
  have hm : Poly (fun q : RecordInput α => many q.1.1 q.1.2.1 q.1.2.2.1 q.1.2.2.2
      (q.2.1.1.filter (fun i => !lessEq q.2.1.2.1 i)) q.2.2.1 q.2.2.2.1) :=
    poly_many.comp (f := fun q : RecordInput α =>
      (q.1,(q.2.1.1.filter (fun i => !lessEq q.2.1.2.1 i)),q.2.2.1,q.2.2.2.1)) (by fun_prop)
  have hm' : Poly (fun q : RecordInput α => many q.1.1 q.1.2.1 q.1.2.2.1 q.1.2.2.2 q.2.1.1 q.2.2.1 q.2.2.2.1) :=
    poly_many.comp (f := fun q : RecordInput α => (q.1,q.2.1.1,q.2.2.1,q.2.2.2.1)) (by fun_prop)
  unfold record
  dsimp only
  apply BitCode.Poly.ite
  · fun_prop
  · fun_prop
  · exact hm'
end Superstring.DistributeCode


namespace Superstring.LayerArray
open BitCode Hierarchical WalkCode
variable {α : Type} [Inhabited α] [DecidableEq α]
def attachBand (D : GroupData α) (I : List ℕ) (lo hi : ℕ) (P : Walk α) (t : ℤ) : Walk α :=
  splice P (band D I lo hi I.length t)

theorem band_general {V : Set (List α)} {A : ℤ → α} {p : ℕ}
    (L : ℕ → Layer V A p) {D : GroupData α} {I : List ℕ} {lo hi k : ℕ}
    (h : ∀ i ∈ I, Represents D.1 (exits D i) (L i))
    (hl : Represents D.1 (exits D lo) (L lo)) (hh : Represents D.1 (exits D hi) (L hi))
    (lower : ∀ i ∈ I, ∀ x, (L lo).z x ≤ (L i).z x)
    (upper : ∀ i ∈ I, ∀ x, (L i).z x ≤ (L hi).z x)
    (hlohi : ∀ x, (L lo).z x ≤ (L hi).z x)
    (closed : SubstringClosed V) (hp : 0 < p) (per : Function.Periodic A (p : ℤ))
    (letters : ∀ x, [A x] ∈ V) (t : ℤ)
    (hB : (L hi).first t-(L lo).last t ≤ (k*p : ℕ)) :
    Runs V (textWord A t ((L lo).last t)) (textWord A t ((L lo).last t)) (band D I lo hi k t) ∧
      cost (band D I lo hi k t) ≤ (k+I.length)*p ∧
      ∀ i ∈ I, ∀ w ∈ (L i).Content, w ∈ band D I lo hi k t := by
  let J := lo::hi::I
  have hloJ : lo ∈ J := List.mem_cons_self ..
  have hhiJ : hi ∈ J := List.mem_cons_of_mem _ (List.mem_cons_self ..)
  have hlow : ∀ i ∈ J, ∀ x, (L lo).z x ≤ (L i).z x := by
    intro i hi' x
    rcases List.mem_cons.mp hi' with rfl|hi'
    · exact le_rfl
    rcases List.mem_cons.mp hi' with rfl|hi'
    · exact hlohi x
    · exact lower i hi' x
  have hupp : ∀ i ∈ J, ∀ x, (L i).z x ≤ (L hi).z x := by
    intro i hi' x
    rcases List.mem_cons.mp hi' with rfl|hi'
    · exact hlohi x
    rcases List.mem_cons.mp hi' with rfl|hi'
    · exact le_rfl
    · exact upper i hi' x
  obtain ⟨Q,he,hc,ht⟩ := GeoCode.join_band_realizes closed A letters p k per
    (fun j : {j // j ∈ J} => L j.val) ⟨lo,hloJ⟩ ⟨hi,hhiJ⟩
    (fun j => hlow j.val j.property) (fun j => hupp j.val j.property) t hB
  have he' : WalkCode.Path.points Q = GeoCode.band (PeriodWord.text D.1)
      (GeoCode.exit (exits D lo)) (GeoCode.exit (exits D hi)) D.1.length k t := by
    rw [hh.text_eq,hl.exit_eq,hh.exit_eq,hh.length_eq]; exact he
  obtain ⟨hr,hc',_,hv⟩ := filled_realized L h closed hp per he'
    (fun i hi' => ht ⟨i,List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hi')⟩)
  refine ⟨hr,?_,hv⟩
  change cost (saturate D I _) ≤ _
  rw [hc',Nat.add_mul]
  omega

theorem attachBand_spec {V : Set (List α)} {A : ℤ → α} {p : ℕ}
    (L : ℕ → Layer V A p) {D : GroupData α} {I : List ℕ} {lo hi : ℕ}
    (h : ∀ i ∈ I, Represents D.1 (exits D i) (L i))
    (hl : Represents D.1 (exits D lo) (L lo)) (hh : Represents D.1 (exits D hi) (L hi))
    (lower : ∀ i ∈ I, ∀ x, (L lo).z x ≤ (L i).z x)
    (upper : ∀ i ∈ I, ∀ x, (L i).z x ≤ (L hi).z x)
    (hlohi : ∀ x, (L lo).z x ≤ (L hi).z x)
    (closed : SubstringClosed V) (hp : 0 < p) (per : Function.Periodic A (p : ℤ))
    (letters : ∀ x, [A x] ∈ V) (t : ℤ)
    (hB : (L hi).first t-(L lo).last t ≤ (I.length*p : ℕ))
    {P : Walk α} (hP : Runs V [] [] P) (hcP : ∀ w ∈ (L lo).Content, w ∈ P) :
    Runs V [] [] (attachBand D I lo hi P t) ∧ cost (attachBand D I lo hi P t) ≤ cost P+2*(I.length*p) ∧
      (∀ w ∈ P, w ∈ attachBand D I lo hi P t) ∧
      ∀ i ∈ I, ∀ w ∈ (L i).Content, w ∈ attachBand D I lo hi P t := by
  obtain ⟨hr,hc,hv⟩ := band_general L h hl hh lower upper hlohi closed hp per letters t hB
  have hm : textWord A t ((L lo).last t) ∈ P := hcP _ ⟨t,_,(L lo).first_le_last t,le_rfl,rfl⟩
  obtain ⟨hR,hc',hv'⟩ := splice_spec hP hr ⟨_,hm,List.mem_of_head? hr.2.1⟩
  refine ⟨hR,?_,fun w hw => (hv' w).mpr (Or.inl hw),fun i hi' w hw => (hv' w).mpr (Or.inr (hv i hi' w hw))⟩
  change cost (splice P _) ≤ _
  rw [hc']
  calc
    _ ≤ cost P+(I.length+I.length)*p := Nat.add_le_add_left hc _
    _ = _ := by ring

variable [Coded α]
@[fun_prop] theorem poly_attachBand : Poly (fun q : (GroupData α × List ℕ) × (ℕ × ℕ) × Walk α × ℤ =>
    attachBand q.1.1 q.1.2 q.2.1.1 q.2.1.2 q.2.2.1 q.2.2.2) := by
  unfold attachBand
  exact poly_splice.comp (f := fun q : (GroupData α × List ℕ) × (ℕ × ℕ) × Walk α × ℤ =>
    (q.2.2.1,band q.1.1 q.1.2 q.2.1.1 q.2.1.2 q.1.2.length q.2.2.2)) (by fun_prop)
end Superstring.LayerArray

end OAI
