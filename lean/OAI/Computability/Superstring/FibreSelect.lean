import OAI.Computability.Superstring.UpperController

namespace OAI

namespace Superstring.BitCode
variable {α : Type} [Inhabited α]
def firstGood (xs : List α) (test : α → Bool) : α := (xs.filter test).headD default
theorem firstGood_mem (xs : List α) (test : α → Bool) (hex : ∃ x ∈ xs, test x = true) :
    firstGood xs test ∈ xs ∧ test (firstGood xs test) = true := by
  have hn : xs.filter test ≠ [] := by
    obtain ⟨x,hx,ht⟩ := hex
    exact List.ne_nil_of_mem (List.mem_filter.mpr ⟨hx,ht⟩)
  have hm : firstGood xs test ∈ xs.filter test := by
    unfold firstGood
    cases he : xs.filter test with
    | nil => exact False.elim (hn he)
    | cons a as => exact List.mem_cons_self ..
  exact List.mem_filter.mp hm
end Superstring.BitCode
namespace Superstring.CollectionCode
open BitCode Hierarchical LayerArray WalkCode
variable {α G : Type} [Inhabited α] [LinearOrder α] {V : Set (List α)}
def fibreCheck (vs : Walk α) (X : Env α) (t : ℕ) (R : List Request) (P : Walk α) : Bool :=
  BlockClose.rootedCheck vs P && lessEq (cost P) (2*per X (owner X t)+(R.map (Request.reserve X)).sum) &&
    BlockClose.coversCheck (contents X) (t::R.flatMap (Request.ids X)) P
def fibreSelect (vs : Walk α) (X : Env α) (t : ℕ) (R : List Request) : Walk α :=
  firstGood (fibrePool X t R) (fibreCheck vs X t R)
namespace Model
theorem fibreSelect_spec (vs : Walk α) {X : Env α} {C : LayerCollection {w | w ∈ vs} G}
    (h : Model X C) (closed : SubstringClosed {w | w ∈ vs}) (d : C.Id) (R : List Request)
    (hne : R ≠ []) (valid : ∀ r ∈ R, ValidRequest h r)
    (target : ∀ r ∈ R, r.target = h.encode d) (distinct : SourcesDistinct R) :
    let P := fibreSelect vs X (h.encode d) R
    Runs {w | w ∈ vs} [] [] P ∧ cost P ≤ 2*C.period d.1+(R.map (Request.reserve X)).sum ∧
      (∀ w ∈ ls X (h.encode d), w ∈ P) ∧ ∀ r ∈ R, ∀ i ∈ r.ids X, ∀ w ∈ ls X i, w ∈ P := by
  have hex := h.fibrePool_complete closed d R hne valid target distinct
  have he (P : Walk α) : fibreCheck vs X (h.encode d) R P = true ↔
      Runs {w | w ∈ vs} [] [] P ∧ cost P ≤ 2*C.period d.1+(R.map (Request.reserve X)).sum ∧
        (∀ w ∈ ls X (h.encode d), w ∈ P) ∧ ∀ r ∈ R, ∀ i ∈ r.ids X, ∀ w ∈ ls X i, w ∈ P := by
    simp only [fibreCheck,Bool.and_eq_true,BlockClose.rootedCheck_eq,lessEq,decide_eq_true_eq,
      h.owner_eq,h.per_eq,BlockClose.coversCheck_eq,BlockClose.Covers,List.mem_cons,List.mem_flatMap]
    constructor
    · rintro ⟨⟨hr,hb⟩,hc⟩
      exact ⟨hr,hb,hc _ (Or.inl rfl),fun r hr i hi => hc _ (Or.inr ⟨r,hr,hi⟩)⟩
    · rintro ⟨hr,hb,hd,hcov⟩
      refine ⟨⟨hr,hb⟩,?_⟩
      intro i hi
      rcases hi with rfl|⟨r,hr,hi⟩
      · exact hd
      · exact hcov r hr i hi
  apply (he _).mp
  exact (firstGood_mem _ _ (by obtain ⟨P,hP,hs⟩ := hex; exact ⟨P,hP,(he P).mpr hs⟩)).2
end Model
variable [Coded α]
omit [Inhabited α] [LinearOrder α] in
@[fun_prop] theorem poly_request_reserve : Poly (fun q : Env α × Request => Request.reserve q.1 q.2) := by
  unfold Request.reserve Request.members Request.source
  fun_prop
omit [Inhabited α] [LinearOrder α] in
@[fun_prop] theorem poly_request_ids : Poly (fun q : Env α × Request => Request.ids q.1 q.2) := by
  unfold Request.ids Request.members Request.source
  exact BitCode.Poly.mapFn (f := fun q : (Env α × Request) × ℕ => q.1.2.1*stride q.1.1+q.2)
    (by unfold stride; fun_prop) (by fun_prop)
omit [LinearOrder α] in
@[fun_prop] theorem poly_request_entry : Poly (fun q : (Env α × Request) × ℕ => Request.entry q.1.1 q.1.2 q.2) := by
  unfold Request.entry Request.source Request.code RecordCode.offset RecordCode.start RecordCode.stop
  fun_prop
omit [LinearOrder α] in
@[fun_prop] theorem poly_entries : Poly (fun q : Env α × List Request => entries q.1 q.2) := by
  unfold entries
  apply BitCode.Poly.flatMapFn (f := fun q : (Env α × List Request) × Request => q.2.members.map (Request.entry q.1.1 q.2))
  · exact BitCode.Poly.mapFn (f := fun q : ((Env α × List Request) × Request) × ℕ =>
      Request.entry q.1.1.1 q.1.2 q.2)
      (poly_request_entry.comp (f := fun q : ((Env α × List Request) × Request) × ℕ =>
        ((q.1.1.1,q.1.2),q.2)) (by fun_prop)) (by unfold Request.members; fun_prop)
  · fun_prop
omit [Inhabited α] [LinearOrder α] in
@[fun_prop] theorem poly_requestedData : Poly (fun q : Env α × List Request => requestedData q.1 q.2) := by
  unfold requestedData
  apply BitCode.Poly.flatMapFn (f := fun q : (Env α × List Request) × Request =>
    (q.2.ids q.1.1).map (UpperCode.lookup (book q.1.1)))
  · exact BitCode.Poly.mapFn (f := fun q : ((Env α × List Request) × Request) × ℕ =>
      UpperCode.lookup (book q.1.1.1) q.2) (by fun_prop) (by fun_prop)
  · fun_prop
@[fun_prop] theorem poly_fibrePool : Poly (fun q : Env α × ℕ × List Request => fibrePool q.1 q.2.1 q.2.2) := by
  unfold fibrePool
  fun_prop
@[fun_prop] theorem poly_fibreCheck : Poly (fun q : (Walk α × Env α × ℕ × List Request) × Walk α =>
    fibreCheck q.1.1 q.1.2.1 q.1.2.2.1 q.1.2.2.2 q.2) := by
  unfold fibreCheck
  have hm : Poly (fun q : (Walk α × Env α × ℕ × List Request) × Walk α =>
      q.1.2.2.2.map (Request.reserve q.1.2.1)) :=
    BitCode.Poly.mapFn (f := fun q : ((Walk α × Env α × ℕ × List Request) × Walk α) × Request =>
      Request.reserve q.1.1.2.1 q.2) (by fun_prop) (by fun_prop)
  have hi : Poly (fun q : (Walk α × Env α × ℕ × List Request) × Walk α =>
      q.1.2.2.2.flatMap (Request.ids q.1.2.1)) :=
    BitCode.Poly.flatMapFn (f := fun q : ((Walk α × Env α × ℕ × List Request) × Walk α) × Request =>
      Request.ids q.1.1.2.1 q.2) (by fun_prop) (by fun_prop)
  fun_prop
@[fun_prop] theorem poly_fibreSelect : Poly (fun q : Walk α × Env α × ℕ × List Request =>
    fibreSelect q.1 q.2.1 q.2.2.1 q.2.2.2) := by
  unfold fibreSelect firstGood
  have hf : Poly (fun q : Walk α × Env α × ℕ × List Request =>
      (fibrePool q.2.1 q.2.2.1 q.2.2.2).filter (fibreCheck q.1 q.2.1 q.2.2.1 q.2.2.2)) :=
    BitCode.Poly.filterFn poly_fibreCheck (by fun_prop)
  exact (BitCode.Poly.headD default).comp hf
end Superstring.CollectionCode


namespace Superstring.CollectionCode
open BitCode Hierarchical LayerArray WalkCode
variable {α G : Type} [Inhabited α] [LinearOrder α] {V : Set (List α)}
def fibre (R : List Request) (t : ℕ) : List Request := R.filter (fun r => equal r.target t)
def recipients (X : Env α) (g : ℕ) (R : List Request) : List ℕ :=
  (List.range (data X g).2.length).filter (fun i => !(fibre R (g*stride X+i)).isEmpty)
def incoming (vs : Walk α) (X : Env α) (g : ℕ) (R : List Request) : Walk α :=
  collect ((recipients X g R).map (fun i => fibreSelect vs X (g*stride X+i) (fibre R (g*stride X+i))))

omit [Inhabited α] [LinearOrder α] in
@[simp] theorem mem_fibre (R : List Request) (t : ℕ) (r : Request) :
    r ∈ fibre R t ↔ r ∈ R ∧ r.target = t := by
  simp only [fibre,List.mem_filter,equal,decide_eq_true_eq]
omit [Inhabited α] [LinearOrder α] in
theorem fibre_ne (R : List Request) (t : ℕ) : fibre R t ≠ [] ↔ ∃ r ∈ R, r.target = t := by
  constructor
  · intro hn
    obtain ⟨r,hr⟩ := List.exists_mem_of_ne_nil _ hn
    exact ⟨r,(mem_fibre ..).mp hr⟩
  · rintro ⟨r,hr,ht⟩
    exact List.ne_nil_of_mem ((mem_fibre ..).mpr ⟨hr,ht⟩)
omit [Inhabited α] [LinearOrder α] in
@[simp] theorem mem_recipients (X : Env α) (g : ℕ) (R : List Request) (i : ℕ) :
    i ∈ recipients X g R ↔ i < (data X g).2.length ∧ ∃ r ∈ R, r.target = g*stride X+i := by
  simp only [recipients,List.mem_filter,List.mem_range,Bool.not_eq_true',List.isEmpty_eq_false_iff,fibre_ne]
omit [Inhabited α] [LinearOrder α] in
theorem nodup_recipients (X : Env α) (g : ℕ) (R : List Request) : (recipients X g R).Nodup :=
  List.Nodup.filter _ List.nodup_range

omit [Inhabited α] [LinearOrder α] in
theorem sum_indicator (J : List ℕ) (hn : J.Nodup) (t v : ℕ) (ht : t ∈ J) :
    (J.map (fun j => if t=j then v else 0)).sum = v := by
  induction J with
  | nil => cases ht
  | cons a J ih =>
    obtain ⟨ha,hJ⟩ := List.nodup_cons.mp hn
    rcases List.mem_cons.mp ht with rfl|ht
    · have hz : (J.map (fun j => if t=j then v else 0)).sum = 0 := by
        apply List.sum_eq_zero
        intro n hn
        obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hn
        exact ite_eq_right (show t ≠ j by intro he; exact ha (he.symm ▸ hj))
      simp only [List.map_cons,List.sum_cons,ite_true,hz,Nat.add_zero]
    · have htne : t ≠ a := fun he => ha (he ▸ ht)
      simp only [List.map_cons,List.sum_cons,htne,↓reduceIte,Nat.zero_add,ih hJ ht]

omit [Inhabited α] [LinearOrder α] in
theorem fibre_sum (J : List ℕ) (hn : J.Nodup) (R : List Request) (f : Request → ℕ)
    (key : ℕ → ℕ) (inj : Function.Injective key)
    (targets : ∀ r ∈ R, ∃ j ∈ J, r.target = key j) :
    (J.map (fun j => ((fibre R (key j)).map f).sum)).sum = (R.map f).sum := by
  induction R with
  | nil => simp [fibre]
  | cons r R ih =>
    obtain ⟨t,ht,he⟩ := targets r (List.mem_cons_self ..)
    have hf (j : ℕ) : ((fibre (r::R) (key j)).map f).sum =
        (if t=j then f r else 0)+((fibre R (key j)).map f).sum := by
      have heq : equal r.target (key j) = decide (t=j) := by
        simp only [equal,he,inj.eq_iff]
      simp only [fibre,List.filter_cons,heq]
      split <;> simp_all
    simp only [hf,List.sum_map_add,sum_indicator J hn t (f r) ht,List.map_cons,List.sum_cons]
    rw [ih (fun r hr => targets r (List.mem_cons_of_mem _ hr))]

namespace Model
theorem incoming_spec (vs : Walk α) {X : Env α} {C : LayerCollection {w | w ∈ vs} G}
    (h : Model X C) (closed : SubstringClosed {w | w ∈ vs}) (g : G) (R : List Request)
    (valid : ∀ r ∈ R, ValidRequest h r)
    (targets : ∀ r ∈ R, ∃ i : Fin (C.size g), r.target = h.encode ⟨g,i⟩)
    (distinct : SourcesDistinct R) :
    let J := recipients X (h.group g) R
    let P := incoming vs X (h.group g) R
    Runs {w | w ∈ vs} [] [] P ∧ cost P ≤ 2*(J.length*C.period g)+(R.map (Request.reserve X)).sum ∧
      (∀ i : Fin (C.size g), i.val ∈ J → ∀ w ∈ (C.layer g i).Content, w ∈ P) ∧
      ∀ r ∈ R, ∀ i ∈ r.ids X, ∀ w ∈ ls X i, w ∈ P := by
  let J := recipients X (h.group g) R
  let F := fun i => fibreSelect vs X (h.group g*stride X+i) (fibre R (h.group g*stride X+i))
  have hbnd (i : ℕ) (hi : i ∈ J) : i < C.size g := by
    have hh := ((mem_recipients ..).mp hi).1
    rwa [h.size] at hh
  have hF (i : ℕ) (hi : i ∈ J) := h.fibreSelect_spec vs closed ⟨g,⟨i,hbnd i hi⟩⟩
    (fibre R (h.group g*stride X+i)) ((fibre_ne ..).mpr ((mem_recipients ..).mp hi).2)
    (fun r hr => valid r ((mem_fibre ..).mp hr).1)
    (fun r hr => ((mem_fibre ..).mp hr).2)
    (fun r hr s hs he => distinct r ((mem_fibre ..).mp hr).1 s ((mem_fibre ..).mp hs).1 he)
  obtain ⟨hr,hc,hv⟩ := collect_spec (C.empty_mem closed g) (J.map F)
    (by intro P hP; obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hP; exact (hF i hi).1)
  have targetJ (r : Request) (hr : r ∈ R) : ∃ i ∈ J, r.target = h.group g*stride X+i := by
    obtain ⟨i,hi⟩ := targets r hr
    exact ⟨i.val,(mem_recipients ..).mpr ⟨by rw [h.size]; exact i.isLt,⟨r,hr,hi⟩⟩,hi⟩
  refine ⟨hr,?_,?_,?_⟩
  · change cost (collect (J.map F)) ≤ _
    rw [hc,List.map_map]
    have hh := List.sum_le_sum (l := J) (f := fun i => cost (F i))
      (g := fun i => 2*C.period g+((fibre R (h.group g*stride X+i)).map (Request.reserve X)).sum)
      (fun i hi => (hF i hi).2.1)
    have he : (J.map (fun i => 2*C.period g+((fibre R (h.group g*stride X+i)).map (Request.reserve X)).sum)).sum =
        2*(J.length*C.period g)+(R.map (Request.reserve X)).sum := by
      rw [List.sum_map_add,fibre_sum J (nodup_recipients ..) R (Request.reserve X)
        (fun i => h.group g*stride X+i) (fun _ _ hh => Nat.add_left_cancel hh) targetJ]
      simp only [List.map_const',List.sum_replicate,nsmul_eq_mul,Nat.cast_id]
      ring
    exact hh.trans_eq he
  · intro i hi w hw
    exact hv (F i.val) (List.mem_map.mpr ⟨i.val,hi,rfl⟩) w
      ((hF i.val hi).2.2.1 w ((h.content_iff ⟨g,i⟩ w).mpr hw))
  · intro r hr' i hi w hw
    obtain ⟨j,hj,ht⟩ := targetJ r hr'
    exact hv (F j) (List.mem_map.mpr ⟨j,hj,rfl⟩) w
      ((hF j hj).2.2.2 r ((mem_fibre ..).mpr ⟨hr',ht⟩) i hi w hw)
end Model
end Superstring.CollectionCode


namespace Superstring.CollectionCode
open BitCode Hierarchical LayerArray WalkCode
variable {α G : Type} [Inhabited α] [LinearOrder α] {V : Set (List α)}
def baseIndex (J : List ℕ) : ℕ := J.foldl max 0
def holes (J : List ℕ) : List ℕ := (List.range (baseIndex J+1)).filter (fun i => !(member i J))
def prepare (vs : Walk α) (X : Env α) (g : ℕ) (R : List Request) : ℕ × Walk α :=
  let J := recipients X g R
  let P := incoming vs X g R
  if J.isEmpty then (0,P) else
    let base := baseIndex J
    let r := (fibre R (g*stride X+base)).headD default
    (base+1,below (data X g) (holes J) P
      (RecordCode.start r.code+RecordCode.offset r.code)
      (RecordCode.stop r.code+RecordCode.offset r.code))
def process (vs : Walk α) (X : Env α) (g M : ℕ) (R : List Request) : Plan α :=
  let p := prepare vs X g R
  complete X g p.1 M p.2

omit [Inhabited α] [LinearOrder α] in
theorem maxFold_mem (J : List ℕ) (a : ℕ) : J.foldl max a = a ∨ J.foldl max a ∈ J := by
  induction J generalizing a with
  | nil => exact Or.inl rfl
  | cons b J ih =>
    rcases ih (max a b) with h|h
    · by_cases hab : b ≤ a
      · exact Or.inl (h.trans (max_eq_left hab))
      · exact Or.inr (List.mem_cons.mpr (Or.inl (h.trans (max_eq_right (by omega)))))
    · exact Or.inr (List.mem_cons_of_mem _ h)
omit [Inhabited α] [LinearOrder α] in
theorem base_mem (J : List ℕ) (hn : J ≠ []) : baseIndex J ∈ J := by
  rcases maxFold_mem J 0 with h|h
  · obtain ⟨j,hj⟩ := List.exists_mem_of_ne_nil _ hn
    have hh := le_maxFold J 0 hj
    have he : j = baseIndex J := by change J.foldl max 0 = 0 at h; unfold baseIndex; omega
    exact he ▸ hj
  · exact h
omit [Inhabited α] [LinearOrder α] in
theorem mem_holes (J : List ℕ) (i : ℕ) : i ∈ holes J ↔ i ≤ baseIndex J ∧ i ∉ J := by
  simp [holes,member]
omit [Inhabited α] [LinearOrder α] in
theorem holes_length (J : List ℕ) (hn : J.Nodup) : (holes J).length+J.length=baseIndex J+1 := by
  have hs : J.toFinset ⊆ (Finset.range (baseIndex J+1)) := by
    intro j hj
    have hh := le_maxFold J 0 (List.mem_toFinset.mp hj)
    exact Finset.mem_range.mpr (by change j < J.foldl max 0+1; omega)
  have he : (holes J).toFinset = Finset.range (baseIndex J+1) \ J.toFinset := by
    ext i
    simp only [List.mem_toFinset,mem_holes,Finset.mem_sdiff,Finset.mem_range,Nat.lt_succ_iff]
  have hnd : (holes J).Nodup := List.Nodup.filter _ List.nodup_range
  have hh := Finset.card_sdiff_add_card_eq_card hs
  rwa [← he,List.toFinset_card_of_nodup hnd,List.toFinset_card_of_nodup hn,Finset.card_range] at hh
namespace Model
variable {X : Env α}
theorem prepare_spec (vs : Walk α) {C : LayerCollection {w | w ∈ vs} G}
    (h : Model X C) (closed : SubstringClosed {w | w ∈ vs}) (g : G) (R : List Request)
    (valid : ∀ r ∈ R, ValidRequest h r)
    (targets : ∀ r ∈ R, ∃ i : Fin (C.size g), r.target = h.encode ⟨g,i⟩)
    (distinct : SourcesDistinct R) :
    let p := prepare vs X (h.group g) R
    p.1 ≤ C.size g ∧ Runs {w | w ∈ vs} [] [] p.2 ∧
      cost p.2 ≤ 2*(p.1*C.period g)+(R.map (Request.reserve X)).sum ∧
      (∀ i : Fin (C.size g), i.val < p.1 → ∀ w ∈ (C.layer g i).Content, w ∈ p.2) ∧
      ∀ r ∈ R, ∀ i ∈ r.ids X, ∀ w ∈ ls X i, w ∈ p.2 := by
  obtain ⟨hr,hc,hv,hi⟩ := h.incoming_spec vs closed g R valid targets distinct
  let J := recipients X (h.group g) R
  let P := incoming vs X (h.group g) R
  have hbnd (i : ℕ) (hi : i ∈ J) : i < C.size g := by
    have hh := ((mem_recipients ..).mp hi).1
    rwa [h.size] at hh
  by_cases hn : J = []
  · have he : prepare vs X (h.group g) R = (0,P) := by simp only [prepare,show recipients X (h.group g) R = [] from hn,List.isEmpty_nil,↓reduceIte]; rfl
    rw [he]
    exact ⟨Nat.zero_le _,hr,by simpa only [show recipients X (h.group g) R=[] from hn,List.length_nil] using hc,
      fun i hi => by omega,hi⟩
  · let base := baseIndex J
    have hbJ := base_mem J hn
    have hb := hbnd base hbJ
    let r := (fibre R (h.group g*stride X+base)).headD default
    have hrmem : r ∈ fibre R (h.group g*stride X+base) := by
      have hne := (fibre_ne ..).mpr ((mem_recipients ..).mp hbJ).2
      unfold r
      cases he : fibre R (h.group g*stride X+base) with
      | nil => exact False.elim (hne he)
      | cons a as => exact List.mem_cons_self ..
    obtain ⟨rR,rt⟩ := (mem_fibre ..).mp hrmem
    obtain ⟨w⟩ := h.requestAt (valid r rR) ⟨g,⟨base,hb⟩⟩ rt.symm
    have hlater := (Classical.choice (valid r rR)).later
    have hrec := w.record.length_lt (C.positive w.source) (C.positive g)
      (C.periodic w.source) (C.periodic g) w.foreign
    have hpq : C.period w.source < C.period g := by
      rw [← w.source_eq,rt,owner_encode X _ _ (h.local_lt g ⟨base,hb⟩),h.per_eq,h.per_eq] at hlater
      exact hlater
    have hlen : RecordCode.stop r.code+RecordCode.offset r.code-
        (RecordCode.start r.code+RecordCode.offset r.code) < 2*C.period g := by
      change w.record.stop-w.record.start < (C.period w.source:ℤ)+(C.period g:ℤ) at hrec
      rw [← w.start,← w.stop]; omega
    have hfirst : (h.natLayer g base).first (RecordCode.start r.code+RecordCode.offset r.code) ≤
        RecordCode.stop r.code+RecordCode.offset r.code := by
      rw [h.natLayer_fin g ⟨base,hb⟩,← w.start,← w.stop,← w.offset]
      exact w.record.first_le
    have hlast : RecordCode.stop r.code+RecordCode.offset r.code ≤
        (h.natLayer g base).last (RecordCode.start r.code+RecordCode.offset r.code) := by
      rw [h.natLayer_fin g ⟨base,hb⟩,← w.start,← w.stop,← w.offset]
      exact w.record.le_last
    obtain ⟨hq,hbq,hvp,hiq⟩ := below_spec (h.natLayer g)
      (fun i hi => h.nat_rep g (by have hh := (mem_holes J i).mp hi; omega))
      closed (C.positive g) (C.periodic g) (C.letters closed g) hr
      (by change ∀ w ∈ (h.natLayer g base).Content, _; rw [h.natLayer_fin g ⟨base,hb⟩]; exact hv ⟨base,hb⟩ hbJ)
      (fun i hi => h.nat_order g ((mem_holes J i).mp hi).1) hfirst hlast hlen
    have he : prepare vs X (h.group g) R = (base+1,below (data X (h.group g)) (holes J) P
        (RecordCode.start r.code+RecordCode.offset r.code) (RecordCode.stop r.code+RecordCode.offset r.code)) := by
      simp only [prepare,show recipients X (h.group g) R=J from rfl,List.isEmpty_iff,hn,↓reduceIte]; rfl
    rw [he]
    refine ⟨by omega,hq,?_,?_,fun r hr i hri w hw => hvp w (hi r hr i hri w hw)⟩
    · have hh := holes_length J (nodup_recipients ..)
      have hmul := Nat.add_mul (holes J).length J.length (C.period g)
      rw [hh] at hmul
      dsimp only [P,J,base] at hc hbq hmul ⊢
      omega
    · intro i hi w hw
      by_cases hij : i.val ∈ J
      · exact hvp w (hv i hij w hw)
      · exact hiq i.val ((mem_holes J i.val).mpr ⟨by omega,hij⟩) w ((h.natLayer_fin g i).symm ▸ hw)
theorem process_spec (vs : Walk α) {C : LayerCollection {w | w ∈ vs} G}
    (h : Model X C) (closed : SubstringClosed {w | w ∈ vs}) (supply : C.RecordSupply)
    (M : ℕ) (len : ∀ w ∈ vs, w.length ≤ M) (g : G) (R : List Request)
    (valid : ∀ r ∈ R, ValidRequest h r)
    (targets : ∀ r ∈ R, ∃ i : Fin (C.size g), r.target = h.encode ⟨g,i⟩)
    (distinct : SourcesDistinct R) :
    let o := process vs X (h.group g) M R
    GoodPlan h o ∧ planBudget X o ≤ 2*(C.size g*C.period g)+(R.map (Request.reserve X)).sum ∧
      (∀ i : Fin (C.size g), Covered X o (h.encode ⟨g,i⟩)) ∧
      (∀ r ∈ R, ∀ i ∈ r.ids X, ∀ w ∈ ls X i, w ∈ o.1) ∧
      (∀ r ∈ o.2.2, r.source=h.group g) ∧ o.2.2.length≤1 := by
  obtain ⟨hp,hr,hc,hv,hi⟩ := h.prepare_spec vs closed g R valid targets distinct
  obtain ⟨hg,hb,hv',hi',hs,hn⟩ := h.complete_spec closed supply M len g _ hp _ hr hv
  refine ⟨hg,?_,?_,fun r hri i hii w hw => hv' w (hi r hri i hii w hw),hs,hn⟩
  · have he := Nat.sub_add_cancel hp
    have hm := Nat.add_mul (C.size g-(prepare vs X (h.group g) R).1)
      (prepare vs X (h.group g) R).1 (C.period g)
    rw [he] at hm
    exact (hb.trans (by omega))
  · intro i
    by_cases hh : i.val < (prepare vs X (h.group g) R).1
    · exact Or.inl (fun w hw => hv' w (hv i hh w ((h.content_iff ⟨g,i⟩ w).mp hw)))
    · exact hi' i (by omega)
end Model
end Superstring.CollectionCode

end OAI
