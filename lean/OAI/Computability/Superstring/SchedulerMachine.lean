import OAI.Computability.Superstring.GroupPoly

namespace OAI

namespace Superstring.CollectionCode
open BitCode Hierarchical LayerArray WalkCode BlockClose
variable {α G : Type} [Inhabited α] [LinearOrder α] [Coded α]
abbrev Context (α : Type) := Walk α × Env α × ℕ
abbrev Input (α : Type) := Context α × State α
def iterStep (q : Input α) : Input α := (q.1,advance q.1.1 q.1.2.1 q.1.2.2 q.2)
def schedulerCapacity (q : Input α) : ℕ :=
  bitSize q.1+bitSize (gs q.1.2.1)+bitSize q.2.2.2+1+
    (2*budget q.1.2.1 q.2+1)*(bitSize q.1.1+1)+(gs q.1.2.1).length*maxExtras q.1.2.1 q.1.2.2
def sweep (q : Context α) : Plan α :=
  let s : Input α := (q,initial q.2.1)
  (((cappedStep iterStep)^[((gs q.2.1).length)] (schedulerCapacity s,s)).2).2.2

omit [Coded α] in
theorem iterate_iterStep (q : Input α) (n : ℕ) :
    iterStep^[n] q = (q.1,(advance q.1.1 q.1.2.1 q.1.2.2)^[n] q.2) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply',ih,Function.iterate_succ_apply']; rfl

namespace Model
variable {vs : Walk α} {X : Env α} {C : LayerCollection {w | w ∈ vs} G} (h : Model X C)
theorem state_size (M : ℕ) (s t : State α) (ht : Invariant h t)
    (hc : budget X t ≤ budget X s)
    (he : bitSize t.2.2 ≤ bitSize s.2.2+(gs X).length*maxExtras X M) :
    bitSize (((vs,X,M),t) : Input α) ≤ schedulerCapacity ((vs,X,M),s) := by
  have hi := bitSize_sublist ht.todo
  have hp : cost t.2.1 ≤ budget X s := by
    unfold budget planBudget at hc ⊢
    omega
  have hv : ∀ w ∈ t.2.1, bitSize w ≤ bitSize vs := fun w hw => bitSize_mem (ht.good.1.1.2.1 w hw)
  have hh := bitSize_map_le t.2.1 (fun w => w) (bitSize vs) hv
  change bitSize (List.map (id : List α → List α) t.2.1) ≤ _ at hh
  rw [List.map_id,rooted_length ht.good.1] at hh
  have ht1 := bitSize_prod t.1 t.2
  have ht2 := bitSize_prod t.2.1 t.2.2
  simp only [Prod.eta] at ht1 ht2
  have hm := Nat.mul_le_mul_right (bitSize vs+1) (show 2*cost t.2.1+1 ≤ 2*budget X s+1 by omega)
  simp only [bitSize_prod] at hi he ⊢
  unfold schedulerCapacity
  simp only [bitSize_prod]
  omega

theorem sweep_spec (closed : SubstringClosed {w | w ∈ vs}) (nil_mem : ([] : List α) ∈ vs)
    (supply : C.RecordSupply) (M : ℕ) (len : ∀ w ∈ vs, w.length ≤ M) :
    let o := sweep (vs,X,M)
    GoodPlan h o ∧ planBudget X o ≤ ((gs X).map (charge X)).sum ∧ o.2.2=[] ∧
      ∀ i ∈ ids X, Covered X o i := by
  have hi := h.iterate_advance vs closed supply M len (initial X) (h.initial_invariant vs nil_mem)
  have he := iterate_cappedStep_eq iterStep (gs X).length (schedulerCapacity (((vs,X,M),initial X) : Input α))
    (((vs,X,M),initial X) : Input α) (by
      intro n hn _
      rw [iterate_iterStep]
      apply h.state_size M (initial X) _ (hi n).1 (hi n).2.1
      have hh := (hi n).2.2.2
      have hm := Nat.mul_le_mul_right (maxExtras X M) (show n ≤ (gs X).length by omega)
      omega)
  have hh := hi (gs X).length
  let t := (advance vs X M)^[(gs X).length] (initial X)
  change Invariant h t ∧ _ at hh
  have hz : t.1=[] := by
    apply List.length_eq_zero_iff.mp
    have ht := hh.2.2.1
    change t.1.length ≤ (gs X).length-(gs X).length at ht
    omega
  have hr : t.2.2.2=[] := by
    by_contra hn
    obtain ⟨r,hr⟩ := List.exists_mem_of_ne_nil _ hn
    have ht := hh.1.targets r hr
    rw [hz] at ht
    exact List.not_mem_nil ht
  unfold sweep
  dsimp only
  rw [he,iterate_iterStep]
  change GoodPlan h t.2 ∧ _
  refine ⟨hh.1.good,?_,hr,?_⟩
  · change planBudget X t.2 ≤ _
    have hc := hh.2.1
    change budget X t ≤ budget X (initial X) at hc
    simpa only [budget,hz,initial,planBudget,cost_singleton,List.map_nil,List.sum_nil,Nat.add_zero,Nat.zero_add] using hc
  · intro i hi
    obtain ⟨j,rfl⟩ := (h.mem_ids i).mp hi
    rcases hh.1.ready j with hj|hj
    · rw [hz] at hj; exact False.elim (List.not_mem_nil hj)
    · exact hj
end Model
end Superstring.CollectionCode


namespace Superstring.CollectionCode
open BitCode Hierarchical LayerArray WalkCode BlockClose
variable {α : Type} [Inhabited α] [LinearOrder α] [Coded α]
omit [Inhabited α] [LinearOrder α] in
@[fun_prop] theorem poly_gs : Poly (gs : Env α → List ℕ) := by unfold gs; fun_prop
omit [Inhabited α] [LinearOrder α] in
@[fun_prop] theorem poly_pick : Poly (fun q : Env α × List ℕ => pick q.1 q.2) := by
  unfold pick firstGood
  have hp : Poly (fun q : (Env α × List ℕ) × ℕ => q.1.2.all (fun j => lessEq (per q.1.1 q.2) (per q.1.1 j))) :=
    BitCode.Poly.allFn
      (p := fun q : ((Env α × List ℕ) × ℕ) × ℕ => lessEq (per q.1.1.1 q.1.2) (per q.1.1.1 q.2))
      (by fun_prop) (by fun_prop)
  exact (BitCode.Poly.headD 0).comp (BitCode.Poly.filterFn hp BitCode.Poly.snd)
@[fun_prop] theorem poly_without : Poly (fun q : List ℕ × ℕ => without q.1 q.2) := by
  unfold without
  exact BitCode.Poly.filterFn (p := fun q : (List ℕ × ℕ) × ℕ => !(equal q.2 q.1.2)) (by fun_prop) (by fun_prop)
omit [Inhabited α] [LinearOrder α] in
@[fun_prop] theorem poly_inRequests : Poly (fun q : Env α × ℕ × List Request => inRequests q.1 q.2.1 q.2.2) := by
  unfold inRequests Request.target
  exact BitCode.Poly.filterFn (p := fun q : (Env α × ℕ × List Request) × Request => equal (owner q.1.1 q.2.2.1) q.1.2.1) (by fun_prop) (by fun_prop)
omit [Inhabited α] [LinearOrder α] in
@[fun_prop] theorem poly_restRequests : Poly (fun q : Env α × ℕ × List Request => restRequests q.1 q.2.1 q.2.2) := by
  unfold restRequests Request.target
  exact BitCode.Poly.filterFn (p := fun q : (Env α × ℕ × List Request) × Request => !(equal (owner q.1.1 q.2.2.1) q.1.2.1)) (by fun_prop) (by fun_prop)
omit [Inhabited α] [LinearOrder α] in
@[fun_prop] theorem poly_charge : Poly (fun q : Env α × ℕ => charge q.1 q.2) := by unfold charge; fun_prop
omit [Inhabited α] [LinearOrder α] in
@[fun_prop] theorem poly_requestReserve : Poly (fun q : Env α × Request => q.2.reserve q.1) := by
  unfold Request.reserve Request.members Request.source
  fun_prop
omit [Inhabited α] [LinearOrder α] in
@[fun_prop] theorem poly_planBudget : Poly (fun q : Env α × Plan α => planBudget q.1 q.2) := by
  have hr : Poly (fun q : Env α × Plan α => (q.2.2.2.map (Request.reserve q.1)).sum) :=
    BitCode.Poly.sum.comp (BitCode.Poly.mapFn
      (f := fun q : (Env α × Plan α) × Request => q.2.reserve q.1.1) (by fun_prop) (by fun_prop))
  have hb : Poly (fun q : Env α × Plan α => (q.2.2.1.map Block.reserve).sum) :=
    BlockClose.poly_reserves.comp (by fun_prop)
  unfold planBudget
  fun_prop
omit [Inhabited α] [LinearOrder α] in
@[fun_prop] theorem poly_budget : Poly (fun q : Env α × State α => budget q.1 q.2) := by
  have hr : Poly (fun q : Env α × State α => (q.2.1.map (charge q.1)).sum) :=
    BitCode.Poly.sum.comp (BitCode.Poly.mapFn
      (f := fun q : (Env α × State α) × ℕ => charge q.1.1 q.2) (by fun_prop) (by fun_prop))
  unfold budget
  fun_prop
@[fun_prop] theorem poly_extraSizes (hlt : Poly (fun q : α × α => decide (q.1<q.2))) :
    Poly (fun q : Env α × ℕ => extraSizes q.1 q.2) := by
  have hc := poly_complete hlt
  unfold extraSizes
  apply BitCode.Poly.flatMapFn (f := fun q : (Env α × ℕ) × ℕ =>
    (List.range ((data q.1.1 q.2).2.length+1)).map (fun cut => bitSize (complete q.1.1 q.2 cut q.1.2 [[]]).2))
  · exact BitCode.Poly.mapFn (f := fun q : ((Env α × ℕ) × ℕ) × ℕ =>
      bitSize (complete q.1.1.1 q.1.2 q.2 q.1.1.2 [[]]).2) (by fun_prop) (by fun_prop)
  · fun_prop
@[fun_prop] theorem poly_maxExtras (hlt : Poly (fun q : α × α => decide (q.1<q.2))) :
    Poly (fun q : Env α × ℕ => maxExtras q.1 q.2) :=
  BitCode.Poly.maxFold.comp (poly_extraSizes hlt)
omit [Inhabited α] [LinearOrder α] in
@[fun_prop] theorem poly_initial : Poly (initial : Env α → State α) := by unfold initial; fun_prop
@[fun_prop] theorem poly_advance (hlt : Poly (fun q : α × α => decide (q.1<q.2))) :
    Poly (fun q : Input α => advance q.1.1 q.1.2.1 q.1.2.2 q.2) := by
  have hp := poly_process hlt
  have ho : Poly (fun q : Input α =>
      process q.1.1 q.1.2.1 (pick q.1.2.1 q.2.1) q.1.2.2 (inRequests q.1.2.1 (pick q.1.2.1 q.2.1) q.2.2.2.2)) :=
    hp.comp (f := fun q : Input α => ((q.1.1,q.1.2.1),pick q.1.2.1 q.2.1,q.1.2.2,
      inRequests q.1.2.1 (pick q.1.2.1 q.2.1) q.2.2.2.2)) (by fun_prop)
  unfold advance
  dsimp only
  apply BitCode.Poly.ite (by fun_prop) (by fun_prop)
  fun_prop
@[fun_prop] theorem poly_schedulerStep (hlt : Poly (fun q : α × α => decide (q.1<q.2))) :
    Poly (iterStep : Input α → Input α) := BitCode.Poly.fst.pair (poly_advance hlt)
@[fun_prop] theorem poly_schedulerCapacity (hlt : Poly (fun q : α × α => decide (q.1<q.2))) :
    Poly (schedulerCapacity : Input α → ℕ) := by
  have hm := poly_maxExtras hlt
  unfold schedulerCapacity
  fun_prop
@[fun_prop] theorem poly_sweep (hlt : Poly (fun q : α × α => decide (q.1<q.2))) :
    Poly (sweep : Context α → Plan α) := by
  have hc := poly_schedulerCapacity hlt
  have ht : Poly (fun q : Context α =>
      ((cappedStep iterStep)^[(gs q.2.1).length] (schedulerCapacity (q,initial q.2.1),(q,initial q.2.1))).2) :=
    (BitCode.Poly.cappedIterate (poly_schedulerStep hlt)).comp
      (f := fun q : Context α => ((gs q.2.1).length,(schedulerCapacity (q,initial q.2.1),(q,initial q.2.1)))) (by fun_prop)
  exact BitCode.Poly.snd.comp (BitCode.Poly.snd.comp ht)
end Superstring.CollectionCode


namespace Superstring.CollectionCode
open BitCode Hierarchical LayerArray WalkCode BlockClose
variable {α G : Type} [Inhabited α] [LinearOrder α] [Coded α]
def tour (q : Context α) : Walk α :=
  let o := sweep q
  close ((q.1,contents q.2.1),o.1,o.2.1)
@[fun_prop] theorem poly_tour (hlt : Poly (fun q : α × α => decide (q.1<q.2))) :
    Poly (tour : Context α → Walk α) := by
  have hs := poly_sweep hlt
  exact BlockClose.poly_close.comp
    (f := fun q : Context α => ((q.1,contents q.2.1),(sweep q).1,(sweep q).2.1)) (by fun_prop)
namespace Model
variable {vs : Walk α} {X : Env α} {C : LayerCollection {w | w ∈ vs} G} (h : Model X C)
include h in
theorem tour_spec (closed : SubstringClosed {w | w ∈ vs}) (nil_mem : ([] : List α) ∈ vs)
    (supply : C.RecordSupply) (M : ℕ) (len : ∀ w ∈ vs, w.length ≤ M) :
    Runs {w | w ∈ vs} [] [] (tour (vs,X,M)) ∧
    cost (tour (vs,X,M)) ≤ ((gs X).map (charge X)).sum ∧
    ∀ i ∈ ids X, ∀ w ∈ ls X i, w ∈ tour (vs,X,M) := by
  obtain ⟨hg,hb,hr,hcov⟩ := h.sweep_spec closed nil_mem supply M len
  let o := sweep (vs,X,M)
  have hh := BlockClose.close_spec ((vs,contents X),o.1,o.2.1) closed (ids X) (owner X) (per X) (rank X)
    hg.1 hg.2.1 (by
      intro i hi
      rcases hcov i hi with hh|hh|⟨r,hm,_⟩
      · exact Or.inl hh
      · exact Or.inr hh
      · rw [hr] at hm; exact False.elim (List.not_mem_nil hm))
  change Runs _ [] [] (tour (vs,X,M)) ∧ _ at hh
  refine ⟨hh.1,?_,hh.2.2.2⟩
  have hc := hh.2.1
  change cost (tour (vs,X,M)) ≤ cost o.1+(o.2.1.map Block.reserve).sum at hc
  change planBudget X o ≤ _ at hb
  unfold planBudget at hb
  omega
end Model
end Superstring.CollectionCode

end OAI
