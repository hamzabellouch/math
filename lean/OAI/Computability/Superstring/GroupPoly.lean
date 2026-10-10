import OAI.Computability.Superstring.SchedulerCode

namespace OAI

namespace Superstring.CollectionCode
open BitCode Hierarchical LayerArray WalkCode UpperCode
variable {α : Type} [Coded α] [Inhabited α] [LinearOrder α]
@[fun_prop] theorem poly_foreign : Poly (fun q : GroupData α × Book α × Param => foreign q.1 q.2.1 q.2.2) := by
  unfold foreign RecordCode.offset
  fun_prop
abbrev ChooseInput (α : Type) := (GroupData α × Book α × List ℕ) × ℕ × ℕ × ℤ
@[fun_prop] theorem poly_choose : Poly (fun q : ChooseInput α =>
    choose q.1.1 q.1.2.1 q.1.2.2 q.2.1 q.2.2.1 q.2.2.2 (foreign q.1.1 q.1.2.1)) := by
  unfold choose
  have hf : Poly (fun q : ChooseInput α =>
      (params q.1.2.1 q.1.2.2 q.1.1.2.length q.2.2.1 q.2.2.2).filter
        (fun v => test q.1.1 q.1.2.1 q.2.1 q.2.2.2 v && foreign q.1.1 q.1.2.1 v)) :=
    BitCode.Poly.filterFn (p := fun q : ChooseInput α × Param =>
      test q.1.1.1 q.1.1.2.1 q.1.2.1 q.1.2.2.2 q.2 && foreign q.1.1.1 q.1.1.2.1 q.2)
      (by fun_prop) (by fun_prop)
  fun_prop
@[fun_prop] theorem poly_hard (hlt : Poly (fun q : α × α => decide (q.1<q.2))) :
    Poly (fun q : Env α × ℕ × ℕ × UpperCode.Param => hard q.1 q.2.1 q.2.2.1 q.2.2.2) := by
  have ph := poly_phase hlt
  unfold hard stride RecordCode.start RecordCode.stop
  exact DistributeCode.poly_record.comp
    (f := fun q : Env α × ℕ × ℕ × UpperCode.Param =>
      ((data q.1 q.2.1,q.2.1,q.2.2.2.2.1,q.2.1*q.1.2),
       (upper (data q.1 q.2.1).2.length q.2.2.1,(data q.1 q.2.1).2.length-q.2.2.2.1,(data q.1 q.2.1).2.length-1),
       (q.2.2.2.2.2.2.1,q.2.2.2.2.2.2.2,phase q.1 q.2.1))) (by fun_prop)
@[fun_prop] theorem poly_hardPlan (hlt : Poly (fun q : α × α => decide (q.1<q.2))) :
    Poly (fun q : Env α × ℕ × ℕ × UpperCode.Param => hardPlan q.1 q.2.1 q.2.2.1 q.2.2.2) := by
  have ph := poly_hard hlt
  unfold hardPlan
  fun_prop
abbrev CompleteInput (α : Type) := Env α × ℕ × ℕ × ℕ × Walk α
@[fun_prop] theorem poly_cond {δ ε : Type} [Coded δ] [Coded ε] {p : δ → Prop} [DecidablePred p]
    {f g : δ → ε} (hp : Poly (fun x => decide (p x))) (hf : Poly f) (hg : Poly g) :
    Poly (fun x => if p x then f x else g x) := by
  simpa only [decide_eq_true_eq] using BitCode.Poly.ite hp hf hg
@[fun_prop] theorem poly_decide_and {δ : Type} [Coded δ] {p q : δ → Prop} [DecidablePred p] [DecidablePred q]
    (hp : Poly (fun x => decide (p x))) (hq : Poly (fun x => decide (q x))) :
    Poly (fun x => decide (p x ∧ q x)) := by
  simpa only [Bool.decide_and,Function.comp_def] using BitCode.Poly.and.comp (hp.pair hq)
def completeRoot (q : CompleteInput α) : Walk α := rootUpper (data q.1 q.2.1)
  (upper (data q.1 q.2.1).2.length q.2.2.1) ((data q.1 q.2.1).2.length-1) (phase q.1 q.2.1)
def completeBand (q : CompleteInput α) : Walk α := attachBand (data q.1 q.2.1)
  (upper (data q.1 q.2.1).2.length q.2.2.1) (q.2.2.1-1) ((data q.1 q.2.1).2.length-1) q.2.2.2.2 (phase q.1 q.2.1)
def completePick (q : CompleteInput α) : UpperCode.Param := choose (data q.1 q.2.1) (book q.1) (ids q.1)
  q.2.2.1 q.2.2.2.1 (phase q.1 q.2.1) (foreign (data q.1 q.2.1) (book q.1))
def completeHard (q : CompleteInput α) : Plan α := hardPlan q.1 q.2.1 q.2.2.1 (completePick q)
def completeM (q : CompleteInput α) : ℕ := (data q.1 q.2.1).2.length
def completeP (q : CompleteInput α) : ℕ := (data q.1 q.2.1).1.length
def completeT (q : CompleteInput α) : ℤ := phase q.1 q.2.1
def completeH (q : CompleteInput α) : ℤ := GeoCode.first (exits (data q.1 q.2.1) (completeM q-1)) (completeT q)
def completeExit (q : CompleteInput α) : ℤ := GeoCode.exit (exits (data q.1 q.2.1) (q.2.2.1-1)) (completeT q)
@[fun_prop] theorem poly_completeRoot (hlt : Poly (fun q : α × α => decide (q.1<q.2))) : Poly (completeRoot (α:=α)) := by
  have ph := poly_phase hlt
  exact poly_rootUpper.comp
    (f := fun q : CompleteInput α => (data q.1 q.2.1,upper (data q.1 q.2.1).2.length q.2.2.1,
      (data q.1 q.2.1).2.length-1,phase q.1 q.2.1)) (by fun_prop)
@[fun_prop] theorem poly_completeBand (hlt : Poly (fun q : α × α => decide (q.1<q.2))) : Poly (completeBand (α:=α)) := by
  have ph := poly_phase hlt
  exact poly_attachBand.comp
    (f := fun q : CompleteInput α => ((data q.1 q.2.1,upper (data q.1 q.2.1).2.length q.2.2.1),
      (q.2.2.1-1,(data q.1 q.2.1).2.length-1),q.2.2.2.2,phase q.1 q.2.1)) (by fun_prop)
@[fun_prop] theorem poly_completePick (hlt : Poly (fun q : α × α => decide (q.1<q.2))) : Poly (completePick (α:=α)) := by
  have ph := poly_phase hlt
  exact poly_choose.comp
    (f := fun q : CompleteInput α => ((data q.1 q.2.1,book q.1,ids q.1),q.2.2.1,q.2.2.2.1,phase q.1 q.2.1)) (by fun_prop)
@[fun_prop] theorem poly_completeHard (hlt : Poly (fun q : α × α => decide (q.1<q.2))) : Poly (completeHard (α:=α)) := by
  have hc := poly_completePick hlt
  exact (poly_hardPlan hlt).comp (f := fun q : CompleteInput α => (q.1,q.2.1,q.2.2.1,completePick q)) (by fun_prop)
omit [Inhabited α] [LinearOrder α] in
@[fun_prop] theorem poly_completeM : Poly (completeM (α:=α)) := by unfold completeM; fun_prop
omit [Inhabited α] [LinearOrder α] in
@[fun_prop] theorem poly_completeP : Poly (completeP (α:=α)) := by unfold completeP; fun_prop
@[fun_prop] theorem poly_completeT (hlt : Poly (fun q : α × α => decide (q.1<q.2))) : Poly (completeT (α:=α)) :=
  (poly_phase hlt).comp (f := fun q : CompleteInput α => (q.1,q.2.1)) (by fun_prop)
@[fun_prop] theorem poly_completeH (hlt : Poly (fun q : α × α => decide (q.1<q.2))) : Poly (completeH (α:=α)) := by
  have ht := poly_completeT hlt
  unfold completeH
  fun_prop
@[fun_prop] theorem poly_completeExit (hlt : Poly (fun q : α × α => decide (q.1<q.2))) : Poly (completeExit (α:=α)) := by
  have ht := poly_completeT hlt
  unfold completeExit
  fun_prop
omit [Inhabited α] [LinearOrder α] in
@[fun_prop] theorem poly_completeTest1 : Poly (fun q : CompleteInput α => decide (completeM q ≤ q.2.2.1)) := by fun_prop
@[fun_prop] theorem poly_completeTest2 (hlt : Poly (fun q : α × α => decide (q.1<q.2))) :
    Poly (fun q : CompleteInput α => decide (completeH q-completeT q ≤ ((completeM q-q.2.2.1)*completeP q : ℕ))) := by
  have hH := poly_completeH hlt
  have ht := poly_completeT hlt
  fun_prop
@[fun_prop] theorem poly_completeTest3 (hlt : Poly (fun q : α × α => decide (q.1<q.2))) :
    Poly (fun q : CompleteInput α => decide (0 < q.2.2.1 ∧
      completeH q-completeExit q ≤ ((completeM q-q.2.2.1)*completeP q : ℕ))) := by
  have hH := poly_completeH hlt
  have he := poly_completeExit hlt
  have h0 : Poly (fun q : CompleteInput α => decide (0 < q.2.2.1)) := by fun_prop
  have hn : Poly (fun q : CompleteInput α => (((completeM q-q.2.2.1)*completeP q : ℕ) : ℤ)) := by fun_prop
  have hs : Poly (fun q : CompleteInput α => completeH q-completeExit q) := BitCode.Poly.subInt.comp (hH.pair he)
  have h1 : Poly (fun q : CompleteInput α => decide (completeH q-completeExit q ≤ ((completeM q-q.2.2.1)*completeP q : ℕ))) :=
    BitCode.Poly.leInt.comp (hs.pair hn)
  exact poly_decide_and h0 h1
@[fun_prop] theorem poly_complete (hlt : Poly (fun q : α × α => decide (q.1<q.2))) :
    Poly (fun q : CompleteInput α => complete q.1 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2) := by
  have hr := poly_completeRoot hlt
  have hb := poly_completeBand hlt
  have hp := poly_completeHard hlt
  have ha : Poly (fun q : CompleteInput α => (q.2.2.2.2,([] : List (BlockClose.Block α)),([] : List Request))) := by fun_prop
  have hb1 : Poly (fun q : CompleteInput α => (join q.2.2.2.2 (completeRoot q),([] : List (BlockClose.Block α)),([] : List Request))) := by fun_prop
  have hb2 : Poly (fun q : CompleteInput α => (completeBand q,([] : List (BlockClose.Block α)),([] : List Request))) := by fun_prop
  have hb3 : Poly (fun q : CompleteInput α => (join q.2.2.2.2 (completeHard q).1,(completeHard q).2)) := by
    exact (WalkCode.poly_join.comp (BitCode.Poly.pair (by fun_prop) (BitCode.Poly.fst.comp hp))).pair (BitCode.Poly.snd.comp hp)
  exact poly_cond poly_completeTest1 ha (poly_cond (poly_completeTest2 hlt) hb1 (poly_cond (poly_completeTest3 hlt) hb2 hb3))
@[fun_prop] theorem poly_fibre : Poly (fun q : List Request × ℕ => fibre q.1 q.2) := by
  unfold fibre Request.target
  exact BitCode.Poly.filterFn (p := fun q : (List Request × ℕ) × Request => equal q.2.2.1 q.1.2)
    (by fun_prop) (by fun_prop)
omit [Inhabited α] [LinearOrder α] in
@[fun_prop] theorem poly_recipients : Poly (fun q : Env α × ℕ × List Request => recipients q.1 q.2.1 q.2.2) := by
  unfold recipients stride
  exact BitCode.Poly.filterFn (p := fun q : (Env α × ℕ × List Request) × ℕ =>
    !(fibre q.1.2.2 (q.1.2.1*q.1.1.2+q.2)).isEmpty) (by fun_prop) (by fun_prop)
@[fun_prop] theorem poly_incoming : Poly (fun q : (Walk α × Env α) × ℕ × List Request => incoming q.1.1 q.1.2 q.2.1 q.2.2) := by
  unfold incoming stride
  have hm : Poly (fun q : (Walk α × Env α) × ℕ × List Request =>
      (recipients q.1.2 q.2.1 q.2.2).map (fun i => fibreSelect q.1.1 q.1.2 (q.2.1*q.1.2.2+i)
        (fibre q.2.2 (q.2.1*q.1.2.2+i)))) :=
    BitCode.Poly.mapFn (f := fun q : ((Walk α × Env α) × ℕ × List Request) × ℕ =>
      fibreSelect q.1.1.1 q.1.1.2 (q.1.2.1*q.1.1.2.2+q.2) (fibre q.1.2.2 (q.1.2.1*q.1.1.2.2+q.2)))
      (by fun_prop) (by fun_prop)
  fun_prop
@[fun_prop] theorem poly_baseIndex : Poly baseIndex := BitCode.Poly.maxFold
@[fun_prop] theorem poly_holes : Poly holes := by
  unfold holes
  exact BitCode.Poly.filterFn (p := fun q : List ℕ × ℕ => !(member q.2 q.1)) (by fun_prop) (by fun_prop)
@[fun_prop] theorem poly_prepare : Poly (fun q : (Walk α × Env α) × ℕ × List Request => prepare q.1.1 q.1.2 q.2.1 q.2.2) := by
  let J := fun q : (Walk α × Env α) × ℕ × List Request => recipients q.1.2 q.2.1 q.2.2
  let r := fun q : (Walk α × Env α) × ℕ × List Request =>
    (fibre q.2.2 (q.2.1*stride q.1.2+baseIndex (J q))).headD (default : Request)
  have hr : Poly r := by unfold r J stride; fun_prop
  have hb : Poly (fun q : (Walk α × Env α) × ℕ × List Request =>
      below (data q.1.2 q.2.1) (holes (J q)) (incoming q.1.1 q.1.2 q.2.1 q.2.2)
        (RecordCode.start (r q).code+RecordCode.offset (r q).code)
        (RecordCode.stop (r q).code+RecordCode.offset (r q).code)) :=
    poly_below.comp (f := fun q : (Walk α × Env α) × ℕ × List Request =>
      ((data q.1.2 q.2.1,holes (J q)),incoming q.1.1 q.1.2 q.2.1 q.2.2,
       RecordCode.start (r q).code+RecordCode.offset (r q).code,
       RecordCode.stop (r q).code+RecordCode.offset (r q).code))
      (by unfold RecordCode.start RecordCode.stop RecordCode.offset Request.code; unfold J; fun_prop)
  unfold prepare
  dsimp only
  fun_prop
abbrev ProcessInput (α : Type) := (Walk α × Env α) × ℕ × ℕ × List Request
@[fun_prop] theorem poly_process (hlt : Poly (fun q : α × α => decide (q.1<q.2))) :
    Poly (fun q : ProcessInput α => process q.1.1 q.1.2 q.2.1 q.2.2.1 q.2.2.2) := by
  have hc := poly_complete hlt
  unfold process
  exact hc.comp (f := fun q : ProcessInput α =>
    (q.1.2,q.2.1,(prepare q.1.1 q.1.2 q.2.1 q.2.2.2).1,q.2.2.1,(prepare q.1.1 q.1.2 q.2.1 q.2.2.2).2)) (by
    have hp := poly_prepare.comp (f := fun q : ProcessInput α => (q.1,q.2.1,q.2.2.2)) (by fun_prop)
    exact (by fun_prop))
end Superstring.CollectionCode


namespace Superstring.CollectionCode
open BitCode Hierarchical LayerArray WalkCode BlockClose
variable {α G : Type} [Inhabited α] [LinearOrder α] {V : Set (List α)}

theorem complete_extras (X : Env α) (g cut M : ℕ) (P Q : Walk α) :
    (complete X g cut M P).2 = (complete X g cut M Q).2 := by
  unfold complete
  dsimp only
  split <;> first | rfl | (split <;> first | rfl | (split <;> rfl))

variable [Coded α]
def extraSizes (X : Env α) (M : ℕ) : List ℕ :=
  (gs X).flatMap (fun g => (List.range ((data X g).2.length+1)).map
    (fun cut => bitSize (complete X g cut M [[]]).2))
def maxExtras (X : Env α) (M : ℕ) : ℕ := (extraSizes X M).foldl max 0

theorem extras_le (X : Env α) (M g cut : ℕ) (hg : g ∈ gs X) (hc : cut ≤ (data X g).2.length) (P : Walk α) :
    bitSize (complete X g cut M P).2 ≤ maxExtras X M := by
  rw [complete_extras X g cut M P [[]]]
  exact le_maxFold _ 0 (List.mem_flatMap.mpr ⟨g,hg,List.mem_map.mpr ⟨cut,List.mem_range.mpr (by omega),rfl⟩⟩)

namespace Model
variable {X : Env α} (vs : Walk α) {C : LayerCollection {w | w ∈ vs} G} (h : Model X C)
theorem process_extra_bound (closed : SubstringClosed {w | w ∈ vs})
    (g : G) (R : List Request) (M : ℕ)
    (valid : ∀ r ∈ R, ValidRequest h r)
    (targets : ∀ r ∈ R, ∃ i : Fin (C.size g), r.target=h.encode ⟨g,i⟩)
    (distinct : SourcesDistinct R) :
    bitSize (process vs X (h.group g) M R).2 ≤ maxExtras X M := by
  have hc := (h.prepare_spec vs closed g R valid targets distinct).1
  unfold process
  apply extras_le
  · exact (h.groups _).mpr ⟨g,rfl⟩
  · rwa [h.size]

theorem advance_extra_bound (closed : SubstringClosed {w | w ∈ vs})
    (M : ℕ) (s : State α) (hs : Invariant h s) :
    bitSize (advance vs X M s).2.2 ≤ bitSize s.2.2+maxExtras X M := by
  by_cases hn : s.1=[]
  · simp only [advance,hn,List.isEmpty_nil,↓reduceIte]
    omega
  · let j := pick X s.1
    have hj := (pick_spec X s.1 hn).1
    obtain ⟨g,hg⟩ := (h.groups j).mp (hs.todo.subset hj)
    let R := inRequests X j s.2.2.2
    have hr : ∀ r ∈ R, ValidRequest h r := fun r hr => hs.good.2.2 r ((mem_inRequests ..).mp hr).1
    have htar : ∀ r ∈ R, ∃ i : Fin (C.size g), r.target=h.encode ⟨g,i⟩ := by
      intro r hr'
      obtain ⟨w⟩ := hr r hr'
      have he : h.group w.target.1=h.group g := by
        rw [← h.owner_eq w.target,w.target_eq,hg]
        exact ((mem_inRequests ..).mp hr').2
      have heg := h.group_inj he
      cases hwt : w.target with
      | mk d i =>
        have hdg : d=g := by simpa only [hwt] using heg
        subst d
        exact ⟨i,by rw [← w.target_eq,hwt]⟩
    have hd : SourcesDistinct R := fun r hr u hu he => hs.distinct r ((mem_inRequests ..).mp hr).1 u ((mem_inRequests ..).mp hu).1 he
    have he := h.process_extra_bound vs closed g R M hr htar hd
    rw [hg] at he
    have hB := bitSize_append s.2.2.1 (process vs X j M R).2.1
    have hR := bitSize_append (restRequests X j s.2.2.2) (process vs X j M R).2.2
    have hsR := bitSize_sublist (List.filter_sublist (p := fun r => !(equal (owner X r.target) j)) (l := s.2.2.2))
    change bitSize (restRequests X j s.2.2.2) ≤ bitSize s.2.2.2 at hsR
    have hp := bitSize_prod (process vs X j M R).2.1 (process vs X j M R).2.2
    have hs := bitSize_prod s.2.2.1 s.2.2.2
    simp only [Prod.eta] at hp hs
    simp only [advance,List.isEmpty_iff,hn,↓reduceIte,bitSize_prod]
    change bitSize (s.2.2.1++(process vs X j M R).2.1)+
      bitSize (restRequests X j s.2.2.2++(process vs X j M R).2.2)≤_
    omega
end Model
end Superstring.CollectionCode


namespace Superstring.CollectionCode
open BitCode Hierarchical LayerArray WalkCode BlockClose
variable {α G : Type} [Inhabited α] [LinearOrder α] {V : Set (List α)}
def initial (X : Env α) : State α := (gs X,[[]],[],[])
theorem advance_nil (vs : Walk α) (X : Env α) (M : ℕ) (P : Plan α) : advance vs X M ([],P)=([],P) := by
  simp only [advance,List.isEmpty_nil,↓reduceIte]
namespace Model
variable {X : Env α} (vs : Walk α) {C : LayerCollection {w | w ∈ vs} G} (h : Model X C)
theorem initial_invariant (nil_mem : ([] : List α) ∈ vs) : Invariant h (initial X) := by
  refine { todo := List.Sublist.refl _, good := ?_, upward := ?_, targets := ?_, sources := ?_, distinct := ?_, ready := ?_ }
  · exact ⟨⟨valid_nil [] nil_mem,rfl,rfl⟩,by simp [initial],by simp [initial]⟩
  · intro g hg j hj _; exact hj
  · simp [initial]
  · simp [initial]
  · intro r hr; cases hr
  · intro i; exact Or.inl ((h.groups _).mpr ⟨i.1,rfl⟩)

variable [Coded α]
theorem iterate_advance (closed : SubstringClosed {w | w ∈ vs}) (supply : C.RecordSupply)
    (M : ℕ) (len : ∀ w ∈ vs, w.length ≤ M) (s : State α) (hs : Invariant h s) (n : ℕ) :
    let t := (advance vs X M)^[n] s
    Invariant h t ∧ budget X t ≤ budget X s ∧ t.1.length ≤ s.1.length-n ∧
      bitSize t.2.2 ≤ bitSize s.2.2+n*maxExtras X M := by
  dsimp only
  induction n with
  | zero => exact ⟨hs,le_rfl,by simp,by simp⟩
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    let t := (advance vs X M)^[n] s
    change Invariant h t ∧ budget X t ≤ budget X s ∧ t.1.length ≤ s.1.length-n ∧
      bitSize t.2.2 ≤ bitSize s.2.2+n*maxExtras X M at ih
    change Invariant h (advance vs X M t) ∧ budget X (advance vs X M t) ≤ budget X s ∧
      (advance vs X M t).1.length ≤ s.1.length-(n+1) ∧
      bitSize (advance vs X M t).2.2 ≤ bitSize s.2.2+(n+1)*maxExtras X M
    by_cases hn : t.1=[]
    · have ht : advance vs X M t=t := by rw [← Prod.eta t,hn,advance_nil]
      rw [ht]
      refine ⟨ih.1,ih.2.1,by simp [hn],?_⟩
      have hh := ih.2.2.2
      rw [Nat.succ_mul]
      omega
    · have hh := h.advance_spec vs closed supply M len t ih.1 hn
      have he := h.advance_extra_bound vs closed M t ih.1
      refine ⟨hh.1,hh.2.1.trans ih.2.1,?_,?_⟩
      · have h1 := hh.2.2; have h2 := ih.2.2.1; change (advance vs X M t).1.length ≤ _; omega
      · have h1 := ih.2.2.2; rw [Nat.succ_mul]; omega
end Model
end Superstring.CollectionCode

end OAI
