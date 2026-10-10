import OAI.Computability.Superstring.BlockClose

namespace OAI

namespace Superstring.BlockFactory
open BitCode Hierarchical WalkCode LayerArray BlockClose
variable {α : Type} [Coded α] [Inhabited α] [DecidableEq α]
abbrev PackInput (α : Type) := (GroupData α × ℕ × ℕ × ℕ) × (List ℕ × ℤ × ℤ) × (Walk α × List (Walk α))
instance codedPackInput : Coded (PackInput α) := codedProd
omit [DecidableEq α] in
@[fun_prop] theorem poly_pack : Poly (fun q : PackInput α =>
    pack q.1.1 q.1.2.1 q.1.2.2.1 q.1.2.2.2 q.2.1.1 q.2.1.2.1 q.2.1.2.2 q.2.2.1 q.2.2.2) := by
  unfold pack
  have hm : Poly (fun q : PackInput α => q.2.1.1.map (q.1.2.2.2+·)) :=
    BitCode.Poly.mapFn (f := fun q : PackInput α × ℕ => q.1.1.2.2.2+q.2) (by fun_prop) (by fun_prop)
  fun_prop
abbrev IndividualInput (α : Type) := (GroupData α × ℕ × ℕ × ℕ) × (ℕ × ℤ × ℤ)
instance codedIndividualInput : Coded (IndividualInput α) := codedProd
@[fun_prop] theorem poly_individual : Poly (fun q : IndividualInput α =>
    individual q.1.1 q.1.2.1 q.1.2.2.1 q.1.2.2.2 q.2.1 q.2.2.1 q.2.2.2) := by
  unfold individual
  exact poly_pack.comp
    (f := fun q : IndividualInput α => (q.1,([q.2.1],q.2.2),
      (turn q.1.1.1 (exits q.1.1 q.2.1),[LayerArray.individual q.1.1 q.2.1 q.2.2.1 q.2.2.2]))) (by fun_prop)
abbrev CollectiveInput (α : Type) := (GroupData α × ℕ × ℕ × ℕ) × (List ℕ × ℕ × ℕ) × (ℤ × ℤ × ℤ)
instance codedCollectiveInput : Coded (CollectiveInput α) := codedProd
@[fun_prop] theorem poly_collective : Poly (fun q : CollectiveInput α =>
    collective q.1.1 q.1.2.1 q.1.2.2.1 q.1.2.2.2 q.2.1.1 q.2.1.2.1 q.2.1.2.2 q.2.2.1 q.2.2.2.1 q.2.2.2.2) := by
  unfold collective
  exact poly_pack.comp
    (f := fun q : CollectiveInput α => (q.1,(q.2.1.1,q.2.2.1,q.2.2.2.1),
      (band q.1.1 q.2.1.1 q.2.1.2.1 q.2.1.2.2 (q.2.1.1.length-1) q.2.2.2.2,
       [LayerArray.collective q.1.1 q.2.1.1 q.2.1.2.2 q.2.2.1 q.2.2.2.1,
        shortSweep q.1.1 q.2.1.1 q.2.1.2.2 q.2.2.1 q.2.2.2.1 q.2.2.2.2]))) (by fun_prop)
end Superstring.BlockFactory


namespace Superstring.LayerArray
open BitCode Hierarchical WalkCode
variable {α : Type} [Inhabited α] [DecidableEq α]
def shortWords (D : GroupData α) (i : ℕ) : List (List α) :=
  (content D.1 (exits D i)).filter (fun w => lessEq w.length D.1.length)
def hasShort (D : GroupData α) (i : ℕ) : Bool := !(shortWords D i).isEmpty
def shortLoop (D : GroupData α) (i : ℕ) : Walk α :=
  rootContent D [i] ((shortWords D i).headD [])

omit [DecidableEq α] in
theorem hasShort_eq {V : Set (List α)} {A : ℤ → α} {p : ℕ}
    {D : GroupData α} {i : ℕ} {L : Layer V A p}
    (h : Represents D.1 (exits D i) L) (hp : 0 < p) (per : Function.Periodic A (p : ℤ)) :
    hasShort D i = true ↔ L.HasShort p := by
  simp only [hasShort,Bool.not_eq_true',List.isEmpty_eq_false_iff]
  constructor
  · intro hn
    obtain ⟨w,hw⟩ := List.exists_mem_of_ne_nil _ hn
    obtain ⟨hw,hl⟩ := List.mem_filter.mp (show w ∈ (content D.1 (exits D i)).filter (fun w => lessEq w.length D.1.length) from hw)
    obtain ⟨x,e,hf,he,rfl⟩ := (mem_content h hp per w).mp hw
    refine ⟨x,e,hf,he,?_⟩
    simpa only [lessEq,decide_eq_true_eq,h.length_eq,length_textWord] using hl
  · rintro ⟨x,e,hf,he,hl⟩
    have hm : textWord A x e ∈ shortWords D i := by
      apply List.mem_filter.mpr
      exact ⟨(mem_content h hp per _).mpr ⟨x,e,hf,he,rfl⟩,
        by simpa only [lessEq,decide_eq_true_eq,h.length_eq,length_textWord] using hl⟩
    exact fun hn => by rw [hn] at hm; exact List.not_mem_nil hm

theorem shortLoop_spec {V : Set (List α)} {A : ℤ → α} {p : ℕ}
    (L : ℕ → Layer V A p) {D : GroupData α} {i : ℕ}
    (h : Represents D.1 (exits D i) (L i)) (closed : SubstringClosed V)
    (hp : 0 < p) (per : Function.Periodic A (p : ℤ)) (hs : hasShort D i = true) :
    Runs V [] [] (shortLoop D i) ∧ cost (shortLoop D i) ≤ 2*p ∧
      ∀ w ∈ (L i).Content, w ∈ shortLoop D i := by
  have hn : shortWords D i ≠ [] := by simpa only [hasShort,Bool.not_eq_true',List.isEmpty_eq_false_iff] using hs
  have hm : (shortWords D i).headD [] ∈ shortWords D i := by
    generalize shortWords D i = X at hn ⊢
    cases X with
    | nil => exact False.elim (hn rfl)
    | cons w X => exact List.mem_cons_self ..
  change (shortWords D i).headD [] ∈ (content D.1 (exits D i)).filter (fun w => lessEq w.length D.1.length) at hm
  obtain ⟨hm,hl⟩ := List.mem_filter.mp hm
  have hw := (mem_content h hp per _).mp hm
  have hlen : ((shortWords D i).headD []).length ≤ p := by
    simpa only [lessEq,decide_eq_true_eq,h.length_eq] using hl
  obtain ⟨hr,hc,hv⟩ := rootContent_spec L (D:=D) (js:=[i])
    (by intro j hj; have := List.mem_singleton.mp hj; subst j; exact h)
    closed hp per ((L i).content_mem hw)
    (by intro j hj; have := List.mem_singleton.mp hj; subst j; exact ⟨_,hw,List.prefix_refl _⟩)
  refine ⟨hr,?_,hv i (by simp)⟩
  change cost (rootContent D [i] ((shortWords D i).headD [])) ≤ _
  rw [hc]
  simp only [List.length_singleton,one_mul]
  omega

variable [Coded α]
omit [DecidableEq α] in
@[fun_prop] theorem poly_shortWords : Poly (fun q : GroupData α × ℕ => shortWords q.1 q.2) := by
  unfold shortWords
  exact BitCode.Poly.filterFn
    (p := fun q : (GroupData α × ℕ) × List α => lessEq q.2.length q.1.1.1.length) (by fun_prop) (by fun_prop)
omit [DecidableEq α] in
@[fun_prop] theorem poly_hasShort : Poly (fun q : GroupData α × ℕ => hasShort q.1 q.2) := by
  unfold hasShort
  fun_prop
@[fun_prop] theorem poly_shortLoop : Poly (fun q : GroupData α × ℕ => shortLoop q.1 q.2) := by
  unfold shortLoop
  exact poly_rootContent.comp (f := fun q : GroupData α × ℕ => (q.1,[q.2],(shortWords q.1 q.2).headD [])) (by fun_prop)
end Superstring.LayerArray


namespace Superstring.BlockClose
open BitCode Hierarchical WalkCode
variable {α : Type} [DecidableEq α] [Inhabited α]

theorem step_nil (vs : Walk α) (L : List (Walk α)) (P : Walk α) : step vs L (P,[]) = (P,[]) := by
  simp [step,select,pool,remaining]

variable {β : Type} [LinearOrder β]
theorem iterate_step (vs : Walk α) (closed : SubstringClosed {w | w ∈ vs}) (L : List (Walk α))
    (ids : List ℕ) (owner per : ℕ → ℕ) (rank : ℕ → β) (s : State α)
    (hP : Runs {w | w ∈ vs} [] [] s.1)
    (valid : ∀ b ∈ s.2, ValidBlock {w | w ∈ vs} ids (lookup L) owner per rank b)
    (ready : ∀ i ∈ ids, (∀ w ∈ lookup L i, w ∈ s.1) ∨ ∃ b ∈ s.2, i ∈ b.members) (n : ℕ) :
    let t := (step vs L)^[n] s
    Runs {w | w ∈ vs} [] [] t.1 ∧
      cost t.1+(t.2.map Block.reserve).sum ≤ cost s.1+(s.2.map Block.reserve).sum ∧
      (∀ w ∈ s.1, w ∈ t.1) ∧ t.2.Sublist s.2 ∧ t.2.length ≤ s.2.length-n ∧
      ∀ i ∈ ids, (∀ w ∈ lookup L i, w ∈ t.1) ∨ ∃ b ∈ t.2, i ∈ b.members := by
  dsimp only
  induction n with
  | zero => exact ⟨hP,le_rfl,fun _ h => h,List.Sublist.refl _,by simp,ready⟩
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    let t := (step vs L)^[n] s
    change Runs _ [] [] t.1 ∧ _ at ih
    by_cases hn : t.2 = []
    · have he : step vs L t = t := by
        rw [← Prod.eta t,hn,step_nil]
      rw [he]
      exact ⟨ih.1,ih.2.1,ih.2.2.1,ih.2.2.2.1,by simp [hn],ih.2.2.2.2.2⟩
    · obtain ⟨hQ,hcost,hvis,hsub,hlen,hr⟩ := step_spec vs closed L ids owner per rank t ih.1 hn
        (fun b hb => valid b (ih.2.2.2.1.subset hb)) ih.2.2.2.2.2
      exact ⟨hQ,hcost.trans ih.2.1,fun w hw => hvis w (ih.2.2.1 w hw),hsub.trans ih.2.2.2.1,
        by change (step vs L t).2.length ≤ _; have hh : t.2.length ≤ s.2.length-n := ih.2.2.2.2.1; omega,hr⟩

omit [DecidableEq α] [Inhabited α] [LinearOrder β] in
theorem rooted_length {V : Set (List α)} {P : Walk α} (hP : Runs V [] [] P) :
    P.length = 2*cost P+1 := by
  cases P with
  | nil => exact False.elim (hP.1.1 rfl)
  | cons a P =>
    have ha : a = [] := by simpa using hP.2.1
    subst a
    have h := length_cost hP.1
    simp only [hP.2.2,Option.getD_some,List.length_nil,Nat.add_zero] at h
    simpa only [List.length_cons] using congrArg (·+1) h

variable [Coded α]
abbrev Input (α : Type) := (Walk α × List (Walk α)) × State α
def iterStep (q : Input α) : Input α := (q.1,step q.1.1 q.1.2 q.2)
def capacity (q : Input α) : ℕ :=
  2*bitSize q + 1 + (2*(cost q.2.1+(q.2.2.map Block.reserve).sum)+1)*(bitSize q+1)
def close (q : Input α) : Walk α :=
  (((cappedStep iterStep)^[q.2.2.length] (capacity q,q)).2).2.1

omit [LinearOrder β] [Coded α] in
theorem iterate_iterStep (q : Input α) (n : ℕ) :
    iterStep^[n] q = (q.1,(step q.1.1 q.1.2)^[n] q.2) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply',ih,Function.iterate_succ_apply']; rfl

omit [LinearOrder β] [DecidableEq α] [Inhabited α] in
theorem state_size (q : Input α) (t : State α)
    (hP : Runs {w | w ∈ q.1.1} [] [] t.1)
    (hcost : cost t.1 ≤ cost q.2.1+(q.2.2.map Block.reserve).sum)
    (hsub : t.2.Sublist q.2.2) : bitSize (q.1,t) ≤ capacity q := by
  have eqQ : bitSize q = bitSize q.1+bitSize q.2 := bitSize_prod q.1 q.2
  have eqCtx : bitSize q.1 = bitSize q.1.1+bitSize q.1.2 := bitSize_prod q.1.1 q.1.2
  have eqS : bitSize q.2 = bitSize q.2.1+bitSize q.2.2 := bitSize_prod q.2.1 q.2.2
  have eqT : bitSize t = bitSize t.1+bitSize t.2 := bitSize_prod t.1 t.2
  have eqOut : bitSize (q.1,t) = bitSize q.1+bitSize t := bitSize_prod q.1 t
  have hv : ∀ w ∈ t.1, bitSize w ≤ bitSize q := by
    intro w hw
    have hm := bitSize_mem (hP.1.2.1 w hw)
    omega
  have hh := bitSize_map_le t.1 (fun w => w) (bitSize q) hv
  have hid : t.1.map (fun w => w) = t.1 := by simp
  rw [hid,rooted_length hP] at hh
  have hb := bitSize_sublist hsub
  unfold capacity
  nlinarith

theorem close_spec (q : Input α) (closed : SubstringClosed {w | w ∈ q.1.1})
    (ids : List ℕ) (owner per : ℕ → ℕ) (rank : ℕ → β)
    (hP : Runs {w | w ∈ q.1.1} [] [] q.2.1)
    (valid : ∀ b ∈ q.2.2, ValidBlock {w | w ∈ q.1.1} ids (lookup q.1.2) owner per rank b)
    (ready : ∀ i ∈ ids, (∀ w ∈ lookup q.1.2 i, w ∈ q.2.1) ∨ ∃ b ∈ q.2.2, i ∈ b.members) :
    Runs {w | w ∈ q.1.1} [] [] (close q) ∧
      cost (close q) ≤ cost q.2.1+(q.2.2.map Block.reserve).sum ∧
      (∀ w ∈ q.2.1, w ∈ close q) ∧ Covers (lookup q.1.2) ids (close q) := by
  have hi := iterate_step q.1.1 closed q.1.2 ids owner per rank q.2 hP valid ready
  have he := iterate_cappedStep_eq iterStep q.2.2.length (capacity q) q (by
    intro n _ _
    rw [iterate_iterStep]
    exact state_size q _ (hi n).1 (by have := (hi n).2.1; omega) (hi n).2.2.2.1)
  unfold close
  rw [he,iterate_iterStep]
  dsimp only
  have hh := hi q.2.2.length
  have hz : ((step q.1.1 q.1.2)^[q.2.2.length] q.2).2 = [] := by
    apply List.length_eq_zero_iff.mp
    have := hh.2.2.2.2.1; omega
  refine ⟨hh.1,by have := hh.2.1; omega,hh.2.2.1,?_⟩
  intro i hi
  rcases hh.2.2.2.2.2 i hi with h | ⟨b,hb,_⟩
  · exact h
  · rw [hz] at hb; exact False.elim (List.not_mem_nil hb)

omit [LinearOrder β] in
@[fun_prop] theorem poly_iterStep : Poly (iterStep : Input α → Input α) := by
  exact BitCode.Poly.fst.pair poly_step
omit [LinearOrder β] [DecidableEq α] [Inhabited α] in
@[fun_prop] theorem poly_capacity : Poly (capacity : Input α → ℕ) := by
  have hr : Poly (fun q : Input α => (q.2.2.map Block.reserve).sum) := poly_reserves.comp (by fun_prop)
  unfold capacity
  fun_prop
omit [LinearOrder β] in
@[fun_prop] theorem poly_close : Poly (close : Input α → Walk α) := by
  have ht : Poly (fun q : Input α => ((cappedStep iterStep)^[q.2.2.length] (capacity q,q)).2) :=
    (BitCode.Poly.cappedIterate poly_iterStep).comp
      (f := fun q : Input α => (q.2.2.length,(capacity q,q))) (by fun_prop)
  exact BitCode.Poly.fst.comp (BitCode.Poly.snd.comp ht)
end Superstring.BlockClose


namespace Superstring.WalkCode
open Hierarchical BitCode
variable {α : Type}
def collect (Ps : List (Walk α)) : Walk α := Ps.foldl join [[]]

theorem fold_join_spec {V : Set (List α)} (Ps : List (Walk α)) (P : Walk α)
    (hP : Runs V [] [] P) (h : ∀ Q ∈ Ps, Runs V [] [] Q) :
    Runs V [] [] (Ps.foldl join P) ∧
      cost (Ps.foldl join P) = cost P+(Ps.map cost).sum ∧
      (∀ w ∈ P, w ∈ Ps.foldl join P) ∧
      ∀ Q ∈ Ps, ∀ w ∈ Q, w ∈ Ps.foldl join P := by
  induction Ps generalizing P with
  | nil => exact ⟨hP,by simp,fun _ hw => hw,by simp⟩
  | cons Q Ps ih =>
    have hQ := h Q (List.mem_cons_self ..)
    obtain ⟨hr,hc,hv,ha⟩ := ih (join P Q) (runs_join hP hQ)
      (fun R hR => h R (List.mem_cons_of_mem _ hR))
    refine ⟨hr,?_,?_,?_⟩
    · simp only [List.foldl_cons,List.map_cons,List.sum_cons,hc,cost_join P Q [] hP.2.2 hQ.2.1]
      omega
    · intro w hw; exact hv w ((mem_join hP.2.2 hQ.2.1).mpr (Or.inl hw))
    · intro R hR w hw
      rcases List.mem_cons.mp hR with rfl|hR
      · exact hv w ((mem_join hP.2.2 hQ.2.1).mpr (Or.inr hw))
      · exact ha R hR w hw

theorem collect_spec {V : Set (List α)} (h0 : ([] : List α) ∈ V)
    (Ps : List (Walk α)) (h : ∀ Q ∈ Ps, Runs V [] [] Q) :
    Runs V [] [] (collect Ps) ∧ cost (collect Ps) = (Ps.map cost).sum ∧
      ∀ Q ∈ Ps, ∀ w ∈ Q, w ∈ collect Ps := by
  have hh := fold_join_spec Ps [[]] ⟨valid_nil [] h0,rfl,rfl⟩ h
  exact ⟨hh.1,by simpa only [collect,cost_singleton,Nat.zero_add] using hh.2.1,hh.2.2.2⟩

variable [Coded α]
@[fun_prop] theorem poly_collect : Poly (collect : List (Walk α) → Walk α) := by
  have hs : ∀ P Q : Walk α, bitSize (join P Q) ≤ bitSize P + (Polynomial.X : Polynomial ℕ).eval (bitSize Q) := by
    intro P Q
    simpa only [Polynomial.eval_X] using size_join P Q
  exact (BitCode.Poly.foldl_additive poly_join Polynomial.X hs).comp
    (f := fun Ps : List (Walk α) => (Ps,[[]])) (by fun_prop)
end Superstring.WalkCode

end OAI
