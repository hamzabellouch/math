import OAI.Combinatorics.VariableWL.OneHead

namespace OAI

universe uVariable1 uVariable2 uVariable3 uVariable4 uVariable5 uVariable6 uVariable7 uVariable8 uVariable9 uVariable10 uVariable11 uVariable12 uVariable13 uVariable14 uVariable15 uVariable16 uVariable17 uVariable18 uVariable19

namespace VariableWL.OneHead
variable {Q : Type uVariable1} {Γ : Type uVariable2} {A : Type uVariable3} {B : Type uVariable4} [AddCommGroup A] [AddCommGroup B] [DecidableEq A] [DecidableEq B]

def Related (f : A →+ B) (S : Set A) (s : State Q Γ A) (t : State Q Γ B) : Prop :=
  t.control=s.control ∧ t.head=f s.head ∧ ∀ i ∈ S, t.cells (f i)=s.cells i

theorem next_related (M : Program Q Γ) (u : A) (v : B) (f : A →+ B) (S : Set A)
    (hf : Set.InjOn f S) (hu : f u=v) (s : State Q Γ A) (t : State Q Γ B)
    (hr : Related f S s t) (hs : s.head ∈ S) :
    Related f S (M.next u s) (M.next v t) := by
  classical
  obtain ⟨hq,hh,hc⟩ := hr
  have ha : M.action t.control (t.cells t.head)=M.action s.control (s.cells s.head) := by
    rw [hq,hh,hc s.head hs]
  refine ⟨?_,?_,?_⟩
  · change (M.action t.control (t.cells t.head)).1=(M.action s.control (s.cells s.head)).1
    rw [ha]
  · change move v (M.action t.control (t.cells t.head)).2.2 t.head=
      f (move u (M.action s.control (s.cells s.head)).2.2 s.head)
    rw [ha,hh]
    cases (M.action s.control (s.cells s.head)).2.2 <;> simp [move,hu]
  · intro i hi
    change Function.update t.cells t.head (M.action t.control (t.cells t.head)).2.1 (f i)=
      Function.update s.cells s.head (M.action s.control (s.cells s.head)).2.1 i
    rw [ha,hh]
    by_cases he : i=s.head
    · subst i
      simp only [Function.update_self]
    · have hne : f i ≠ f s.head := fun h => he (hf hi hs h)
      rw [Function.update_of_ne hne,Function.update_of_ne he,hc i hi]

theorem run_related (M : Program Q Γ) (u : A) (v : B) (f : A →+ B) (S : Set A)
    (hf : Set.InjOn f S) (hu : f u=v) (s : State Q Γ A) (t : State Q Γ B)
    (hr : Related f S s t) (T : ℕ) (hs : ∀ n < T, (M.run u s n).head ∈ S) :
    Related f S (M.run u s T) (M.run v t T) := by
  induction T with
  | zero => exact hr
  | succ T ih =>
    exact next_related M u v f S hf hu _ _ (ih (fun n hn => hs n (by omega))) (hs T (by omega))

def window (T : ℕ) : Set ℤ := {i | -(T:ℤ) ≤ i ∧ i ≤ T}

theorem cast_injOn_window (N T : ℕ) (hN : 2*T < N) :
    Set.InjOn (Int.castAddHom (ZMod N)) (window T) := by
  intro a ha b hb he
  change (a : ZMod N)=(b : ZMod N) at he
  have hd := (ZMod.intCast_eq_intCast_iff_dvd_sub a b N).mp he
  have hab : -(N:ℤ) < b-a ∧ b-a < N := by
    have : (2:ℤ)*T < N := by exact_mod_cast hN
    obtain ⟨ha,ha'⟩ := ha
    obtain ⟨hb,hb'⟩ := hb
    omega
  obtain ⟨k,hk⟩ := hd
  have hNp : (0:ℤ)<N := by exact_mod_cast (show 0<N by omega)
  have hk0 : k=0 := by
    by_contra hh
    rcases lt_or_gt_of_ne hh with hn | hp
    · have hk1 : k ≤ -1 := by omega
      have hh := mul_le_mul_of_nonneg_left hk1 (le_of_lt hNp)
      omega
    · have hk1 : 1 ≤ k := by omega
      have hh := mul_le_mul_of_nonneg_left hk1 (le_of_lt hNp)
      omega
  rw [hk0,mul_zero] at hk
  omega

variable {m : ℕ}

def lineInput (blank : Γ) (w : Fin m → Γ) (i : ℤ) : Γ :=
  if h : 0 ≤ i ∧ i < m then w ⟨i.toNat,by omega⟩ else blank

def ringInput (N : ℕ) (blank : Γ) (w : Fin m → Γ) (i : ZMod N) : Γ :=
  if h : i.val < m then w ⟨i.val,h⟩ else blank

theorem ringInput_cast (N T : ℕ) (hN : 2*T < N) (hm : m ≤ T)
    (blank : Γ) (w : Fin m → Γ) (i : ℤ) (hi : i ∈ window T) :
    ringInput N blank w (i : ZMod N)=lineInput blank w i := by
  have hNp : 0<N := by omega
  let : NeZero N := ⟨by omega⟩
  obtain ⟨hil,hir⟩ := hi
  by_cases h0 : 0 ≤ i
  · have hin : i < N := by omega
    have hv : ((i : ZMod N).val:ℤ)=i := by
      rw [ZMod.val_intCast,Int.emod_eq_of_lt h0 hin]
    have hvn : (i : ZMod N).val=i.toNat := by omega
    unfold ringInput lineInput
    split_ifs with h h'
    · congr 1
      apply Fin.ext
      exact hvn
    · omega
    · omega
    · rfl
  · have hmod : i % N=i+N := by
      have hmod0 : 0 ≤ i+(N:ℤ) := by omega
      have hmodN : i+(N:ℤ)<N := by omega
      have hx := Int.emod_eq_of_lt hmod0 hmodN
      simpa only [Int.add_emod_right] using hx
    have hv : ((i : ZMod N).val:ℤ)=i+N := by rw [ZMod.val_intCast,hmod]
    have hm' : ¬(i : ZMod N).val < m := by omega
    simp only [ringInput,hm',dite_false,lineInput,h0,false_and]

def lineInitial (M : Program Q Γ) (blank : Γ) (w : Fin m → Γ) : State Q Γ ℤ :=
  ⟨M.start,0,lineInput blank w⟩

def ringInitial (M : Program Q Γ) (N : ℕ) (blank : Γ) (w : Fin m → Γ) : State Q Γ (ZMod N) :=
  ⟨M.start,0,ringInput N blank w⟩

theorem initial_related (M : Program Q Γ) (N T : ℕ) (hN : 2*T<N) (hm : m ≤ T)
    (blank : Γ) (w : Fin m → Γ) :
    Related (Int.castAddHom (ZMod N)) (window T) (lineInitial M blank w) (ringInitial M N blank w) := by
  refine ⟨rfl,by simp [ringInitial,lineInitial],?_⟩
  intro i hi
  exact ringInput_cast N T hN hm blank w i hi

theorem line_ring_related (M : Program Q Γ) (N T : ℕ) (hN : 2*T<N) (hm : m ≤ T)
    (blank : Γ) (w : Fin m → Γ) (t : ℕ) (ht : t ≤ T) :
    Related (Int.castAddHom (ZMod N)) (window T)
      (M.run 1 (lineInitial M blank w) t) (M.run 1 (ringInitial M N blank w) t) := by
  apply run_related M 1 1 (Int.castAddHom (ZMod N)) (window T)
      (cast_injOn_window N T hN) (by simp) _ _ (initial_related M N T hN hm blank w) t
  intro n hn
  obtain ⟨hl,hr⟩ := head_bounds M (lineInitial M blank w) n
  change 0-(n:ℤ) ≤ _ at hl
  change _ ≤ 0+(n:ℤ) at hr
  constructor <;> omega

theorem line_ring_acceptance (M : Program Q Γ) (N T : ℕ) (hN : 2*T<N) (hm : m ≤ T)
    (blank : Γ) (w : Fin m → Γ) (t : ℕ) (ht : t ≤ T) :
    M.accepting (M.run 1 (ringInitial M N blank w) t).control
      ((M.run 1 (ringInitial M N blank w) t).cells (M.run 1 (ringInitial M N blank w) t).head) =
    M.accepting (M.run 1 (lineInitial M blank w) t).control
      ((M.run 1 (lineInitial M blank w) t).cells (M.run 1 (lineInitial M blank w) t).head) := by
  obtain ⟨hq,hh,hc⟩ := line_ring_related M N T hN hm blank w t ht
  rw [hq,hh,hc]
  obtain ⟨hl,hr⟩ := head_bounds M (lineInitial M blank w) t
  change 0-(t:ℤ) ≤ _ at hl
  change _ ≤ 0+(t:ℤ) at hr
  constructor <;> omega

end VariableWL.OneHead

namespace VariableWL.OneHead
variable {Q : Type uVariable5} {Γ : Type uVariable6} {m d : ℕ}

def markedInput (M : Program Q Γ) (w : Fin m → Γ) (j : Fin m) : Cell Q Γ :=
  (w j, if j.val=0 then some M.start else none)

noncomputable def product (M : Program Q Γ) (blank : Γ) (w : Fin m → Γ)
    (hfit : m < 2^d) : Circuit.ProductCellular.Data (Cell Q Γ) d m where
  rule := M.rule
  input := markedInput M w
  blank := (blank,none)
  accepting := M.acceptingCell
  fits := hfit

theorem finEquiv_val (N : ℕ) [NeZero N] (j : Fin N) : (ZMod.finEquiv N j).val=j.val := by
  cases N with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ N => rfl

theorem product_initial (M : Program Q Γ) (blank : Γ) (w : Fin m → Γ)
    (hfit : m < 2^d) (hm : 0 < m) (j : Fin (2^d)) :
    (product M blank w hfit).initial j =
      encode (ringInitial M (2^d) blank w) (ZMod.finEquiv (2^d) j) := by
  have hf : (ZMod.finEquiv (2^d) j).val=j.val := finEquiv_val _ j
  have hz : ZMod.finEquiv (2^d) j=0 ↔ j.val=0 := by
    rw [← (ZMod.finEquiv (2^d)).map_zero,(ZMod.finEquiv (2^d)).injective.eq_iff]
    exact Fin.ext_iff
  unfold Circuit.ProductCellular.Data.initial product
  dsimp only [encode,ringInitial,ringInput,markedInput]
  rw [hf]
  by_cases h : j.val < m
  · simp only [dite_eq_left h,hz]
  · have hj : j.val ≠ 0 := by omega
    simp only [dite_eq_right h,hz,hj,ite_false]

theorem product_state (M : Program Q Γ) (blank : Γ) (w : Fin m → Γ)
    (hfit : m < 2^d) (hm : 0 < m) (t : ℕ) (j : Fin (2^d)) :
    (product M blank w hfit).state t j =
      encode (M.run 1 (ringInitial M (2^d) blank w) t) (ZMod.finEquiv (2^d) j) := by
  induction t generalizing j with
  | zero => exact product_initial M blank w hfit hm j
  | succ t ih =>
    change M.rule ((product M blank w hfit).state t (j-1))
      ((product M blank w hfit).state t j) ((product M blank w hfit).state t (j+1)) = _
    rw [ih,ih,ih]
    simp only [map_sub,map_one,map_add]
    exact rule_encode M 1 _ _

theorem product_acceptance (M : Program Q Γ) (blank : Γ) (w : Fin m → Γ)
    (hfit : m < 2^d) (hm : 0 < m) (T t : ℕ) (hN : 2*T < 2^d) (hmT : m ≤ T) (ht : t ≤ T) :
    (∃ j, (product M blank w hfit).state t j ∈ (product M blank w hfit).accepting) ↔
    M.accepting (M.run 1 (lineInitial M blank w) t).control
      ((M.run 1 (lineInitial M blank w) t).cells (M.run 1 (lineInitial M blank w) t).head)=true := by
  have he : (∃ j, (product M blank w hfit).state t j ∈ (product M blank w hfit).accepting) ↔
      ∃ i : ZMod (2^d), M.acceptingCell (encode (M.run 1 (ringInitial M (2^d) blank w) t) i) := by
    constructor
    · rintro ⟨j,hj⟩
      exact ⟨ZMod.finEquiv _ j,by
        change M.acceptingCell _ at hj
        simpa only [product_state M blank w hfit hm] using hj⟩
    · rintro ⟨i,hi⟩
      obtain ⟨j,rfl⟩ := (ZMod.finEquiv (2^d)).surjective i
      exact ⟨j,by
        change M.acceptingCell _
        simpa only [product_state M blank w hfit hm] using hi⟩
  rw [he,accepting_encode,line_ring_acceptance M (2^d) T hN hmT blank w t ht]

end VariableWL.OneHead

namespace VariableWL.OneHead
variable {Q : Type uVariable7} {Γ : Type uVariable8} {m d : ℕ}

theorem line_ring_halt (M : Program Q Γ) (N T : ℕ) (hN : 2*T<N) (hm : m ≤ T)
    (blank : Γ) (w : Fin m → Γ) (t : ℕ) (ht : t ≤ T)
    (h : M.transition (M.run 1 (lineInitial M blank w) t).control
      ((M.run 1 (lineInitial M blank w) t).cells (M.run 1 (lineInitial M blank w) t).head)=none) :
    M.transition (M.run 1 (ringInitial M N blank w) t).control
      ((M.run 1 (ringInitial M N blank w) t).cells (M.run 1 (ringInitial M N blank w) t).head)=none := by
  obtain ⟨hq,hh,hc⟩ := line_ring_related M N T hN hm blank w t ht
  rw [hq,hh,hc]
  · exact h
  · obtain ⟨hl,hr⟩ := head_bounds M (lineInitial M blank w) t
    change 0-(t:ℤ) ≤ _ at hl
    change _ ≤ 0+(t:ℤ) at hr
    constructor <;> omega

theorem product_final_acceptance (M : Program Q Γ) (blank : Γ) (w : Fin m → Γ)
    (hfit : m < 2^d) (hm : 0 < m) (T t : ℕ) (hN : 2*T < 2^d) (hmT : m ≤ T) (ht : t ≤ T)
    (halt : M.transition (M.run 1 (lineInitial M blank w) t).control
      ((M.run 1 (lineInitial M blank w) t).cells (M.run 1 (lineInitial M blank w) t).head)=none) :
    (∃ j, (product M blank w hfit).state (2^d-1) j ∈ (product M blank w hfit).accepting) ↔
    M.accepting (M.run 1 (lineInitial M blank w) t).control
      ((M.run 1 (lineInitial M blank w) t).cells (M.run 1 (lineInitial M blank w) t).head)=true := by
  have hf := run_freeze M (1 : ZMod (2^d)) (ringInitial M (2^d) blank w) t (2^d-1)
    (by omega) (line_ring_halt M (2^d) T hN hmT blank w t ht halt)
  have he : ∀ j, (product M blank w hfit).state (2^d-1) j=(product M blank w hfit).state t j := by
    intro j
    rw [product_state M blank w hfit hm,product_state M blank w hfit hm,hf]
  simp only [he]
  exact product_acceptance M blank w hfit hm T t hN hmT ht

theorem product_consistent_iff (M : Program Q Γ) (blank : Γ) (w : Fin m → Γ)
    (hfit : m < 2^d) (hm : 0 < m) (T t : ℕ) (hN : 2*T < 2^d) (hmT : m ≤ T) (ht : t ≤ T)
    (halt : M.transition (M.run 1 (lineInitial M blank w) t).control
      ((M.run 1 (lineInitial M blank w) t).cells (M.run 1 (lineInitial M blank w) t).head)=none) :
    (product M blank w hfit).description.consistency.Consistent ↔
    M.accepting (M.run 1 (lineInitial M blank w) t).control
      ((M.run 1 (lineInitial M blank w) t).cells (M.run 1 (lineInitial M blank w) t).head)=false := by
  rw [Circuit.ProductCellular.Data.consistency_iff]
  have h := product_final_acceptance M blank w hfit hm T t hN hmT ht halt
  simpa only [not_exists,Bool.not_eq_true] using not_congr h

end VariableWL.OneHead

namespace VariableWL.BoundedSimulation

inductive Steps {S : Type uVariable9} (f : S → Option S) : ℕ → S → S → Prop where
  | zero (a) : Steps f 0 a a
  | succ {n a b c} : f a=some b → Steps f n b c → Steps f (n+1) a c

namespace Steps
variable {S : Type uVariable10} {f : S → Option S} {a b c : S} {n m : ℕ}
theorem trans (h : Steps f n a b) (h' : Steps f m b c) : Steps f (n+m) a c := by
  induction h with
  | zero => simpa only [Nat.zero_add] using h'
  | @succ n a b c hab h ih => simpa only [Nat.succ_add] using Steps.succ hab (ih h')

theorem single (h : f a=some b) : Steps f 1 a b := Steps.succ h (Steps.zero b)

theorem tail (h : Steps f n a b) (h' : f b=some c) : Steps f (n+1) a c := h.trans (single h')

theorem head (h : f a=some b) (h' : Steps f n b c) : Steps f (n+1) a c := Steps.succ h h'
end Steps

noncomputable def evolve {S : Type uVariable11} (f : S → Option S) (a : S) : ℕ → S
  | 0 => a
  | t+1 => (f (evolve f a t)).getD (evolve f a t)

theorem evolve_add {S : Type uVariable12} (f : S → Option S) (a : S) (n m : ℕ) :
    evolve f a (n+m)=evolve f (evolve f a n) m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    change (f (evolve f a (n+m))).getD (evolve f a (n+m))=
      (f (evolve f (evolve f a n) m)).getD (evolve f (evolve f a n) m)
    rw [ih]

theorem Steps.evolve {S : Type uVariable13} {f : S → Option S} {n : ℕ} {a b : S}
    (h : Steps f n a b) : evolve f a n=b := by
  induction h with
  | zero => rfl
  | @succ n a b c hab h ih =>
    rw [Nat.add_comm,evolve_add]
    have he : BoundedSimulation.evolve f a 1=b := by change (f a).getD a=b; rw [hab]; rfl
    rw [he]
    exact ih

def Within {S : Type uVariable14} (f : S → Option S) (a b : S) (N : ℕ) : Prop :=
  ∃ n ≤ N, Steps f n a b

namespace Within
variable {S : Type uVariable15} {f : S → Option S} {a b c : S} {n m : ℕ}
theorem zero (a : S) : Within f a a 0 := ⟨0,le_rfl,Steps.zero a⟩
theorem mono (h : Within f a b n) (hn : n ≤ m) : Within f a b m :=
  let ⟨t,ht,hs⟩ := h; ⟨t,ht.trans hn,hs⟩
theorem trans (h : Within f a b n) (h' : Within f b c m) : Within f a c (n+m) := by
  obtain ⟨i,hi,h⟩ := h
  obtain ⟨j,hj,h'⟩ := h'
  exact ⟨i+j,Nat.add_le_add hi hj,h.trans h'⟩
theorem single (h : f a=some b) : Within f a b 1 := ⟨1,le_rfl,Steps.single h⟩
theorem head (h : f a=some b) (h' : Within f b c n) : Within f a c (n+1) := by
  simpa only [Nat.add_comm 1] using (single h).trans h'
theorem tail (h : Within f a b n) (h' : f b=some c) : Within f a c (n+1) := h.trans (single h')
end Within

end VariableWL.BoundedSimulation

namespace VariableWL.StackSimulation
open Turing TM2to1 TM2to1.Λ' VariableWL.BoundedSimulation
variable {K : Type uVariable16} {Γ : K → Type uVariable19} {Λ : Type uVariable17} {σ : Type uVariable18} [DecidableEq K]

def operations : TM2.Stmt Γ Λ σ → ℕ
  | .push _ _ q => operations q+1
  | .peek _ _ q => operations q+1
  | .pop _ _ q => operations q+1
  | .load _ q => operations q
  | .branch _ q r => max (operations q) (operations r)
  | .goto _ | .halt => 0

omit [DecidableEq K] in
theorem operations_run {k : K} (s : StAct K Γ σ k) (q : TM2.Stmt Γ Λ σ) :
    operations (stRun s q)=operations q+1 := by cases s <;> rfl

omit [DecidableEq K] in
theorem stWrite_length {k : K} (v : σ) (l : List (Γ k)) (s : StAct K Γ σ k) :
    (stWrite v l s).length ≤ l.length+1 := by
  cases s <;> simp only [stWrite,List.length_cons,List.length_tail]
  all_goals omega

theorem stepAux_length (q : TM2.Stmt Γ Λ σ) (v : σ) (S : ∀ k, List (Γ k)) (B : ℕ)
    (hS : ∀ k, (S k).length ≤ B) : ∀ k, ((TM2.stepAux q v S).stk k).length ≤ B+operations q := by
  induction q using stmtStRec generalizing v S B with
  | run k s q ih =>
    rw [step_run,operations_run]
    have hS' : ∀ j, (Function.update S k (stWrite v (S k) s) j).length ≤ B+1 := by
      intro j
      by_cases hj : j=k
      · subst j; rw [Function.update_self]; exact (stWrite_length v (S k) s).trans (Nat.add_le_add_right (hS k) 1)
      · rw [Function.update_of_ne hj]; exact (hS j).trans (by omega)
    intro j
    have h := ih (stVar v (S k) s) _ (B+1) hS' j
    omega
  | load f q ih => exact ih (f v) S B hS
  | branch p q r ihq ihr =>
    cases hp : p v
    · simpa only [TM2.stepAux,hp,Bool.cond_false,operations] using
        (fun k => (ihr v S B hS k).trans (Nat.add_le_add_left (le_max_right _ _) B))
    · simpa only [TM2.stepAux,hp,Bool.cond_true,operations] using
        (fun k => (ihq v S B hS k).trans (Nat.add_le_add_left (le_max_left _ _) B))
  | goto f => exact hS
  | halt => exact hS

variable (M : Λ → TM2.Stmt Γ Λ σ)

theorem go_steps {k : K} (o q v) {S : List (Γ k)} {L : ListBlank (∀ k, Option (Γ k))}
    (hL : L.map (proj k)=ListBlank.mk (S.map some).reverse) (n : ℕ) (H : n ≤ S.length) :
    Steps (TM1.step (tr M)) n ⟨some (go k o q),v,Tape.mk' ∅ (addBottom L)⟩
      ⟨some (go k o q),v,(Tape.move Dir.right)^[n] (Tape.mk' ∅ (addBottom L))⟩ := by
  induction n with
  | zero => exact Steps.zero _
  | succ n ih =>
    apply (ih (by omega)).tail
    rw [Function.iterate_succ_apply']
    simp only [TM1.step,TM1.stepAux,tr,Tape.mk'_nth_nat,Tape.move_right_n_head,addBottom_nth_snd]
    rw [stk_nth_val _ hL,List.getElem?_eq_getElem]
    · rfl
    · rwa [List.length_reverse]

theorem return_steps {q v} {L : ListBlank (∀ k, Option (Γ k))} (n : ℕ) :
    Steps (TM1.step (tr M)) n
      ⟨some (ret q),v,(Tape.move Dir.right)^[n] (Tape.mk' ∅ (addBottom L))⟩
      ⟨some (ret q),v,Tape.mk' ∅ (addBottom L)⟩ := by
  induction n with
  | zero => exact Steps.zero _
  | succ n ih =>
    refine Steps.head ?_ ih
    simp only [TM1.step]
    rw [Option.some_inj,tr,TM1.stepAux,Tape.move_right_n_head,Tape.mk'_nth_nat,
      addBottom_nth_succ_fst,TM1.stepAux,Function.iterate_succ',Function.comp_apply,Tape.move_right_left]
    rfl

theorem normal_bound (q : TM2.Stmt Γ Λ σ) (v : σ) (S : ∀ k, List (Γ k))
    (L : ListBlank (∀ k, Option (Γ k)))
    (hL : ∀ k, L.map (proj k)=ListBlank.mk ((S k).map some).reverse)
    (B : ℕ) (hS : ∀ k, (S k).length ≤ B) :
    ∃ c, TrCfg (TM2.stepAux q v S) c ∧
      Within (TM1.step (tr M)) (TM1.stepAux (trNormal q) v (Tape.mk' ∅ (addBottom L))) c
        (operations q * (2*(B+operations q)+2)) := by
  induction q using stmtStRec generalizing v S L B with
  | run k o q ih =>
    rw [trNormal_run,step_run,operations_run]
    let S' := Function.update S k (stWrite v (S k) o)
    let v' := stVar v (S k) o
    obtain ⟨L',hL',hs⟩ := tr_respects_aux₂ (Λ := Λ) hL o
    have hS' : ∀ j, (S' j).length ≤ B+1 := by
      intro j
      dsimp only [S']
      by_cases hj : j=k
      · subst j
        rw [Function.update_self]
        exact (stWrite_length v (S k) o).trans (Nat.add_le_add_right (hS k) 1)
      · rw [Function.update_of_ne hj]
        exact (hS j).trans (by omega)
    obtain ⟨c,hc,hpath⟩ := ih v' S' L' hL' (B+1) hS'
    refine ⟨c,hc,?_⟩
    have hgo : Within (TM1.step (tr M))
        ⟨some (go k o q),v,Tape.mk' ∅ (addBottom L)⟩
        ⟨some (go k o q),v,(Tape.move Dir.right)^[(S k).length] (Tape.mk' ∅ (addBottom L))⟩
          (S k).length := ⟨_,le_rfl,go_steps M o q v (hL k) _ le_rfl⟩
    have hend : TM1.step (tr M)
        ⟨some (go k o q),v,(Tape.move Dir.right)^[(S k).length] (Tape.mk' ∅ (addBottom L))⟩ =
        some ⟨some (ret q),v',(Tape.move Dir.right)^[(S' k).length] (Tape.mk' ∅ (addBottom L'))⟩ := by
      simp only [TM1.step,tr,TM1.stepAux,Tape.move_right_n_head,Tape.mk'_nth_nat,addBottom_nth_snd,
        stk_nth_val _ (hL k),List.getElem?_eq_none (le_of_eq List.length_reverse),Option.isNone,cond]
      rw [hs]
      rfl
    have hret : Within (TM1.step (tr M))
        ⟨some (ret q),v',(Tape.move Dir.right)^[(S' k).length] (Tape.mk' ∅ (addBottom L'))⟩
        ⟨some (ret q),v',Tape.mk' ∅ (addBottom L')⟩ (S' k).length :=
      ⟨_,le_rfl,return_steps M _⟩
    have hbottom : TM1.step (tr M) ⟨some (ret q),v',Tape.mk' ∅ (addBottom L')⟩ =
        some (TM1.stepAux (trNormal q) v' (Tape.mk' ∅ (addBottom L'))) := by
      simp only [TM1.step,tr,TM1.stepAux,Tape.mk'_head,addBottom_head_fst,Bool.cond_true]
    change Within _ ⟨some (go k o q),v,Tape.mk' ∅ (addBottom L)⟩ c _
    apply (((hgo.tail hend).trans hret).tail hbottom |>.trans hpath).mono
    have hp := hS k
    have hp' := hS' k
    nlinarith
  | load f q ih => exact ih (f v) S L hL B hS
  | branch p q r ihq ihr =>
    cases hp : p v
    · dsimp only [TM2.stepAux,trNormal,TM1.stepAux]
      rw [hp]
      obtain ⟨c,hc,hpath⟩ := ihr v S L hL B hS
      refine ⟨c,hc,hpath.mono ?_⟩
      have hr : operations r ≤ operations (.branch p q r) := le_max_right _ _
      exact Nat.mul_le_mul hr (by omega)
    · dsimp only [TM2.stepAux,trNormal,TM1.stepAux]
      rw [hp]
      obtain ⟨c,hc,hpath⟩ := ihq v S L hL B hS
      refine ⟨c,hc,hpath.mono ?_⟩
      have hq : operations q ≤ operations (.branch p q r) := le_max_left _ _
      exact Nat.mul_le_mul hq (by omega)
  | goto f =>
    refine ⟨_,TrCfg.mk L hL,?_⟩
    simpa only [trNormal,TM1.stepAux,TM2.stepAux,operations,zero_mul,Option.map_some] using
      (Within.zero (f := TM1.step (tr M)) ⟨some (normal (f v)),v,Tape.mk' ∅ (addBottom L)⟩)
  | halt =>
    refine ⟨_,TrCfg.mk L hL,?_⟩
    simpa only [trNormal,TM1.stepAux,TM2.stepAux,operations,zero_mul,Option.map_none] using
      (Within.zero (f := TM1.step (tr M)) ⟨none,v,Tape.mk' ∅ (addBottom L)⟩)

end VariableWL.StackSimulation

end OAI
