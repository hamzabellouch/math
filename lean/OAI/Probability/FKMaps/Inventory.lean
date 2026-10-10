import Mathlib

namespace OAI

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.Inventory

/-- `none` is the flexible order; a typed order is `some type`. -/
abbrev Order := Option Bool
inductive Letter where
  | burger : Bool → Letter
  | order : Order → Letter
  deriving DecidableEq, Fintype

/-- Internal stacks are freshest-first. The source's surviving-burger list
is `Evaluation.burgers.reverse`, so source chronology is unchanged. -/
def eligible (a : Order) (b : Bool) : Prop := a=none ∨ a=some b

instance (a : Order) (b : Bool) : Decidable (eligible a b) :=
  inferInstanceAs (Decidable (a=none ∨ a=some b))

def pop (a : Order) : List Bool → Option (List Bool)
  | [] => none
  | b::bs => if eligible a b then some bs else (pop a bs).map (b::·)

lemma pop_append (a : Order) (s t : List Bool) :
    pop a (s++t) = match pop a s with
      | some s' => some (s'++t)
      | none => (pop a t).map (s++·) := by
  induction s with
  | nil => simp [pop]
  | cons b bs ih =>
    simp only [List.cons_append,pop]
    split_ifs with h
    · rfl
    · rw [ih]
      cases pop a bs <;> cases pop a t <;> rfl

lemma pop_eq_none_iff (a : Order) (s : List Bool) :
    pop a s=none ↔ ∀ b∈s,¬eligible a b := by
  induction s with
  | nil => simp [pop]
  | cons b bs ih =>
    by_cases h : eligible a b <;> simp [pop,h,ih]

lemma pop_length {a : Order} {s t : List Bool} (h : pop a s=some t) :
    t.length+1=s.length := by
  induction s generalizing t with
  | nil => simp [pop] at h
  | cons b bs ih =>
    simp only [pop] at h
    split_ifs at h with he
    · cases h; rfl
    · cases hp : pop a bs with
      | none => simp [hp] at h
      | some s' =>
        simp only [hp,Option.map_some,Option.some.injEq] at h
        subst t
        simp only [List.length_cons]
        have := ih hp
        omega

structure Evaluation where
  orders : List Order
  burgers : List Bool
  deriving DecidableEq

def step (e : Evaluation) : Letter → Evaluation
  | .burger b => ⟨e.orders,b::e.burgers⟩
  | .order a => match pop a e.burgers with
    | some bs => ⟨e.orders,bs⟩
    | none => ⟨e.orders++[a],e.burgers⟩

def run : List Letter → Evaluation → Evaluation
  | [],e => e
  | a::w,e => run w (step e a)

def reduce (w : List Letter) : Evaluation := run w ⟨[],[]⟩

def evalOrders (as : List Order) (s : List Bool) : Evaluation :=
  run (as.map Letter.order) ⟨[],s⟩

lemma run_append (w w' : List Letter) (e : Evaluation) :
    run (w++w') e=run w' (run w e) := by
  induction w generalizing e with
  | nil => rfl
  | cons a w ih => exact ih _

lemma run_orders_prefix (w : List Letter) (os : List Order) (e : Evaluation) :
    run w ⟨os++e.orders,e.burgers⟩ =
      ⟨os++(run w e).orders,(run w e).burgers⟩ := by
  induction w generalizing e with
  | nil => rfl
  | cons a w ih =>
    cases a with
    | burger b => simpa only [run,step] using ih ⟨e.orders,b::e.burgers⟩
    | order a =>
      simp only [run,step]
      cases pop a e.burgers with
      | none => simpa only [List.append_assoc] using ih ⟨e.orders++[a],e.burgers⟩
      | some bs => exact ih ⟨e.orders,bs⟩

lemma evalOrders_nil (s : List Bool) : evalOrders [] s=⟨[],s⟩ := rfl

lemma evalOrders_append (as as' : List Order) (s : List Bool) :
    evalOrders (as++as') s =
      ⟨(evalOrders as s).orders++(evalOrders as' (evalOrders as s).burgers).orders,
       (evalOrders as' (evalOrders as s).burgers).burgers⟩ := by
  unfold evalOrders
  rw [List.map_append,run_append]
  simpa only [List.append_nil] using
    run_orders_prefix (as'.map Letter.order) (run (as.map Letter.order) ⟨[],s⟩).orders
      (⟨[],(run (as.map Letter.order) ⟨[],s⟩).burgers⟩ : Evaluation)

/-- Exact older-supply reduction. Unfilled orders retain chronological order;
all surviving new burgers are fresher than all surviving old burgers. -/
theorem run_older_supply (w : List Letter) (s : List Bool) :
    run w ⟨[],s⟩ =
      ⟨(evalOrders (reduce w).orders s).orders,
        (reduce w).burgers++(evalOrders (reduce w).orders s).burgers⟩ := by
  induction w using List.reverseRecOn with
  | nil => simp [run,reduce,evalOrders]
  | append_singleton w a ih =>
    rw [run_append,ih]
    have hr : reduce (w++[a])=step (reduce w) a := by
      simp [reduce,run_append,run]
    rw [hr]
    cases a with
    | burger b => simp only [run,step,List.cons_append]
    | order a =>
      simp only [run,step]
      rw [pop_append]
      cases hp : pop a (reduce w).burgers with
      | some bs => rfl
      | none =>
        dsimp only
        rw [evalOrders_append]
        simp only [evalOrders,List.map_singleton,run,step]
        cases pop a (run (List.map Letter.order (reduce w).orders) ⟨[],s⟩).burgers <;>
          simp only [Option.map_none,Option.map_some,List.append_nil,List.nil_append]

lemma run_burgers (s : List Bool) (e : Evaluation) :
    run (s.map Letter.burger) e=⟨e.orders,s.reverse++e.burgers⟩ := by
  induction s generalizing e with
  | nil => simp [run]
  | cons b bs ih => simp [run,step,ih,List.reverse_cons,List.append_assoc]

def normalWord (e : Evaluation) : List Letter :=
  e.orders.map Letter.order++e.burgers.reverse.map Letter.burger

/-- A finite word may be replaced by its source reduction in any supply. -/
theorem run_normalWord (w : List Letter) (e : Evaluation) :
    run (normalWord (reduce w)) e=run w e := by
  obtain ⟨os,s⟩ := e
  have hz : run (normalWord (reduce w)) ⟨[],s⟩=run w ⟨[],s⟩ := by
    rw [run_older_supply w s]
    simp only [normalWord,run_append,run_burgers,List.reverse_reverse,evalOrders]
  have h₁ := run_orders_prefix (normalWord (reduce w)) os (⟨[],s⟩ : Evaluation)
  have h₂ := run_orders_prefix w os (⟨[],s⟩ : Evaluation)
  simp only [List.append_nil] at h₁ h₂
  rw [h₁,h₂,hz]

/-- Once a suffix has a surviving burger, its freshest survivor is unchanged
by prepending arbitrary further letters. -/
theorem freshest_survivor_prepend (w w' : List Letter) {b : Bool} {bs : List Bool}
    (h : (reduce w).burgers=b::bs) : (reduce (w'++w)).burgers.head?=some b := by
  unfold reduce
  rw [run_append]
  have hh := run_orders_prefix w (reduce w').orders (⟨[],(reduce w').burgers⟩ : Evaluation)
  simp only [List.append_nil] at hh
  rw [show run w' ⟨[],[]⟩=⟨(reduce w').orders,(reduce w').burgers⟩ from rfl,hh,run_older_supply,h]
  rfl

def Letter.increment : Letter → ℤ
  | .burger _ => 1
  | .order _ => -1

def imbalance (e : Evaluation) : ℤ := (e.burgers.length:ℤ)-e.orders.length

lemma step_imbalance (e : Evaluation) (a : Letter) :
    imbalance (step e a)=imbalance e+a.increment := by
  cases a with
  | burger b => simp [imbalance,step,Letter.increment]; ring
  | order a =>
    simp only [step,Letter.increment]
    cases hp : pop a e.burgers with
    | none => simp [imbalance]; ring
    | some bs =>
      have hlen := pop_length hp
      simp only [imbalance]
      omega

lemma run_imbalance (w : List Letter) (e : Evaluation) :
    imbalance (run w e)=(w.map Letter.increment).sum+imbalance e := by
  induction w generalizing e with
  | nil => simp [run]
  | cons a w ih =>
    simp only [run,ih,step_imbalance,List.map_cons,List.sum_cons]
    ring

lemma reduce_imbalance (w : List Letter) :
    imbalance (reduce w)=(w.map Letter.increment).sum := by
  rw [reduce,run_imbalance]
  simp [imbalance]

lemma survivor_of_sum_pos (w : List Letter) (h : 0<(w.map Letter.increment).sum) :
    (reduce w).burgers≠[] := by
  intro hn
  rw [← reduce_imbalance,imbalance,hn] at h
  simp only [List.length_nil,Nat.cast_zero,zero_sub] at h
  omega

lemma orders_length_le_step (e : Evaluation) (a : Letter) :
    e.orders.length≤(step e a).orders.length := by
  cases a with
  | burger b => rfl
  | order a => simp only [step]; split <;> simp

lemma orders_length_le_run (w : List Letter) (e : Evaluation) :
    e.orders.length≤(run w e).orders.length := by
  induction w generalizing e with
  | nil => rfl
  | cons a w ih => exact (orders_length_le_step e a).trans (ih (step e a))

def EmptyReducing (w : List Letter) : Prop := reduce w=⟨[],[]⟩

/-- Exact necessary Dyck-path event, without invoking a map encoding. -/
theorem emptyReducing_dyck (w : List Letter) (h : EmptyReducing w) :
    (w.map Letter.increment).sum=0 ∧
      ∀ j,0≤((w.take j).map Letter.increment).sum := by
  have he : reduce w=⟨[],[]⟩ := h
  constructor
  · rw [← reduce_imbalance,he,imbalance]; simp
  · intro j
    have hle := orders_length_le_run (w.drop j) (reduce (w.take j))
    have hr : run (w.drop j) (reduce (w.take j))=reduce w := by
      rw [reduce,← run_append,List.take_append_drop]
      rfl
    rw [hr,he] at hle
    have ho : (reduce (w.take j)).orders=[] := List.length_eq_zero_iff.mp (by simpa using hle)
    rw [← reduce_imbalance,imbalance,ho]
    simp

lemma evalOrders_cons (a : Order) (as : List Order) (s : List Bool) :
    evalOrders (a::as) s = match pop a s with
      | some s' => evalOrders as s'
      | none => ⟨a::(evalOrders as s).orders,(evalOrders as s).burgers⟩ := by
  unfold evalOrders
  simp only [List.map_cons,run,step]
  cases pop a s with
  | some s' => rfl
  | none =>
    simpa only [List.nil_append,List.append_nil,List.singleton_append] using
      run_orders_prefix (as.map Letter.order) [a] (⟨[],s⟩ : Evaluation)

lemma evalOrders_empty (as : List Order) : evalOrders as []=⟨as,[]⟩ := by
  induction as with
  | nil => rfl
  | cons a as ih => simp [evalOrders_cons,pop,ih]

lemma evalOrders_singleton (as : List Order) (b : Bool) :
    (evalOrders as [b]).burgers= if ∀ a∈as,¬eligible a b then [b] else [] := by
  induction as with
  | nil => simp [evalOrders,run]
  | cons a as ih =>
    rw [evalOrders_cons]
    by_cases h : eligible a b
    · simp [pop,h,evalOrders_empty]
    · simp [pop,h,ih]

lemma evalOrders_no_match (as : List Order) (s : List Bool)
    (h : ∀ a∈as,pop a s=none) : evalOrders as s=⟨as,s⟩ := by
  induction as with
  | nil => rfl
  | cons a as ih =>
    rw [evalOrders_cons,h a (by simp),ih (by intro a ha; exact h a (by simp [ha]))]

lemma prepend_order_burgers (a : Order) (w : List Letter) :
    (reduce (.order a::w)).burgers=(reduce w).burgers := by
  change (run w (step ⟨[],[]⟩ (.order a))).burgers=_
  simp only [step,pop,List.nil_append]
  have h := run_orders_prefix w [a] (⟨[],[]⟩ : Evaluation)
  simpa only [List.append_nil,reduce] using congrArg Evaluation.burgers h

/-- The first backwards survivor has exactly one burger and only fixed
orders of the opposite type, precisely as in source word:stopped-sum. -/
theorem first_survivor_shape (a : Letter) (w : List Letter)
    (h₀ : (reduce w).burgers=[]) (h₁ : (reduce (a::w)).burgers≠[]) :
    ∃ b, a=.burger b ∧ reduce (a::w)=⟨(reduce w).orders,[b]⟩ ∧
      ∀ o∈(reduce w).orders,o=some (!b) := by
  cases a with
  | order a => exact (h₁ (by rw [prepend_order_burgers,h₀])).elim
  | burger b =>
    have he : reduce (.burger b::w)=evalOrders (reduce w).orders [b] := by
      change run w ⟨[],[b]⟩=_
      rw [run_older_supply,h₀,List.nil_append]
    rw [he,evalOrders_singleton] at h₁
    have hn : ∀ o∈(reduce w).orders,¬eligible o b := by
      by_contra hn
      exact h₁ (ite_eq_right hn)
    refine ⟨b,rfl,?_,?_⟩
    · rw [he,evalOrders_no_match]
      intro o ho
      exact (pop_eq_none_iff o [b]).2 (by simpa using hn o ho)
    · intro o ho
      have hh := hn o ho
      cases o with
      | none => exact (hh (Or.inl rfl)).elim
      | some c => cases b <;> cases c <;> simp_all [eligible]

end FKCRT.Inventory
end

end OAI
