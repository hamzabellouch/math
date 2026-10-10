import OAI.Computability.SpaceSimulation.Evaluation.Circuit

namespace OAI

/-!
Verification of the activation flow at a given circuit, using induction
on the meter. The induction contract is from *every* initial pool.
-/
namespace Fifths
namespace Circuit
open Bin Finset Modulus
variable {C : Circuit}

theorem Ylimit (g : C.Good) (x : C.Node) : C.YCount x ≤ 2^C.width :=
  Nat.pow_le_pow_right (by omega) (g.small x)

theorem fee_form (C : Circuit) (x : C.Request) (pc : Pc) (s z y i r j : ℕ)
    (u w : C.F) (h : y ≤ 2^j) :
    C.flow.fee (C.form x pc s z y i r u w) ≤ C.price j := by
  apply C.price_bounds _ j
  change (min _ y).size ≤ j+1
  exact le_trans (Nat.size_le_size (le_trans (min_le_right _ _) h)) (le_of_eq Nat.size_pow)

theorem width_below (C : Circuit) : C.width+1 < C.P.n :=
  lt_of_le_of_lt (by unfold outerDegree; nlinarith) (Modulus.chosen_large C.outerDegree)

def solved (B : C.Node → ℕ) (v : C.Node) : Prop :=
  ∀ (x : C.Request), x.node = v → ∀ R : C.Pool,
    C.flow.Executes (B v) R (C.fEntry x) (x.result R)

structure HasKids (B : C.Node → ℕ) (v : C.Node) : Prop where
  notBase : C.base v = false
  funds : C.Meter B
  h : solved B (C.head v)
  arrays : ∀ i < C.count, solved B (C.child v i)

section
variable {B : C.Node → ℕ} (g : C.Good)
    {x : C.Request} (kids : HasKids B x.node)

def sampleTerm (x : C.Request) (R : C.Pool) (z y i r : ℕ) : C.F :=
  C.P.weight C.width (r:C.F) *
    (C.ET x.node z y i (R (Slot.H x.target))
      (C.P.shift (R (Slot.A x.target)) (C.value (C.child x.node i)) r))

def predVal (x : C.Request) (H : C.Vec) (z y i : ℕ) : C.F :=
  C.ET x.node z y i H (C.value (C.child x.node i))

-- Evaluation of a gate on its distinguished (possibly shifted)
-- register, evaluating each factor already at semantic child vectors.
def summand (x : C.Request) (H : C.Vec) (z y : ℕ) : C.F :=
  C.EG x.node z y H * (∏ i ∈ range C.count, predVal x H z y i)
def formula (x : C.Request) (H : C.Vec) (z : ℕ) : C.F :=
  ∑ y ∈ range (C.YCount x.node), summand x H z y
def cropped (x : C.Request) (H : C.Vec) (s n : ℕ) : C.Vec :=
  fun z => if z<n then C.amount x s (formula x H z) else 0
def advanceR (x : C.Request) (R : C.Pool) (s : ℕ) : C.Vec :=
  cropped x (C.P.shift (R (Slot.H x.target))
    (C.value (C.head x.node)) s) s (C.width+1)

include g kids
/-- Forward and reverse call on an array. Caller labors over arbitrary
pool R; hash coefficient is between those calls. -/
theorem sample_one (R : C.Pool) {s z y i r : ℕ}
    (a : s < C.P.n) (b : z ≤ C.width) (c : y < C.YCount x.node)
    (d : i < C.count) (e : r < C.P.n)
    (u w : C.F) :
    C.flow.Continues (B x.node) R (C.fSample x s z y i r u w) R
      (C.fSample x s z y i (r+1) u (w + sampleTerm x R z y i r)) := by
  have b' : z ≤ C.width+1 := by omega
  have c' := c.le.trans (Ylimit g _)
  let A := x.otherA i r
  let t := C.fCheck x s z y i r u w
  have step : C.flow.act R (C.fSample x s z y i r u w) =
      (R,.call (C.fEntry A) t) := by
    simp only [flow,fSample,form,atPc,clip_ok _ _ a.le,clip_ok _ _ b',
      clip_ok _ _ c',clip_ok _ _ d.le,clip_ok _ _ e.le,ite_eq_left e,A,t]
  have qa (p : C.Frame) (l : C.flow.fee p ≤ C.price (C.guessing x.node)) :
      C.flow.fee p + B (C.child x.node i) ≤ B x.node := by
    have := kids.funds.expensive x.node kids.notBase i d
    omega
  refine Flow.Continues.call step (kids.arrays i d A rfl R)
    (qa _ (fee_form _ _ _ _ _ _ _ _ _ _ _ c.le)) ?_
  let w' := w + sampleTerm x R z y i r
  have ar : (A.result R) (Slot.A x.target) =
      C.P.shift (R (Slot.A x.target)) (C.value (C.child x.node i)) (r:C.F) :=
    C.P.plus_shift R _ _ _
  have hr : (A.result R) (Slot.H x.target) = R (Slot.H x.target) :=
    C.P.plus_other R _ (Slot.sep _)
  have step' : C.flow.act (A.result R) t =
      (A.result R,.call (C.fEntry A.undo) (C.fSample x s z y i (r+1) u w')) := by
    simp only [t,flow,fCheck,form,atPc,clip_ok _ _ a.le,clip_ok _ _ b',
      clip_ok _ _ c',clip_ok _ _ d.le,clip_ok _ _ e.le,hr,ar,A,w',sampleTerm]
  refine Flow.Continues.call step' (kids.arrays i d A.undo rfl (A.result R))
    (qa _ (fee_form _ _ _ _ _ _ _ _ _ _ _ c.le)) ?_
  rw [show A.undo.result (A.result R) = R from C.P.plus_cancel ..]
  exact .stop

/-- The sum of the interpolated two-word test over sample points. -/
theorem sample_seq (R : C.Pool) {s z y i : ℕ} (n : ℕ)
    (a : s < C.P.n) (b : z ≤ C.width) (c : y < C.YCount x.node)
    (d : i < C.count) (e : n ≤ C.P.n)
    (u : C.F) :
    C.flow.Continues (B x.node) R (C.fSample x s z y i 0 u 0) R
      (C.fSample x s z y i n u (∑ r ∈ range n, sampleTerm x R z y i r)) := by
  induction n with
  | zero => rw [sum_range_zero]; exact .stop
  | succ n ih =>
    rw [sum_range_succ]
    exact (ih (by omega)).trans (sample_one g kids R a b c d (by omega) u _)

theorem factor_one (R : C.Pool) {s z y i : ℕ}
    (a : s < C.P.n) (b : z ≤ C.width) (c : y < C.YCount x.node)
    (d : i < C.count) (u : C.F) :
    C.flow.Continues (B x.node) R (C.fFactor x s z y i u) R
      (C.fFactor x s z y (i+1) (u * predVal x (R (Slot.H x.target)) z y i)) := by
  have b' : z ≤ C.width+1 := by omega
  have c' := c.le.trans (Ylimit g _)
  have step : C.flow.act R (C.fFactor x s z y i u) =
      (R,.cont (C.fSample x s z y i 0 u 0)) := by
    simp only [flow,fFactor,form,atPc,clip_ok _ _ a.le,clip_ok _ _ b',
      clip_ok _ _ c',clip_ok _ _ d.le,ite_eq_left d]
  refine Flow.Continues.next step ?_
  have m := sample_seq g kids R C.P.n a b c d le_rfl u
  let H := R (Slot.H x.target)
  let v := predVal x H z y i
  have w : (∑ r ∈ range C.P.n, sampleTerm x R z y i r) = v :=
    ((C.P.extTwo_shiftS C.width (C.test x.node z y i) H
      (R (Slot.A x.target)) (C.value (C.child x.node i))).evaluate (width_below _))
  rw [w] at m
  refine m.trans (Flow.Continues.next ?_ .stop)
  simp only [flow,fSample,form,atPc,clip_ok _ _ a.le,clip_ok _ _ b',
    clip_ok _ _ c',clip_ok _ _ d.le,clip_ok _ _ le_rfl,lt_self_iff_false,ite_false,v,H]

theorem factor_seq (R : C.Pool) {s z y : ℕ}
    (a : s < C.P.n) (b : z ≤ C.width) (c : y < C.YCount x.node)
    (n : ℕ) (d : n ≤ C.count) (u : C.F) :
    C.flow.Continues (B x.node) R (C.fFactor x s z y 0 u) R
      (C.fFactor x s z y n (u * (∏ i ∈ range n, predVal x (R (Slot.H x.target)) z y i))) := by
  induction n with
  | zero =>
    simp only [range_zero,prod_empty,mul_one]
    exact .stop
  | succ n ih =>
    rw [prod_range_succ,← mul_assoc]
    exact (ih (by omega)).trans (factor_one g kids R a b c (by omega) _)


theorem guess_one (R : C.Pool) {s z y : ℕ}
    (a : s < C.P.n) (b : z < C.width+1) (c : y < C.YCount x.node) :
    C.flow.Continues (B x.node) R (C.fGuess x s z y)
      (C.P.plus R x.target (C.P.spike
        (C.amount x s (summand x (R (Slot.H x.target)) z y)) z)) (C.fGuess x s z (y+1)) := by
  have c' := c.le.trans (Ylimit g _)
  let u := C.EG x.node z y (R (Slot.H x.target))
  have step : C.flow.act R (C.fGuess x s z y) =
      (R,.cont (C.fFactor x s z y 0 u)) := by
    simp only [flow,fGuess,form,atPc,clip_ok _ _ a.le,clip_ok _ _ b.le,
      clip_ok _ _ c',ite_eq_left c,u]
  refine Flow.Continues.next step ((factor_seq g kids R a (by omega) c C.count le_rfl u).trans
    (Flow.Continues.next ?_ .stop))
  simp only [flow,fFactor,form,atPc,clip_ok _ _ a.le,clip_ok _ _ b.le,clip_ok _ _ c',
    clip_ok _ _ le_rfl,lt_self_iff_false,ite_false,summand,u]

theorem guess_seq (R : C.Pool) {s z : ℕ} (n : ℕ)
    (a : s < C.P.n) (b : z < C.width+1) (c : n ≤ C.YCount x.node) :
    C.flow.Continues (B x.node) R (C.fGuess x s z 0)
      (C.P.plus R x.target (C.P.spike
        (C.amount x s (∑ y ∈ range n, summand x (R (Slot.H x.target)) z y)) z))
      (C.fGuess x s z n) := by
  induction n with
  | zero =>
    simp only [range_zero,sum_empty,amount,mul_zero]
    have h : C.P.spike 0 z = fun _ => 0 := by ext; simp [spike]
    rw [h,plus_zero]
    exact .stop
  | succ n ih =>
    let E := C.amount x s (∑ y ∈ range n, summand x (R (Slot.H x.target)) z y)
    let R' := C.P.plus R x.target (C.P.spike E z)
    have d : n < C.YCount x.node := by omega
    have f := guess_one g kids R' a b d
    rw [show R' (Slot.H x.target) = R (Slot.H x.target) from
      C.P.plus_other R _ (Slot.h_ne _)] at f
    let j := summand x (R (Slot.H x.target)) z n
    rw [sum_range_succ]
    have t :
        C.P.plus R' x.target (C.P.spike (C.amount x s j) z) =
        C.P.plus R x.target (C.P.spike
          (C.amount x s ((∑ y ∈ range n, summand x (R (Slot.H x.target)) z y)+j)) z) := by
      dsimp only [R']
      rw [plus_twice]
      apply congrArg (C.P.plus R x.target)
      funext i
      by_cases b : i=z <;> simp [b,spike,amount,E,mul_add]
    rw [← t]
    exact (ih d.le).trans f

theorem coord_one (R : C.Pool) {s z : ℕ}
    (a : s < C.P.n) (b : z < C.width+1) :
    C.flow.Continues (B x.node) R (C.fCoord x s z)
      (C.P.plus R x.target (C.P.spike
        (C.amount x s (formula x (R (Slot.H x.target)) z)) z))
      (C.fCoord x s (z+1)) := by
  have c' := Ylimit g x.node
  have step : C.flow.act R (C.fCoord x s z) =
      (R,.cont (C.fGuess x s z 0)) := by
    simp only [flow,fCoord,form,atPc,clip_ok _ _ a.le,clip_ok _ _ b.le,ite_eq_left b]
  refine Flow.Continues.next step ((guess_seq g kids R (C.YCount x.node) a b le_rfl).trans
    (Flow.Continues.next ?_ .stop))
  simp only [flow,fGuess,form,atPc,clip_ok _ _ a.le,clip_ok _ _ b.le,clip_ok _ _ c',
    lt_self_iff_false,ite_false,formula]

theorem coord_seq (R : C.Pool) {s : ℕ} (a : s < C.P.n) (n : ℕ) (b : n ≤ C.width+1) :
    C.flow.Continues (B x.node) R (C.fCoord x s 0)
      (C.P.plus R x.target (cropped x (R (Slot.H x.target)) s n)) (C.fCoord x s n) := by
  induction n with
  | zero =>
    have h : cropped x (R (Slot.H x.target)) s 0 = fun _ => 0 := by ext; simp [cropped]
    rw [h,plus_zero]
    exact .stop
  | succ n ih =>
    let u := cropped x (R (Slot.H x.target)) s n
    let R' := C.P.plus R x.target u
    have e : n < C.width+1 := by omega
    have f := coord_one g kids R' a e
    let H := R (Slot.H x.target)
    have t :
        C.P.plus R' x.target (C.P.spike
          (C.amount x s (formula x (R' (Slot.H x.target)) n)) n) =
        C.P.plus R x.target (cropped x H s (n+1)) := by
      unfold R'; rw [plus_other _ R u (Slot.h_ne _),plus_twice]
      apply congrArg (C.P.plus R x.target)
      ext i
      by_cases y : i=n
      · subst i; simp [spike,u,cropped,H]
      · by_cases v : i<n
        · simp [u,cropped,v,spike,y,H,show i<n+1 by omega]
        · simp [u,cropped,v,spike,y,show ¬ i<n+1 by omega]
    rw [t] at f
    exact (ih e.le).trans f

theorem outer_one (R : C.Pool) {s : ℕ} (a : s < C.P.n) :
    C.flow.Continues (B x.node) R (C.fOuter x s)
      (C.P.plus R x.target (advanceR x R s)) (C.fOuter x (s+1)) := by
  let h := x.otherH s
  have step : C.flow.act R (C.fOuter x s) =
      (R, .call (C.fEntry h) (C.fCoord x s 0)) := by
    simp only [flow,fOuter,form,atPc,clip_ok _ _ a.le,ite_eq_left a,h]
  have q (p : C.Frame) (l : C.flow.fee p ≤ C.price 0) :
      C.flow.fee p + B (C.head x.node) ≤ B x.node := by
    have := kids.funds.cheap x.node kids.notBase
    omega
  refine Flow.Continues.call step (kids.h h rfl R)
    (q _ (fee_form _ _ _ _ _ _ _ _ _ _ _ (show 0 ≤ 2^0 from Nat.zero_le _))) ?_
  let R' := h.result R
  let u := cropped x (R' (Slot.H x.target)) s (C.width+1)
  let R'' := C.P.plus R' x.target u
  have e := coord_seq g kids R' a (C.width+1) le_rfl
  have j : C.flow.act R'' (C.fCoord x s (C.width+1)) =
      (R'', .call (C.fEntry h.undo) (C.fOuter x (s+1))) := by
    simp only [flow,fCoord,form,atPc,clip_ok _ _ a.le,clip_ok _ _ le_rfl,lt_self_iff_false,
      ite_false,h]
  apply e.trans
  refine Flow.Continues.call j (kids.h h.undo rfl R'')
    (q _ (fee_form _ _ _ _ _ _ _ _ _ _ _ (show 0 ≤ 2^0 from Nat.zero_le _))) ?_
  have b : u = advanceR x R s := congrArg
    (fun H => cropped x H s (C.width+1)) (C.P.plus_shift R (Slot.H x.target) _ _)
  rw [show h.undo.result R'' = C.P.plus R x.target (advanceR x R s) from ?_]
  · exact .stop
  show C.P.plus (C.P.plus R' x.target u) _ _ = _
  rw [plus_comm,b]
  exact congrArg (fun t => C.P.plus t x.target _) (show h.undo.result R' = R from C.P.plus_cancel ..)

theorem outer_seq (R : C.Pool) (n : ℕ) (a : n ≤ C.P.n) :
    C.flow.Continues (B x.node) R (C.fOuter x 0)
      (C.P.plus R x.target (fun z => ∑ s ∈ range n, advanceR x R s z))
      (C.fOuter x n) := by
  induction n with
  | zero =>
    simp only [range_zero,sum_empty,plus_zero]
    exact .stop
  | succ n ih =>
    let u := fun z => ∑ s ∈ range n, advanceR x R s z
    let R' := C.P.plus R x.target u
    have b : n < C.P.n := by omega
    have f := outer_one g kids R' b
    rw [show advanceR x R' n = advanceR x R n from ?_] at f
    · refine (ih b.le).trans ?_
      simpa only [sum_range_succ,R',plus_twice,u] using f
    · unfold advanceR R'
      rw [plus_other _ _ u (Slot.h_ne _)]

theorem extracted (R : C.Pool) :
    (fun z => ∑ s ∈ range C.P.n, advanceR x R s z) =
    C.P.multiple x.scale (C.value x.node) := by
  funext z
  by_cases l : z < C.width+1
  · let V := C.value (C.head x.node)
    let H := R (Slot.H x.target)
    have p (y : ℕ) : C.P.Line C.outerDegree
        (fun r => summand x (C.P.shift H V r) z y) (summand x V z y) := by
      have q := C.P.extWord_shift C.width (C.G x.node z y) H V
      have r (i : ℕ) :
          C.P.Line C.width (fun r => predVal x (C.P.shift H V r) z y i)
            (predVal x V z y i) :=
        C.P.extTwo_shiftF C.width (C.test x.node z y i) H V _
      unfold outerDegree
      rw [show (C.count+1)*C.width = C.width + C.count * C.width by ring]
      exact q.mul (Line.prods C.count r)
    have u : C.P.Line C.outerDegree
        (fun s => formula x (C.P.shift H V s) z) (formula x V z) :=
      Line.sums _ p
    have h : formula x V z = C.value x.node z := by
      unfold formula V
      have r := g.identityRule x.node kids.notBase z (by omega)
      simpa [V,summand,predVal,EG,ET,value,extWord_aug,extTwo_aug,g.bounded] using r
    unfold advanceR cropped
    simp only [l,↓reduceIte,amount,multiple,mul_assoc,← mul_sum]
    exact congrArg (fun v => x.scale * v)
      ((u.evaluate (chosen_large _)).trans h)
  · unfold advanceR cropped value
    simp [l,multiple,aug,augBit,show ¬z < C.width by omega,show z ≠ C.width by omega]

theorem recurse_node (R : C.Pool) :
    C.flow.Executes (B x.node) R (C.fEntry x) (x.result R) := by
  refine Flow.Executes.next (m := C.flow) (f := C.fEntry x) (h := R) (j := C.fOuter x 0) ?_ ?_
  · simp only [flow,fEntry,form,atPc,kids.notBase,Bool.false_eq_true,ite_false]
  · have p := outer_seq g kids R C.P.n le_rfl
    rw [extracted g kids R] at p
    refine p.then_exec (.done ?_)
    simp only [flow,fOuter,form,atPc,clip_ok _ _ le_rfl,lt_self_iff_false,
      ite_false, Request.result]

end

theorem answers (C : Circuit) (B : C.Node → ℕ) (g : C.Good) (m : C.Meter B)
    (v : C.Node) : solved B v := by
  suffices h : ∀ n, ∀ y : C.Node, B y < n → solved B y from h (B v+1) v (by omega)
  intro n
  induction n with
  | zero => intros; omega
  | succ n ih =>
    intro v l x e R
    subst v
    cases q : C.base x.node with
    | true =>
      apply Flow.Executes.done
      simp only [flow,fEntry,form,atPc,q,↓reduceIte,value,Request.result,g.leaf _ q]
    | false =>
      refine recurse_node g ⟨q,m,?_,?_⟩ R
      · apply ih
        have := m.cheap x.node q
        unfold price at this
        omega
      · intro i e
        apply ih
        have := m.expensive _ q _ e
        unfold price at this
        omega

end Circuit
end Fifths

end OAI
