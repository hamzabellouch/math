import Mathlib
import OAI.Analysis.MatrixSigning.Arithmetic.RationalExpressionHeight
import OAI.Analysis.MatrixSigning.Arithmetic.ArithmeticEncodingSize

namespace OAI

section

namespace KS.W13.ExpressionMachine
open KS.W17

inductive Op where
  | value : ℚ → Op
  | add | sub | mul | div | neg
  deriving DecidableEq

def Op.encode : Op → List Bool
  | .value q => false :: KS.W01.frame (KS.W01.encodeRat q)
  | .add => [true,false]
  | .sub => [true,true,false]
  | .mul => [true,true,true,false]
  | .div => [true,true,true,true,false]
  | .neg => [true,true,true,true,true]

def encodeOps (ops : List Op) : List Bool := ops.flatMap Op.encode

def postorder : RationalExpr → List Op
  | .value q => [.value q]
  | .add x y => postorder x ++ postorder y ++ [.add]
  | .sub x y => postorder x ++ postorder y ++ [.sub]
  | .mul x y => postorder x ++ postorder y ++ [.mul]
  | .div x y => postorder x ++ postorder y ++ [.div]
  | .neg x => postorder x ++ [.neg]

def encodeExpr (e : RationalExpr) : List Bool := encodeOps (postorder e)

def encodeStack (s : List ℚ) : List Bool := s.flatMap (fun q => KS.W01.frame (KS.W01.encodeRat q))

@[simp] theorem encodeOps_nil : encodeOps [] = [] := rfl
@[simp] theorem encodeOps_cons (op : Op) (ops : List Op) :
    encodeOps (op::ops) = op.encode ++ encodeOps ops := rfl
@[simp] theorem encodeOps_append (ops rest : List Op) :
    encodeOps (ops++rest) = encodeOps ops ++ encodeOps rest := by simp [encodeOps]
@[simp] theorem encodeStack_nil : encodeStack [] = [] := rfl
@[simp] theorem encodeStack_cons (q : ℚ) (qs : List ℚ) :
    encodeStack (q::qs) = KS.W01.frame (KS.W01.encodeRat q) ++ encodeStack qs := rfl

theorem encodeOp_nonempty (op : Op) : op.encode ≠ [] := by cases op <;> simp [Op.encode]
theorem encodeOps_cons_nonempty (op : Op) (ops : List Op) : encodeOps (op::ops) ≠ [] := by
  cases op <;> simp [encodeOps,Op.encode]

theorem postorder_length (e : RationalExpr) : (postorder e).length = e.leaves + e.operations := by
  induction e <;> simp_all [postorder,RationalExpr.leaves,RationalExpr.operations] <;> omega

theorem encodeOps_length_ge (ops : List Op) : ops.length ≤ (encodeOps ops).length := by
  induction ops with
  | nil => simp
  | cons op ops ih =>
    have hp : 0 < op.encode.length := by cases op <;> simp [Op.encode]
    simp only [encodeOps_cons,List.length_append,List.length_cons]
    omega

theorem nodes_le_syntax_length (e : RationalExpr) : e.leaves + e.operations ≤ (encodeExpr e).length := by
  rw [← postorder_length]
  exact encodeOps_length_ge _

def Op.step : Op → List ℚ → Option (List ℚ)
  | .value q,s => some (q::s)
  | .add,r::q::s => some ((q+r)::s)
  | .sub,r::q::s => some ((q-r)::s)
  | .mul,r::q::s => some ((q*r)::s)
  | .div,r::q::s => some ((q/r)::s)
  | .neg,q::s => some ((-q)::s)
  | _,_ => none

def exec : List Op → List ℚ → Option (List ℚ)
  | [],s => some s
  | op::ops,s => (op.step s).bind (exec ops)

theorem exec_append (ops rest : List Op) (s : List ℚ) :
    exec (ops++rest) s = (exec ops s).bind (exec rest) := by
  induction ops generalizing s with
  | nil => rfl
  | cons op ops ih =>
    simp only [List.cons_append,exec]
    cases op.step s <;> simp [ih]

theorem exec_postorder (e : RationalExpr) (s : List ℚ) :
    exec (postorder e) s = some (e.eval::s) := by
  induction e generalizing s <;>
    simp_all [postorder,exec_append,exec,Op.step,RationalExpr.eval]

inductive Trace : List Op → List ℚ → List ℚ → Prop where
  | nil (s) : Trace [] s s
  | cons {op ops s t out} : op.step s = some t → Trace ops t out → Trace (op::ops) s out

theorem trace_iff_exec (ops : List Op) (s out : List ℚ) : Trace ops s out ↔ exec ops s = some out := by
  induction ops generalizing s out with
  | nil =>
    constructor
    · intro h;cases h;rfl
    · intro h
      have he : s=out := Option.some.inj h
      subst out
      exact .nil _
  | cons op ops ih =>
    constructor
    · intro h; cases h with
      | cons hs ht => simp [exec,hs,(ih _ _).mp ht]
    · intro h
      cases hs : op.step s with
      | none => simp [exec,hs] at h
      | some t => exact .cons hs ((ih t out).mpr (by simpa [exec,hs] using h))

theorem trace_postorder (e : RationalExpr) (s : List ℚ) : Trace (postorder e) s (e.eval::s) :=
  (trace_iff_exec _ _ _).mpr (exec_postorder e s)

def ValueBound (B : ℕ) (s : List ℚ) : Prop := ∀ q∈s, KS.W01.ratLength q ≤ B

def SubtreeBound (B : ℕ) (e : RationalExpr) : Prop :=
  ∀ s : RationalExpr, s.IsSubexpression e → KS.W01.ratLength s.eval ≤ B

inductive BoundedTrace (B : ℕ) : List Op → List ℚ → List ℚ → Prop where
  | nil {s} : ValueBound B s → BoundedTrace B [] s s
  | cons {op ops s t out} : ValueBound B s → op.step s = some t →
      BoundedTrace B ops t out → BoundedTrace B (op::ops) s out

theorem BoundedTrace.toTrace {B ops s out} (h : BoundedTrace B ops s out) : Trace ops s out := by
  induction h with
  | nil => exact .nil _
  | cons hs hstep ht ih => exact .cons hstep ih

theorem BoundedTrace.start_bound {B ops s out} (h : BoundedTrace B ops s out) : ValueBound B s := by
  cases h <;> assumption

theorem BoundedTrace.end_bound {B ops s out} (h : BoundedTrace B ops s out) : ValueBound B out := by
  induction h <;> assumption

theorem BoundedTrace.append {B ops rest s t out} (h : BoundedTrace B ops s t)
    (hr : BoundedTrace B rest t out) : BoundedTrace B (ops++rest) s out := by
  induction h generalizing rest out with
  | nil => exact hr
  | cons hs hstep ht ih => exact .cons hs hstep (ih hr)

theorem bounded_trace_postorder (e : RationalExpr) (B : ℕ) (hb : SubtreeBound B e)
    (s : List ℚ) (hs : ValueBound B s) : BoundedTrace B (postorder e) s (e.eval::s) := by
  induction e generalizing s with
  | value q =>
    have hq : KS.W01.ratLength q ≤ B := hb (.value q) (.refl _)
    apply BoundedTrace.cons hs rfl
    apply BoundedTrace.nil
    intro r hr
    rcases List.mem_cons.mp hr with rfl | hr
    · exact hq
    · exact hs r hr
  | neg x ih =>
    have hx := ih (fun t ht => hb t (.neg ht)) s hs
    have hv : ValueBound B ((-x.eval)::s) := by
      intro q hq
      rcases List.mem_cons.mp hq with rfl | hq
      · exact hb (.neg x) (.refl _)
      · exact hs q hq
    exact hx.append (.cons hx.end_bound rfl (.nil hv))
  | add x y ihx ihy =>
    have hx := ihx (fun t ht => hb t (.add_left ht)) s hs
    have hy := ihy (fun t ht => hb t (.add_right ht)) (x.eval::s) hx.end_bound
    have hv : ValueBound B ((x.eval+y.eval)::s) := by
      intro q hq
      rcases List.mem_cons.mp hq with rfl | hq
      · exact hb (.add x y) (.refl _)
      · exact hs q hq
    simpa only [postorder,List.append_assoc,RationalExpr.eval] using
      (hx.append hy).append (.cons hy.end_bound rfl (.nil hv))
  | sub x y ihx ihy =>
    have hx := ihx (fun t ht => hb t (.sub_left ht)) s hs
    have hy := ihy (fun t ht => hb t (.sub_right ht)) (x.eval::s) hx.end_bound
    have hv : ValueBound B ((x.eval-y.eval)::s) := by
      intro q hq
      rcases List.mem_cons.mp hq with rfl | hq
      · exact hb (.sub x y) (.refl _)
      · exact hs q hq
    simpa only [postorder,List.append_assoc,RationalExpr.eval] using
      (hx.append hy).append (.cons hy.end_bound rfl (.nil hv))
  | mul x y ihx ihy =>
    have hx := ihx (fun t ht => hb t (.mul_left ht)) s hs
    have hy := ihy (fun t ht => hb t (.mul_right ht)) (x.eval::s) hx.end_bound
    have hv : ValueBound B ((x.eval*y.eval)::s) := by
      intro q hq
      rcases List.mem_cons.mp hq with rfl | hq
      · exact hb (.mul x y) (.refl _)
      · exact hs q hq
    simpa only [postorder,List.append_assoc,RationalExpr.eval] using
      (hx.append hy).append (.cons hy.end_bound rfl (.nil hv))
  | div x y ihx ihy =>
    have hx := ihx (fun t ht => hb t (.div_left ht)) s hs
    have hy := ihy (fun t ht => hb t (.div_right ht)) (x.eval::s) hx.end_bound
    have hv : ValueBound B ((x.eval/y.eval)::s) := by
      intro q hq
      rcases List.mem_cons.mp hq with rfl | hq
      · exact hb (.div x y) (.refl _)
      · exact hs q hq
    simpa only [postorder,List.append_assoc,RationalExpr.eval] using
      (hx.append hy).append (.cons hy.end_bound rfl (.nil hv))

end KS.W13.ExpressionMachine

end

end OAI
