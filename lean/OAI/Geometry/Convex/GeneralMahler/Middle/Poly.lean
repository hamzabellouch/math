import OAI.Geometry.Convex.GeneralMahler.Middle.Features
import OAI.Geometry.Convex.GeneralMahler.Middle.Ratio

namespace OAI
/-! Middle-width certificate uses second derivative envelope on the
actual endpoint functional. Syntax shares proof of interval and profile estimates. -/
open Set Filter MeasureTheory MeasureTheory.Measure Real
namespace GeneralMahler.SCal.Mid
open Grid Jet Profile Segment SE Cert Cert.IV Ft
inductive Op
  | src (k:Fin 3) (f:Ft)
  -- rational constant q/r
  | num (q r:Int)
  | add (u v:Op)
  | sub (u v:Op)
  | mul (u v:Op)
deriving Inhabited
namespace Op
local notation x " +| " y => Op.add x y
noncomputable def eval (k:Fin 3→Ft→ℝ):Op→ℝ
  | src n feat=> k n feat
  | num a b=> (a:ℝ)/b
  | add a b=>eval k a+eval k b
  | sub a b=>eval k a-eval k b
  | mul a b=>eval k a*eval k b
def boxE (k:Fin 3→Ft→IV):Op→IV
  | src n feat=> k n feat
  | num a b=> c a/c b
  | add a b=>boxE k a+boxE k b
  | sub a b=>boxE k a-boxE k b
  | mul a b=>boxE k a*boxE k b

noncomputable def capE (k:Fin 3→Ft→Cap):Op→Cap
  | src n feat=> k n feat
  | num a b=> Cap.fl |(a:ℝ)/(b:ℝ)|
  | add a b=>Cap.plus (capE k a) (capE k b)
  | sub a b=>Cap.plus (capE k a) (capE k b)
  | mul a b=>Cap.times (capE k a) (capE k b)

lemma bval {k:Fin 3→Ft→ℝ}{v:Fin 3→Ft→IV}(h:∀ i n,k i n∈ v i n) (x:Op):
    eval k x∈boxE v x := by
  induction x with
  | src=> apply h
  | num a b=>exact mdiv (mc a) (mc b)
  | add a b ih hg=>exact madd ih hg
  | sub a b ih hg=>exact msub ih hg
  | mul a b ih hg=>exact mmul ih hg
lemma valGuard {k:Fin 3→Ft→ℝ→ℝ}{v:Fin 3→Ft→ Cap}(h:∀ i n,Guard (k i n) (v i n))(u:Op):
    Guard (fun x=> eval (fun i n=> k i n x) u) (capE v u):=by
  induction u with
  | src=> apply h
  | num a b=>exact Guard.const _ _ le_rfl
  | add a b ih hg=>exact ih.plus hg
  | sub a b ih hg=>exact ih.minus hg
  | mul a b ih hg=>exact ih.prod hg

-- endpoints stored 0,1; averages 2
def q (v:Op):Op:=mul v v
def ekp:=sub (src 2 Ft.K) (mul (num 1 2) (add (src 0 Ft.K) (src 1 Ft.K)))
def gammaOp:Op:=
  let c:=sub (src 1 Ft.C) (src 0 Ft.C)
  let k:=sub (src 1 Ft.K) (src 0 Ft.K)
  mul (mul (num 8 10) (q (num 1000 352))) (add
    (mul (num 125 100) (q (add k (mul (num 21 1000) c))))
    (mul (mul (num 5 1) (q (num 43 1000))) (q c)))
def ru2 := q (num 22 100)
def sm (p:Fin 3) := add ru2 (src p Ft.M)
def dotOp (p:Fin 3) := add (add (mul (src 2 Ft.Q) (src p Ft.Q)) (mul (src 2 Ft.J) (src p Ft.J)))
  (mul (src 2 Ft.V) (src p Ft.V))
def mb (p:Fin 3) := sub (add (sm 2) (sm p)) (mul (num 2 1) (dotOp p))
def bolt (p q:Fin 3):= sub (sub (src 2 Ft.C) (src q Ft.C)) (mb p)
def E:Op := sub (add (add (add ekp gammaOp)
  (mul (num 10 52) (add (q (bolt 0 1)) (q (bolt 1 0)))))
  (mul (num 32 1000) (add (mb 0) (mb 1))))
  (mul (num 1064 1000) (sub (sm 2) (dotOp 2)))
end Op
noncomputable section
-- choose s=g t profiles
def inp (x y:ℝ):Fin 3→Ft→ℝ:=
  fun n f=> if n=0 then f.g x else if n=1 then f.g y else trav x f.g y
def Fval (x y:ℝ):= Op.eval (inp x y) Op.E
def caps (i:Fin 3) (f:Ft) := if i=0 then Cap.fl f.cap.a else if i=1 then f.cap else Cap.av f.cap
def budgetCap:= Op.capE caps Op.E
lemma gv2 (h:NG)(x:ℝ):Guard (Fval x) budgetCap:= by
  apply Op.valGuard (k:=fun i f y=>inp x y i f) _ _
  intro i v
  have hh:=guarded h v
  unfold inp caps;split_ifs with hf hg
  · exact Guard.const _ _ (hh.fa _)
  · exact hh
  exact trav_guard hh x
lemma Bcost : budgetCap.c ≤ 37:=by
  have he : (2:Fin 3)≠0:=by decide
  have hv : (2:Fin 3)≠1:=by decide
  have ha : (1:Fin 3)≠0:=by decide
  norm_num [he,hv,ha,budgetCap,Op.E,Op.capE,caps,Cap.plus,Cap.times,Cap.fl,Cap.av, Ft.cap,Ft.cP,Ft.cC,
    Ft.cJ,Ft.cK,Op.dotOp,Op.sm,Op.ru2,Op.q,Op.mb,Op.bolt,Op.gammaOp,Op.ekp]
end
end GeneralMahler.SCal.Mid

end OAI
