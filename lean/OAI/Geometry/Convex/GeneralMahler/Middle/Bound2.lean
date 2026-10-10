import OAI.Geometry.Convex.GeneralMahler.Segment.Mean
import OAI.Geometry.Convex.GeneralMahler.Segment.Stats

namespace OAI
/-! Interval on t; second derivative majorants. -/
noncomputable section
open Set Filter Real MeasureTheory
open scoped Topology Interval
namespace GeneralMahler.SCal.Mid
open Tag Grid Jet Profile Segment SE

structure Cap where
  a:ℝ
  b:ℝ
  c:ℝ
namespace Cap
def plus (X Y:Cap):Cap:=⟨X.a+Y.a,X.b+Y.b,X.c+Y.c⟩
def times (X Y:Cap):Cap:=⟨X.a*Y.a,X.b*Y.a+X.a*Y.b,X.c*Y.a+X.a*Y.c+2*X.b*Y.b⟩
def av (X:Cap):Cap:=⟨X.a,X.b+2*X.a,X.c+4*X.b+6*X.a⟩
def fl (a:ℝ):Cap:=⟨a,0,0⟩
end Cap
def ddf (f:ℝ→ℝ):=deriv (deriv f)
structure Guard (f:ℝ→ℝ)(A:Cap):Prop where
  h: Differentiable ℝ f
  g: Differentiable ℝ (deriv f)
  c: Continuous (ddf f)
  fa: ∀ x,|f x|≤A.a
  fb: ∀ x,|deriv f x|≤A.b
  fc: ∀ x,|ddf f x|≤A.c

lemma mkGuard {f g h:ℝ→ℝ} (hf:∀ x,HasDerivAt f (g x) x)
    (hg:∀ x,HasDerivAt g (h x) x) (hh:Continuous h)
    {A:Cap} (ha:∀ x,|f x|≤ A.a)(hb:∀ x,|g x|≤A.b)(hc:∀ x,|h x|≤A.c):Guard f A := by
  have hi:deriv f=g:=funext fun x=>(hf x).deriv
  have he:ddf f=h:=by unfold ddf; rw [hi]; exact funext fun x=>(hg x).deriv
  refine ⟨fun x=>(hf x).differentiableAt,?_,he.symm ▸ hh,ha,hi.symm ▸ hb,he.symm ▸ hc⟩
  rw [hi]; exact fun x=>(hg x).differentiableAt
variable {f g:ℝ→ℝ}{A B:Cap}

namespace Guard
lemma Df(h:Guard f A)(x):HasDerivAt f (deriv f x) x:=(h.h x).hasDerivAt
lemma Db(h:Guard f A)(x):HasDerivAt (deriv f) (ddf f x) x:=(h.g x).hasDerivAt
lemma nn(h:Guard f A):0≤A.a∧0≤A.b∧0≤A.c:=
  ⟨le_trans (_root_.abs_nonneg _) (h.fa 0),le_trans (_root_.abs_nonneg _) (h.fb 0),
    le_trans (_root_.abs_nonneg _) (h.fc 0)⟩
lemma const (a c:ℝ)(h:|a|≤c):Guard (fun _=>a) (Cap.fl c):=
  mkGuard (fun x=>hasDerivAt_const x a) (fun x=>hasDerivAt_const x 0)
    continuous_const (fun _=> h) (fun _=>by simp [Cap.fl]) (fun _=>by simp [Cap.fl])
lemma absAdd {x y a b:ℝ}(h:|x|≤a)(hh:|y|≤b):|x+y|≤a+b:=le_trans (abs_add_le ..) (add_le_add h hh)
lemma absMul {x y a b:ℝ}(h:|x|≤a)(hh:|y|≤b):|x*y|≤a*b:=by
  rw [abs_mul];exact mul_le_mul h hh (_root_.abs_nonneg _) (le_trans (_root_.abs_nonneg _) h)
lemma plus (h:Guard f A)(he:Guard g B):Guard (fun x=>f x+g x) (Cap.plus A B) :=
  mkGuard (fun x=>(h.Df x).fun_add (he.Df x)) (fun x=>(h.Db x).fun_add (he.Db x))
    (h.c.add he.c) (fun x=>absAdd (h.fa x) (he.fa x))
    (fun x=>absAdd (h.fb x) (he.fb x)) (fun x=>absAdd (h.fc x) (he.fc x))
lemma opp (h:Guard f A):Guard (fun x=> -f x) A:=
  mkGuard (g:=fun x=> -deriv f x) (h:=fun x=> -ddf f x) (fun x=>(h.Df x).neg)
    (fun x=>(h.Db x).neg) h.c.neg (fun x=>by simpa using h.fa x) (fun x=>by simpa using h.fb x)
    (fun x=>by simpa using h.fc x)
lemma minus (h:Guard f A)(he:Guard g B): Guard (fun x=>f x-g x) (Cap.plus A B):=
  by simpa only [sub_eq_add_neg] using h.plus he.opp
lemma prod (h:Guard f A)(he:Guard g B):Guard (fun x=>f x*g x) (Cap.times A B):= by
  let k:=fun x=> deriv f x*g x+f x*deriv g x
  have hd (x): HasDerivAt (fun x=>f x*g x) (k x) x:=
    (h.Df x).fun_mul (he.Df x)
  let l := fun x=> ddf f x*g x+deriv f x*deriv g x+(deriv f x*deriv g x+f x*ddf g x)
  have hc(x): HasDerivAt k (l x) x:=
    ((h.Db x).fun_mul (he.Df x)).fun_add ((h.Df x).fun_mul (he.Db x))
  have h1 : Continuous l:=
    ((h.c.mul he.h.continuous).add (h.g.continuous.mul he.g.continuous)).add
      ((h.g.continuous.mul he.g.continuous).add (h.h.continuous.mul he.c))
  apply mkGuard hd hc h1 (fun x=>absMul (h.fa x) (he.fa x))
    (fun x=>absAdd (absMul (h.fb x) (he.fa x)) (absMul (h.fa x) (he.fb x))) ?_
  intro x
  have heX:=absMul (h.fc x) (he.fa x)
  have hh:=absMul (h.fb x) (show |deriv g x|≤_ from (by exact he.fb x))
  have hj:=absMul (h.fa x) (he.fc x)
  apply le_trans (absAdd (absAdd heX hh) (absAdd hh hj))
  apply le_of_eq; unfold Cap.times;dsimp only;ring

lemma sq (h:Guard f A):Guard (fun x=>f x^2) (Cap.times A A):=by simpa only [pow_two] using h.prod h
end Guard
end GeneralMahler.SCal.Mid

end

end OAI
