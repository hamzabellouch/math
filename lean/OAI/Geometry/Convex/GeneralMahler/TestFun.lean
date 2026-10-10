import OAI.Geometry.Convex.GeneralMahler.MillsLog

namespace OAI
/-! Real test functions, all orders of polynomial growth used in the proof. -/
noncomputable section
open MeasureTheory Set Filter Real Metric
namespace GeneralMahler

def Moderate : ℕ→(ℝ→ℝ)→Prop
  | 0,f=> PolyBound f ∧ Continuous f
  | n+1,f => PolyBound f ∧ Differentiable ℝ f ∧ Moderate n (deriv f)
def TestF (f:ℝ→ℝ) := ∀ n, Moderate n f
variable {f g:ℝ→ℝ} {n : ℕ}
namespace Moderate
lemma poly (hf:Moderate n f) : PolyBound f := by cases n <;> apply hf.1
lemma diff (hf:Moderate (n+1) f) : Differentiable ℝ f := hf.2.1
lemma dc (hf:Moderate n f) : Continuous f := by
  cases n
  · exact hf.2
  exact hf.diff.continuous
lemma der (hf:Moderate (n+1) f) : Moderate n (deriv f) := hf.2.2
lemma mk (hh:∀ x, HasDerivAt f (g x) x) (hb:PolyBound f) (hc:Moderate n g) :
    Moderate (n+1) f := by
  have h : deriv f=g := funext fun x=>(hh x).deriv
  exact ⟨hb,fun x=>(hh x).differentiableAt,h.symm ▸ hc⟩
lemma mk' (hh:∀ x, HasDerivAt f (g x) x) (hc:Moderate n g) :
    Moderate (n+1) f := mk hh (poly_of_d hh hc.poly) hc
lemma mono (hf:Moderate (n+1) f) : Moderate n f := by
  induction n generalizing f with
  | zero=> exact ⟨hf.poly,hf.dc⟩
  | succ n ih=> exact ⟨hf.poly,hf.diff,ih hf.der⟩
lemma add (hf:Moderate n f) (hg:Moderate n g) : Moderate n fun x=>f x+g x := by
  induction n generalizing f g with
  | zero=> exact ⟨hf.poly.add hg.poly,hf.dc.add hg.dc⟩
  | succ n ih=>
    exact mk' (fun x=> (hf.diff x).hasDerivAt.fun_add (hg.diff x).hasDerivAt)
      (ih hf.der hg.der)
lemma neg (hf:Moderate n f) : Moderate n fun x=> -(f x) := by
  induction n generalizing f with
  | zero=> exact ⟨hf.poly.neg,hf.dc.neg⟩
  | succ n ih=>
    exact mk' (fun x=> (hf.diff x).hasDerivAt.neg) (ih hf.der)
lemma sub (hf:Moderate n f) (hg:Moderate n g) : Moderate n fun x=>f x-g x := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg
lemma mul (hf:Moderate n f) (hg:Moderate n g) : Moderate n fun x=> f x*g x := by
  induction n generalizing f g with
  | zero=> exact ⟨hf.poly.mul hg.poly,hf.dc.mul hg.dc⟩
  | succ n ih=>
    exact mk' (fun x=>(hf.diff x).hasDerivAt.fun_mul (hg.diff x).hasDerivAt)
      ((ih hf.der hg.mono).add (ih hf.mono hg.der))
lemma ref (hf:Moderate n f) : Moderate n fun x=>f (-x) := by
  induction n generalizing f with
  | zero=> exact ⟨hf.poly.comp PolyBound.id.neg,hf.dc.comp continuous_neg⟩
  | succ n ih=>
    apply mk' (g:=fun x=> -deriv f (-x)) _ (ih hf.der).neg
    intro x
    convert (hf.diff (-x)).hasDerivAt.comp x (hasDerivAt_neg' x) using 1
    all_goals first | rfl | ring
lemma const (c:ℝ) (n:ℕ) : Moderate n fun _=> c := by
  induction n generalizing c with
  | zero=> exact ⟨PolyBound.const _, continuous_const⟩
  | succ n ih=> exact mk' (fun x=>hasDerivAt_const x c) (ih 0)
lemma id (n : ℕ) : Moderate n fun x=> x := by
  cases n with
  | zero=> exact ⟨PolyBound.id,continuous_id⟩
  | succ n=> exact mk' (fun x=>hasDerivAt_id' x) (const 1 n)
end Moderate

namespace TestF
variable (hf:TestF f)
include hf in lemma poly : PolyBound f := (hf 0).1
include hf in lemma cont : Continuous f := (hf 0).2
include hf in lemma diff : Differentiable ℝ f := Moderate.diff (hf 1)
include hf in lemma der : TestF (deriv f) := fun n=> Moderate.der (hf (n+1))
lemma of_d (hf:∀ x,HasDerivAt f (g x) x) (hg:TestF g) : TestF f :=
  fun n=> Moderate.mono (Moderate.mk' hf (hg n))

include hf in lemma add (hg:TestF g) : TestF fun x=> f x+g x := fun n=>(hf n).add (hg n)
include hf in lemma sub (hg:TestF g) : TestF fun x=> f x-g x := fun n=>(hf n).sub (hg n)
include hf in lemma mul (hg:TestF g) : TestF fun x=> f x*g x := fun n=>(hf n).mul (hg n)
include hf in lemma neg : TestF fun x=> -(f x) := fun n=>(hf n).neg
include hf in lemma ref : TestF fun x=> f (-x) := fun n=>(hf n).ref
lemma const (c:ℝ) : TestF fun _=> c := Moderate.const c
lemma id : TestF fun x=>x := Moderate.id
end TestF

namespace Layers
lemma mc_test : TestF MillsC := by
  intro n; induction n with
  | zero=> exact ⟨poly_mc,c_mc⟩
  | succ n ih=>
    apply Moderate.mk' d_mc
    exact (((Moderate.id n).add ih).mul ih).neg
lemma mj_test : TestF MillsJ := TestF.id.add mc_test
lemma mw_test : TestF MillsW := mj_test.mul mc_test
lemma lc_test : TestF LC := TestF.of_d d_lc mj_test.neg
lemma lp_test : TestF LP := TestF.of_d d_lp mc_test
end Layers
end GeneralMahler

end

end OAI
