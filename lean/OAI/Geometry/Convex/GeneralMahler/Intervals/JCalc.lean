import OAI.Geometry.Convex.GeneralMahler.Intervals.Jet
import OAI.Geometry.Convex.GeneralMahler.Intervals.Log

namespace OAI
/-! Tower AD for exp, log, inverse, square root. -/
open Set Real
namespace GeneralMahler.Jet

noncomputable def vn (n:ℕ):ℝ:=n
def invJs {α} [Inv α] [Mul α] [Neg α] (c:ℕ→α) (x:α) : J α
  | 0=>x⁻¹
  | n+1=> -(c (n+1)*(x⁻¹)* invJs c x n)
def rootJs {α} [Inv α] [Mul α] [Sub α] (h:α) (c:ℕ→α) (x a:α) : J α
  | 0=>a
  | n+1=>(h-c n)*(x⁻¹)* rootJs h c x a n
def logJs {α} [Inv α] [Mul α] [Neg α] (c:ℕ→α) (x a:α) : J α
  | 0=>a
  | n+1=>invJs c x n

-- utilities (exp evaluation an external input)
def expSub {α} [Add α] [Mul α] (X:J α) (a:α) : J α :=
  compJ (fun _=>a) X
def invSub {α} [Add α] [Inv α] [Mul α] [Neg α] (c:ℕ→α) (X:J α) : J α :=
  compJ (invJs c (X 0)) X
def logSub {α} [Add α] [Inv α] [Mul α] [Neg α] (c:ℕ→α) (X:J α) (a:α) : J α :=
  compJ (logJs c (X 0) a) X
def rootSub {α} [Add α] [Inv α] [Mul α] [Sub α] (h:α) (c:ℕ→α) (X:J α) (a:α) : J α :=
  compJ (rootJs h c (X 0) a) X

lemma twInvs : TW {x:ℝ|x≠0} (invJs vn) := by
  intro n x hx; change x≠0 at hx
  induction n with
  | zero=>
    convert (hasDerivAt_id' x).inv hx using 1
    all_goals first | rfl|skip
    simp [invJs,vn]; ring
  | succ n ih=>
    have he:= ((((hasDerivAt_id' x).inv hx).const_mul (vn (n+1))).fun_mul ih).neg
    convert he using 1
    all_goals first|rfl|skip
    rw [invJs,invJs]
    unfold vn; push_cast
    simp; ring

lemma twRoots : TW {x:ℝ|0<x} (fun x=>rootJs (1/2:ℝ) vn x (Real.sqrt x)) := by
  intro n x hx; change 0<x at hx
  induction n with
  | zero=>
    have hp := Real.sqrt_pos.mpr hx
    convert Real.hasDerivAt_sqrt hx.ne' using 1
    all_goals first|rfl|skip
    simp only [rootJs,vn,Nat.cast_zero,sub_zero]
    have hi:= Real.sq_sqrt hx.le
    field_simp
    linarith
  | succ n ih=>
    have he:= ((((hasDerivAt_id' x).inv hx.ne').const_mul ((1/2:ℝ)-vn n)).fun_mul ih)
    convert he using 1
    all_goals first|rfl|skip
    simp only [rootJs]; unfold vn; push_cast; simp; ring
lemma twLogs : TW {x:ℝ|x≠0} (fun x=>logJs vn x (Real.log x)) := by
  intro n x hx; cases n with
  | zero=>exact (by convert Real.hasDerivAt_log hx using 1 <;> rfl)
  | succ n=> exact twInvs n x hx
variable {S:Set ℝ} {X:RF}
lemma TW.inv (h:TW S X) (hx:∀ x∈S, X x 0 ≠ 0): TW S fun x=> invSub vn (X x) := h.comp twInvs hx
lemma TW.root (h:TW S X) (hx:∀ x∈S, 0<X x 0):
    TW S fun x=> rootSub (1/2) vn (X x) (Real.sqrt (X x 0)) := h.comp twRoots hx
lemma TW.log (h:TW S X) (hx:∀ x∈S,X x 0≠ 0): TW S fun x=> logSub vn (X x) (Real.log (X x 0)):=
  h.comp twLogs hx
lemma TW.exp (h:TW S X) :
    TW S fun x=> expSub (X x) (Real.exp (X x 0)) :=
  h.comp (show TW univ fun x _=>Real.exp x from fun _ x _=>Real.hasDerivAt_exp x)
    (fun _ _=> mem_univ _)

open Cert Cert.IV
def ub (n:ℕ):IV:=c n
lemma ubb (n:ℕ):vn n∈ub n := nc n
variable {V:J ℝ} {A:J IV}

lemma fitsInv {x:ℝ} {y:IV} (h:x∈y): Fits (invJs vn x) (invJs ub y) := by
  intro n; induction n with
  | zero=> exact minv h
  | succ n ih=> exact mneg (mmul (mmul (ubb _) (minv h)) ih)
lemma Fits.inv (h:Fits V A):Fits (invSub vn V) (invSub ub A) :=
  Fits.comp h (fitsInv (h 0))
lemma Fits.rt (h:Fits V A){B} (hh:Real.sqrt (V 0)∈B):
    Fits (rootSub (1/2) vn V (Real.sqrt (V 0))) (rootSub (1/2) ub A B) := by
  apply Fits.comp h
  intro n; induction n with
  | zero=> exact hh
  | succ n ih=> exact mmul (mmul (msub mhalf (ubb _)) (minv (h _))) ih
lemma Fits.log (h:Fits V A){B} (hh:Real.log (V 0)∈B):
    Fits (logSub vn V (Real.log (V 0))) (logSub ub A B) :=
  Fits.comp h (by
    intro n; cases n with
    | zero=>exact hh
    | succ n=>exact fitsInv (h 0) n)
lemma Fits.exp (h:Fits V A){B}(hh:Real.exp (V 0)∈B):
    Fits (expSub V (Real.exp (V 0))) (expSub A B) :=
  Fits.comp h fun _=>hh
end GeneralMahler.Jet

end OAI
