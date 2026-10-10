import OAI.Geometry.Convex.GeneralMahler.Intervals.Basic

namespace OAI
/-! Interval square root and exponential. -/
namespace GeneralMahler.Cert.IV
def piB : IV := box 3141592653589793238460000000000
  3141592653589793238470000000000
lemma mpi : Real.pi ∈ piB := by
  have h₁ := Real.pi_gt_d20; have h₂:=Real.pi_lt_d20
  change w _ ≤ _ ∧ _ ≤ w _
  norm_num [w,den] at *
  constructor <;> linarith

def isrt (n: Int) : Nat → Int → Int
  | 0,x=>x
  | m+1,x=> let y:=(x+n/x)/2; if y<x then isrt n m y else x
def getR (a:Int) : Int :=
  -- A fixed initial upper estimate feeds the integer Newton iteration.
  -- Failed enclosure inequalities produce the unknown interval.
  isrt (a*den) 112 (1000*den)

def rlo (a:Int) : Int := if a>0 then getR a else 0

def rtB : IV→IV
  | unk=>unk
  | box a b =>
    let l:= rlo a
    let u:= getR (max b 0)+1
    if u≥0 && (max b 0)*den ≤ u*u && (a≤0 || (l≥0 && l*l ≤ a*den)) then box l u
    else unk

private lemma callSq (q a:Int): w q^2-w a=((q*q-a*den:Int):ℝ)/(den:ℝ)^2 := by
  unfold w; push_cast; field_simp
private lemma Lsq {a q:Int} (h:0< a) (hh:q*q≤a*den): w q ≤ Real.sqrt (w a) := by
  have hi : w q^2≤w a := by
    rw [← sub_nonpos,callSq]
    apply div_nonpos_of_nonpos_of_nonneg ?_ (sq_nonneg _)
    exact_mod_cast (sub_nonpos.mpr hh)
  have hp : 0≤w a := by have h := w_strict h; rw [w0] at h; exact h.le
  nlinarith [Real.sq_sqrt hp,Real.sqrt_nonneg (w a)]
private lemma Usq {a q:Int} (hq:0≤q) (h:0≤a) (hh:a*den≤q*q) :
    Real.sqrt (w a) ≤ w q := by
  have hi : w a≤w q^2 := by
    rw [← sub_nonneg,callSq]
    apply div_nonneg ?_ (sq_nonneg _)
    exact_mod_cast (sub_nonneg.mpr hh)
  have hp (a:Int) (ha:0≤a) : 0≤w a := by have h:=w_mono ha; rwa [w0] at h
  nlinarith [Real.sq_sqrt (hp a h),hp q hq,Real.sqrt_nonneg (w a)]
lemma mrt {x:ℝ} {A:IV} (h:x∈A) : Real.sqrt x ∈ rtB A := by
  cases A
  · trivial
  rename_i a b
  rw [rtB]
  split
  next hh=>
    simp only [Bool.and_eq_true,Bool.or_eq_true,decide_eq_true_eq] at hh
    change w _ ≤ _ ∧ _≤ w _
    refine ⟨?_,le_trans (Real.sqrt_le_sqrt (le_trans h.2 (w_mono (le_max_left b 0))))
      (Usq hh.1.1 (le_max_right b 0) hh.1.2)⟩
    unfold rlo at *
    by_cases he: a>0
    · have hj := (hh.2.resolve_left (not_le.mpr he)).2
      rw [ite_eq_left he] at hj ⊢
      exact le_trans (Lsq he hj) (Real.sqrt_le_sqrt h.1)
    rw [ite_eq_right he,w0]; apply Real.sqrt_nonneg
  trivial

def eSeries (A:IV) : ℕ→IV×IV
  | 0=>(1,0)
  | n+1=>
    let p:=eSeries A n
    (p.1*A/c (Int.ofNat (n+1)),p.2+p.1)
open Finset
lemma mSeries {x:ℝ} {A:IV} (h:x∈A) (n:Nat):
    x^n/n.factorial∈(eSeries A n).1∧
      (∑ m∈range n,x^m/m.factorial)∈(eSeries A n).2 := by
  induction n with
  | zero => simpa [eSeries] using (And.intro mo mz)
  | succ n ih =>
    unfold eSeries
    refine ⟨?_,?_⟩
    · have he := mdiv (mmul ih.1 h) (nc (n+1))
      have hi : x^(n+1)/(n+1).factorial=(x^n/n.factorial*x)/(n+1:Nat) := by
        rw [Nat.factorial_succ,pow_succ]; push_cast; field_simp
      rw [hi]
      exact he
    rw [Finset.sum_range_succ]; exact madd ih.2 ih.1

-- error < 1e-24 through terms n=0:24.
def terr : IV := box (-1000000) 1000000

protected def esmall (A:IV) : IV :=
  clampNN ((eSeries A 25).2+terr)
lemma mesmall {x:ℝ} {A:IV} (h:x∈A) (hx:|x|≤1) :
    Real.exp x ∈ IV.esmall A := by
  let v:ℝ:=∑ m∈range 25,x^m/m.factorial
  have hp : Real.exp x-v ∈ terr := by
    have he := Real.exp_bound hx (show 0<25 by decide)
    have hh : |x|^25 ≤1 := pow_le_one₀ (_root_.abs_nonneg x) hx
    change w _ ≤ _ ∧ _ ≤ w _
    have hm : |Real.exp x-v| ≤ _ := he
    have hr : (0:ℝ)< (↑(25+1:ℕ):ℝ) / (((25:ℕ).factorial:ℝ)* ((25:ℕ):ℝ)) := by positivity
    have hi := abs_le.mp hm
    norm_num [w,den,Nat.factorial] at *
    constructor <;> linarith
  apply mclamp _ (Real.exp_pos x).le
  have he := madd (mSeries h 25).2 hp
  rwa [show v+(Real.exp x-v)=Real.exp x by ring] at he

def ebox : ℕ→IV→IV
  | 0,A=> if LeB (Zabs A) 1 then A.esmall else unk
  | n+1,A=>
    if LeB (Zabs A) 1 then A.esmall
    else let B:= ebox n (A/(2:IV)); B*B

lemma mebox {x:ℝ} (n:ℕ) {A:IV} (h:x∈A): Real.exp x∈ebox n A := by
  induction n generalizing x A with
  | zero=>
    rw [ebox]
    split
    next he=> exact mesmall h (mle (mabs h) mo he)
    trivial
  | succ n ih=>
    rw [ebox]
    split
    next he=> exact mesmall h (mle (mabs h) mo he)
    have htwo : (2:ℝ)∈(2:IV) := mc 2
    have he:=ih (mdiv h htwo)
    apply (show Real.exp (x/2)*Real.exp (x/2)=Real.exp x by rw [← Real.exp_add]; congr 1; ring) ▸ mmul he he
end GeneralMahler.Cert.IV

end OAI
