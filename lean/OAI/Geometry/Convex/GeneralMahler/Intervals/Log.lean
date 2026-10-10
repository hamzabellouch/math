import OAI.Geometry.Convex.GeneralMahler.Intervals.Elem

namespace OAI
namespace GeneralMahler.Cert.IV
open Real Finset

lemma mtwo : (2:ℝ)∈(2:IV) := mc 2
lemma mhalf : (1/2:ℝ)∈(1/2:IV) := mdiv mo mtwo

def seriesL (Y:IV):ℕ→IV×IV
  | 0=>(Y,0)
  | n+1=>let z:= seriesL Y n; (z.1*(sq Y), z.2+z.1/c (Int.ofNat (2*n+1)))
def logY (X:IV) := (X-1)/(X+1)
def lob (X:IV) := Less 0 X && LeB (Zabs (logY X)) (1/2)
def errLog : IV := box (-10000000000000) 10000000000000
def lbox0 (X:IV):=2*((seriesL (logY X) 32).2+errLog)

lemma mseriesL {y:ℝ} {Y:IV} (hy:y∈Y) (n:ℕ) :
    y^(2*n+1)∈(seriesL Y n).1 ∧
      (∑ i∈range n, y^(2*i+1)/(↑(2*i+1:Nat):ℝ))∈(seriesL Y n).2 := by
  induction n with
  | zero=> simpa [seriesL] using (And.intro hy mz)
  | succ n ih=>
    rw [seriesL,sum_range_succ]
    have he:= mmul ih.1 (msq hy)
    refine ⟨?_,madd ih.2 (mdiv ih.1 (nc _))⟩
    rw [show 2*(n+1)+1=(2*n+1)+2 by omega, pow_add]
    exact he
lemma mlbox0 {x:ℝ} {X:IV} (hx:x∈X) (he:lob X=true) :
    Real.log x∈ lbox0 X := by
  let y:=(x-1)/(x+1)
  have hh : y∈logY X := mdiv (msub hx mo) (madd hx mo)
  simp only [lob,Bool.and_eq_true] at he
  obtain ⟨hu,hv⟩ := he
  have hp := mlt mz hx hu
  have ht := mle (mabs hh) mhalf hv
  change |y| ≤1/2 at ht
  have h₁ : (1+y)/(1-y) = x := by unfold y; field_simp; ring
  have h₂ : |y|<1 := by linarith
  let P:=∑ i∈range 32,y^(2*i+1)/(↑(2*i+1:Nat):ℝ)
  have hi : 1/2*Real.log x-P∈errLog := by
    have he:= Real.sum_range_sub_log_div_le h₂ 32
    rw [h₁] at he
    have hi : |1/2*Real.log x-P|≤ |y|^(2*32+1)/(1-y^2) := by
      convert he using 2
      unfold P; push_cast; rfl
    have hv : |y|^(2*32+1)/(1-y^2)≤ ((1/2:ℝ)^(2*32+1))/(1-(1/2:ℝ)^2) := by
      have h₁ : y^2≤ (1/2:ℝ)^2 := sq_le_sq.2 (by simpa using ht)
      gcongr
    have hh:=abs_le.mp (le_trans hi hv)
    change w _ ≤ _ ∧ _ ≤ w _
    norm_num [w,den] at *
    constructor <;> linarith
  apply (show 2*(P+(1/2*Real.log x-P))=Real.log x by ring) ▸
    mmul mtwo (madd (mseriesL hh _).2 hi)
def lbox : ℕ→IV→IV
  | 0,A=> if lob A then lbox0 A else unk
  | n+1,A=>if Less 0 A then if lob A then lbox0 A else
      2*lbox n (rtB A)
    else unk

lemma mlbox {x:ℝ} {A:IV} (h:x∈A) (n:ℕ) :
    Real.log x∈ lbox n A := by
  induction n generalizing A x with
  | zero=>
    rw [lbox]; split
    next hh=> exact mlbox0 h hh
    trivial
  | succ n ih=>
    rw [lbox]; split
    next he=>
      split
      next hh=> exact mlbox0 h hh
      have hp : 0<x := mlt mz h he
      have hi:=Real.log_sqrt hp.le
      have heq : 2*Real.log (Real.sqrt x) = Real.log x := by linarith
      exact heq ▸ mmul mtwo (ih (mrt h))
    trivial
end GeneralMahler.Cert.IV

end OAI
