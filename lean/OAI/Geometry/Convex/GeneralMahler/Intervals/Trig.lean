import OAI.Geometry.Convex.GeneralMahler.Intervals.Log

namespace OAI
namespace GeneralMahler.Cert.IV
open Complex Finset

abbrev Duo:=IV×IV
def covers (v:Duo) (x:ℂ):Prop :=
  x.re∈v.1 ∧ x.im∈v.2
def isum (X:IV) : ℕ→ Duo × Duo
  | 0=> ((1,0),(0,0))
  | n+1=>
    let (a,b):=isum X n
    let Y:=X/c (Int.ofNat (n+1))
    ((-(a.2*Y),a.1*Y),(b.1+a.1,b.2+a.2))
lemma misum {x:ℝ} {X:IV} (hx:x∈X) (n):
    let t : ℕ→ℂ:=fun k=>(↑x*I)^k/k.factorial
    covers (isum X n).1 (t n) ∧ covers (isum X n).2 (∑ i∈range n,t i) := by
  intro t; induction n with
  | zero=>
    simp only [isum,t,pow_zero,Nat.factorial_zero,Nat.cast_one,div_one,sum_range_zero]
    exact ⟨⟨mo,mz⟩,⟨mz,mz⟩⟩
  | succ n ih=>
    let a:ℝ:=x/((n+1:Nat):ℝ)
    have ha:a∈ (X / c (Int.ofNat (n+1))) := mdiv hx (nc (n+1))
    have he : t (n+1)= t n*a*I := by unfold t a; rw [pow_succ,Nat.factorial_succ]; push_cast; field_simp
    have h1 : (t (n+1)).re= -((t n).im*a) := by rw [he]; simp
    have h2 : (t (n+1)).im=(t n).re*a := by rw [he]; simp
    constructor
    · refine ⟨?_,?_⟩
      · rw [h1]; exact mneg (mmul ih.1.2 ha)
      rw [h2]; exact mmul ih.1.1 ha
    rw [sum_range_succ]
    exact ⟨madd ih.2.1 ih.1.1,madd ih.2.2 ih.1.2⟩

def smallsc (X:IV) : Duo :=
  let a:=(isum X 25).2
  (a.1+terr,a.2+terr)
lemma msmallsc {x:ℝ} {X:IV} (hx:x∈X) (h:|x|≤1) :
    Real.cos x∈(smallsc X).1∧Real.sin x∈(smallsc X).2 := by
  let y := (x:ℂ)* I
  have he : ‖y‖=|x| := by simp [y]
  let v:ℂ:=∑ i∈range 25,y^i/i.factorial
  let R:= Complex.exp y-v
  have hp := Complex.exp_bound (x:=y) (by rwa [he]) (show 0<25 by decide)
  have hw : ‖R‖ ≤_ := hp
  have hr {x:ℝ} (hx:|x| ≤ ‖R‖):x∈terr := by
    have h1:= abs_le.mp hx
    have h2 := pow_le_one₀ (_root_.abs_nonneg _) h (n:=25)
    change w _ ≤ _ ∧ _ ≤ w _
    rw [he] at hw
    norm_num [w,den,Nat.factorial] at *
    constructor <;> linarith
  have hv:= misum hx 25
  change _ ∧ covers _ v at hv
  have hi : covers (smallsc X) (Complex.exp y) := by
    rw [show Complex.exp y=v+R from by unfold R; ring]
    exact ⟨madd hv.2.1 (hr (abs_re_le_norm R)),madd hv.2.2 (hr (abs_im_le_norm R))⟩
  unfold y covers at hi
  simpa using hi

def trbox : ℕ→IV→ Duo
  | 0,X=> if LeB (Zabs X) 1 then smallsc X else (unk,unk)
  | n+1,X=>
    if LeB (Zabs X) 1 then smallsc X else
      let (c,s):=trbox n (X/(2:IV))
      (sq c - sq s,2*c*s)
lemma mtrbox {x:ℝ} {X:IV} (hx:x∈X) (n:ℕ) :
    Real.cos x∈(trbox n X).1 ∧ Real.sin x∈(trbox n X).2 := by
  induction n generalizing x X with
  | zero=>
    rw [trbox]; split
    next he=> exact msmallsc hx (mle (mabs hx) mo he)
    exact ⟨trivial,trivial⟩
  | succ n ih=>
    rw [trbox]; split
    next he=> exact msmallsc hx (mle (mabs hx) mo he)
    obtain ⟨H,G⟩:= ih (mdiv hx mtwo)
    have ha : Real.cos x=Real.cos (x/2)^2-Real.sin (x/2)^2 := by
      conv_lhs=> rw [show x=x/2+x/2 from by ring,Real.cos_add]
      ring
    have hb : Real.sin x=2*Real.cos (x/2)*Real.sin (x/2) := by
      conv_lhs=> rw [show x=x/2+x/2 from by ring,Real.sin_add]
      ring
    rw [ha,hb]; exact ⟨msub (msq H) (msq G),mmul (mmul mtwo H) G⟩
end GeneralMahler.Cert.IV

end OAI
