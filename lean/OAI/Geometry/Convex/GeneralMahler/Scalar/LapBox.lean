import OAI.Geometry.Convex.GeneralMahler.Scalar.Moments
import OAI.Geometry.Convex.GeneralMahler.Intervals.Log

namespace OAI
/-! §07 interval enclosures for the Ymk via Taylor and CF. -/
open Set Filter MeasureTheory MeasureTheory.Measure Real
open scoped Topology NNReal ENNReal Interval
namespace GeneralMahler.SCal
open Profile Layers Cert Cert.IV
def phi0B:= (rtB ((2:IV)*piB))⁻¹
def cxB (X:IV):= -(sq X)/(2:IV)
def phiB (X:IV):=phi0B*ebox 14 (cxB X)
lemma mphi0: phi 0∈ phi0B := by
  have h : phi 0= (√(2*π))⁻¹ := by simp [phi_apply]
  rw [h]; exact minv (mrt (mmul mtwo mpi))
lemma mcx {x:ℝ} {X:IV} (hx:x∈X): -(x^2)/2∈cxB X := mdiv (mneg (msq hx)) mtwo
lemma mphi {x:ℝ} {X:IV} (hx:x∈X) : phi x∈phiB X := by
  have he : phi x=phi 0*Real.exp (-(x^2)/2) := by simp [phi_apply]
  rw [he]; exact mmul mphi0 (mebox _ (mcx hx))

def pSeries (C:IV) : ℕ → IV×IV
  | 0=>(1,0)
  | n+1=> let (a,b):=pSeries C n
          (a*C/IV.c (Int.ofNat (n+1)),b+a/IV.c (Int.ofNat (2*n+1)))
def pTaylor (X:IV):=
  ((1/2:IV)+ (X*phi0B)*((pSeries (cxB X) 25).2+terr))

open Finset
lemma mpSeries {c:ℝ} {C:IV} (hc:c∈C) (n:ℕ) :
    c^n/n.factorial ∈(pSeries C n).1∧
      (∑ i∈range n,c^i/i.factorial / ((2*i+1:Nat):ℝ)) ∈ (pSeries C n).2 := by
  induction n with
  | zero=> simpa [pSeries] using (And.intro mo mz)
  | succ n ih=>
    rw [pSeries,sum_range_succ]
    refine ⟨?_,madd ih.2 (mdiv ih.1 (nc _))⟩
    have he : c^(n+1)/(n+1).factorial = c^n/n.factorial*c/((n+1:Nat):ℝ) := by
      rw [Nat.factorial_succ,pow_succ]; push_cast; field_simp
    rw [he]; exact mdiv (mmul ih.1 hc) (nc _)

lemma p_int_beta (x:ℝ):
    p x=1/2+x*phi 0*(∫ t in (0:ℝ)..1, Real.exp ((-(x^2)/2)*t^2)) := by
  let F:=fun t:ℝ=> p (t*x)
  let A:= fun t:ℝ=> Real.exp ((-(x^2)/2)*t^2)
  have hd (t): HasDerivAt F ((x*phi 0)*A t) t := by
    have h: HasDerivAt F (phi (t*x)*(1*x)) t :=
      by change HasDerivAt (p ∘ (fun y=>y*x)) _ t; exact (d_p (t*x)).comp t ((hasDerivAt_id' t).mul_const x)
    convert h using 1
    unfold A; simp [phi_apply]; ring_nf
  have hi:= intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _=> hd t)
    ((continuous_const.mul (by unfold A; fun_prop : Continuous A)).intervalIntegrable (0:ℝ) 1)
  rw [intervalIntegral.integral_const_mul] at hi
  simp only [F,one_mul,zero_mul,p_half] at hi
  change p x=1/2+x*phi 0*(∫ t in (0:ℝ)..1,A t)
  linarith

lemma pT_bound (c:ℝ) (hc:|c|≤1) :
    (∫ t in (0:ℝ)..1,Real.exp (c*t^2)) - (∑ i∈range 25,c^i/i.factorial / ((2*i+1:Nat):ℝ)) ∈terr := by
  let S:=fun i:ℕ=> fun t:ℝ=> (c*t^2)^i/i.factorial
  let f:=fun t=> ∑ i∈range 25,S i t
  let g:= fun t:ℝ=> Real.exp (c*t^2)
  have he : (∑ i∈range 25,c^i/i.factorial / ((2*i+1:Nat):ℝ)) =
      ∫ t in (0:ℝ)..1,f t := by
    unfold f; rw [intervalIntegral.integral_finsetSum]
    · apply Finset.sum_congr rfl; intro i _
      have hi : S i=fun t=> (c^i/i.factorial)*t^(2*i) := by
        ext; unfold S; rw [pow_mul,mul_pow]; ring
      rw [hi,intervalIntegral.integral_const_mul,integral_pow]; push_cast; norm_num; ring
    exact fun i _=> (by unfold S; fun_prop : Continuous (S i)).intervalIntegrable ..
  rw [he]
  let v:ℝ := 1/10^24
  have hu (x:ℝ) (hx:x∈Ι (0:ℝ) 1): ‖g x-f x‖≤ v := by
    have hh : 0≤ x ∧ x≤1 := by rw [uIoc_of_le zero_le_one] at hx; exact ⟨hx.1.le,hx.2⟩
    have hx' : |c*x^2| ≤1 := by
      rw [abs_mul,abs_of_nonneg (sq_nonneg x)]
      exact (mul_le_of_le_one_left (sq_nonneg x) hc).trans (by nlinarith [hh.1,hh.2])
    have h:=Real.exp_bound hx' (show 0<25 by decide)
    have hi : ‖g x-f x‖≤ _ := h
    have hp : |c*x^2|^25 ≤1 := pow_le_one₀ (_root_.abs_nonneg _) hx'
    unfold v
    norm_num [Nat.factorial] at *
    linarith
  have ht:=intervalIntegral.norm_integral_le_of_norm_le_const hu
  have hg : Continuous g := by unfold g; fun_prop
  have hf : Continuous f := by unfold f S; fun_prop
  rw [intervalIntegral.integral_sub (hg.intervalIntegrable ..) (hf.intervalIntegrable ..),
    Real.norm_eq_abs] at ht
  have hp:= abs_le.mp ht
  change w _ ≤ (∫ t in (0:ℝ)..1,g t)-_ ∧ _ ≤ w _
  unfold v at *
  norm_num [w,den] at *
  exact hp

lemma mpTaylor {x:ℝ} {X:IV} (hx:x∈X) (he:|-(x^2)/2|≤1):
    p x∈ pTaylor X := by
  let c:ℝ:=-(x^2)/2
  have h:= madd (mpSeries (mcx hx) 25).2 (pT_bound c he)
  change (∑ i∈range 25,c^i/i.factorial/((2*i+1:Nat):ℝ))+((∫ t in (0:ℝ)..1,Real.exp (c*t^2))-_ )∈_ at h
  have hh : (∫ t in (0:ℝ)..1,Real.exp (c*t^2)) ∈ (pSeries (cxB X) 25).2+terr := by
    rw [add_sub_cancel ..] at h
    exact h
  rw [p_int_beta]
  exact madd mhalf (mmul (mmul hx mphi0) hh)

def cEncl (X:IV):ℕ→ℕ→IV
  | 0,n=> span (0:IV) ((IV.c (Int.ofNat (n+1)))/X)
  | j+1,n=> IV.c (Int.ofNat (n+1))/(X+cEncl X j (n+1))
lemma mcEncl {x:ℝ} {X:IV} (hx:x∈X) (hr:0<x) (i n:ℕ) :
    cRat n x∈ cEncl X i n := by
  induction i generalizing n with
  | zero=>
    apply span_conv mz (mdiv (nc _) hx) (cRp n x).le
    have he:= cfIter n x
    rw [le_div_iff₀ hr]
    nlinarith [cRp n x,cRp (n+1) x]
  | succ i ih=>
    have he:=cfIter n x
    rw [show cRat n x = ((n+1:Nat):ℝ)/(x+cRat (n+1) x) from (eq_div_iff (add_pos hr (cRp (n+1) x)).ne').mpr he]
    exact mdiv (nc _) (madd hx (ih _))

def forward (X Y:IV) : ℕ→IV
  | 0=>Y
  | 1=>1-X*Y
  | n+2=> IV.c (Int.ofNat (n+1))*(forward X Y n)-X*(forward X Y (n+1))
lemma mforward {x:ℝ} {X Y:IV} (hx:x∈X) (h:Ymk 0 x∈Y): ∀ n,Ymk n x∈forward X Y n
  | 0=>h
  | 1=>by
    have he : Ymk 1 x = 1-x*Ymk 0 x := by linarith [R0 x]
    rw [he]; exact msub mo (mmul hx h)
  | n+2=>by
    rw [show Ymk (n+2) x = ((n+1:Nat):ℝ)*Ymk n x-x*Ymk (n+1) x from by linarith [Rn x n] ]
    exact msub (mmul (nc _) (mforward hx h n)) (mmul hx (mforward hx h (n+1)))

def prodCF (X:IV) (e:ℕ) : ℕ→IV
  | 0=>(X+cEncl X e 0)⁻¹
  | n+1=>cEncl X (e-n) n*prodCF X e n
lemma mprodCF {x:ℝ} {X:IV} (hx:x∈X) (hr:0<x) (e n:ℕ):
    Ymk n x∈prodCF X e n := by
  induction n with
  | zero=>
    have he:=cfBase x
    have hv:=add_pos hr (cRp 0 x)
    have heq : Ymk 0 x=(x+cRat 0 x)⁻¹ := by rw [← one_div,eq_div_iff hv.ne',mul_comm]; exact he
    rw [heq]; exact minv (madd hx (mcEncl hx hr _ _))
  | succ n ih=>
    have he : Ymk (n+1) x=cRat n x*Ymk n x := by unfold cRat; rw [div_mul_cancel₀ _ (Ymp n x).ne']
    rw [he]; exact mmul (mcEncl hx hr _ _) ih

def ymBox (n:Nat) (X:IV):IV :=
  if LeB (Zabs (cxB X)) 1 then forward X ((1-pTaylor X)/phiB X) n
  else if Less 0 X then prodCF X (if Less (IV.c 4) X then 42 else 112) n
  else unk
lemma myBox {x:ℝ} {X:IV} (hx:x∈X) (n:ℕ): Ymk n x∈ ymBox n X := by
  unfold ymBox; split
  next he=>
    apply mforward hx
    rw [Ym0]
    exact mdiv (msub mo (mpTaylor hx (mle (mabs (mcx hx)) mo he))) (mphi hx)
  split
  next he=> exact mprodCF hx (mlt mz hx he) _ _
  trivial
end GeneralMahler.SCal

end OAI
