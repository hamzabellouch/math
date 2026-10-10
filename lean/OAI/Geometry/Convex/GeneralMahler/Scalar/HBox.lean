import OAI.Geometry.Convex.GeneralMahler.Scalar.HSeries
import OAI.Geometry.Convex.GeneralMahler.Intervals.Log

namespace OAI
namespace GeneralMahler.SCal
open Set Filter MeasureTheory MeasureTheory.Measure Real
open scoped Topology NNReal ENNReal Interval
open Cert Cert.IV Finset
-- coefficient taylor
noncomputable def Qpol (i n:ℕ) (u:ℝ):=
  ∑ j∈Finset.range n,hCoef i j*u^j / ((i+j+2:Nat):ℝ)
lemma Qh_est (i n:ℕ) (u:ℝ) (hu:0≤u) (h:u<1):
    Qpol i n u≤Qh i u ∧ Qh i u ≤ Qpol i n u+
      hCoef i n*u^n*(1/(1-u))^(i+1) := by
  let f := fun t=> t^(i+1)*Rpoly i n (u*t)
  let C:=hCoef i n*u^n*(1/(1-u))^(i+1)
  have hm (t:ℝ) (ht:t∈Set.Icc (0:ℝ) 1) : f t ≤ Qhv i u t ∧ Qhv i u t ≤ f t+C := by
    have ht' : 0≤t:=ht.1
    have ht₁ : t≤1:=ht.2
    have he : u*t ≤ u := mul_le_of_le_one_right hu ht₁
    obtain ⟨ha,hb⟩:= r_est i n (mul_nonneg hu ht') (lt_of_le_of_lt he h)
    have hg : Qhv i u t = t^(i+1)*Rpow i (u*t) := by unfold Qhv Rpow hden; ring
    rw [hg]; unfold f
    rw [sub_nonneg] at ha
    refine ⟨mul_le_mul_of_nonneg_left ha (by positivity),?_⟩
    have hs : 0≤hCoef i n:= by unfold hCoef; positivity
    have hp := pow_le_one₀ ht' ht₁ (n:=i+1)
    have hq : 0<1-u:= by linarith
    have hv := mul_le_mul_of_nonneg_left hb (show 0 ≤ t^(i+1) by positivity)
    have hd : 0 < 1-u*t:= by linarith
    have hh : t^(i+1)*(hCoef i n*(u*t)^n*Rpow i (u*t))≤ C := by
      apply le_trans (mul_le_of_le_one_left (show 0 ≤ hCoef i n*(u*t)^n*Rpow i (u*t) by unfold Rpow; positivity) hp)
      unfold Rpow C
      gcongr
    linarith
  have he : (∫ t in (0:ℝ)..1,f t) = Qpol i n u := by
    have he (t): f t=∑ j∈Finset.range n,(hCoef i j*u^j)*t^(i+j+1) := by
      unfold f Rpoly; rw [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro j _
      simp_rw [pow_add,mul_pow]; ring
    simp_rw [he]
    rw [intervalIntegral.integral_finsetSum]
    · unfold Qpol
      apply Finset.sum_congr rfl; intro j _
      rw [intervalIntegral.integral_const_mul, integral_pow]; push_cast; norm_num; ring
    exact fun i _=> Continuous.intervalIntegrable (by fun_prop) ..
  have hc : Continuous f := by unfold f Rpoly; fun_prop
  have hi:= hc.intervalIntegrable (μ:=volume) 0 1
  have HH:=intH i h
  rw [← he]
  constructor
  · apply intervalIntegral.integral_mono_on zero_le_one hi HH
    exact fun t h=> (hm t h).1
  have hv:= intervalIntegral.integral_mono_on zero_le_one HH (g:=fun t=> f t+C)
    (hi.add (intervalIntegrable_const ..)) (fun t h=> (hm t h).2)
  rw [intervalIntegral.integral_add hi intervalIntegrable_const,intervalIntegral.integral_const] at hv
  simpa only [Qh,C,sub_zero,one_smul] using hv

def cB (i j:Nat):IV:=IV.c (Int.ofNat ((i+j).choose j))
lemma mcb (i j:Nat): hCoef i j ∈ cB i j:= nc ((i+j).choose j)

def bsumH (U:IV) (i:Nat): ℕ→ IV×IV
  | 0=>(1,0)
  | n+1=>
    let (a,b):=bsumH U i n
    (a*U,b+((cB i n)*a)/(IV.c (Int.ofNat (i+n+2))))
lemma mbsumH (U:IV) (i:Nat) (u:ℝ) (h:u∈U) (n:ℕ):
    u^n∈(bsumH U i n).1 ∧ Qpol i n u∈(bsumH U i n).2 := by
  induction n with
  | zero=> simpa [Qpol,bsumH] using And.intro mo mz
  | succ n ih=>
    rw [bsumH,pow_succ,Qpol,Finset.sum_range_succ]
    exact ⟨mmul ih.1 h,madd ih.2 (mdiv (mmul (mcb _ _) ih.1) (nc (i+n+2)))⟩
-- hBox assumes real u in the designated range
def hBox (U:IV) (i n:Nat):IV :=
  let (a,b):= bsumH U i n
  b + IV.span 0 (cB i n*a*(1/(1-U))^(i+1))
lemma mhBox {U:IV} (i n:Nat) {u:ℝ} (hu:0≤u) (h:u<1) (hx:u∈U):
    Qh i u∈hBox U i n := by
  obtain ⟨hp,hq⟩:=Qh_est i n u hu h
  obtain ⟨ha,hb⟩:=mbsumH U i u hx n
  let k:= Qh i u-Qpol i n u
  have h₁: 0≤k:=sub_nonneg.mpr hp
  have h₂: k≤hCoef i n*u^n*(1/(1-u))^(i+1) := by unfold k; linarith
  have he := mmul (mmul (mcb i n) ha) (mpow (mdiv mo (msub mo hx)) (i+1))
  exact (show Qpol i n u+k=Qh i u from by unfold k; ring) ▸ madd hb (span_conv mz he h₁ h₂)
end GeneralMahler.SCal

end OAI
