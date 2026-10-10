import Mathlib
import OAI.Combinatorics.Chromatic.GradedAlgebra.MutationOrientedCompatibility

namespace OAI

section
namespace ElementaryPositivity.FormalLog
open PowerSeries
noncomputable section
variable {A : Type*} [Ring A]
lemma inverse_coeff_congr (F G : PowerSeries A) (hF : constantCoeff F=1)
    (hG : constantCoeff G=1) (N : ℕ) (H : ∀n≤N,coeff n F=coeff n G) :
    ∀n≤N,coeff n (invOfUnit F 1)=coeff n (invOfUnit G 1) := by
  intro n hn
  have HH:=mul_coeff_congr (invOfUnit F 1) (F*invOfUnit G 1)
    (invOfUnit F 1) (G*invOfUnit G 1) n (fun _ _=>rfl) (by
      intro j hj
      exact mul_coeff_congr _ _ _ _ j (fun k hk=>H k (hk.trans (hj.trans hn))) (fun _ _=>rfl))
  rw [←mul_assoc,invOfUnit_mul F 1 hF,one_mul,mul_invOfUnit G 1 hG,mul_one] at HH
  exact HH.symm
variable [Module ℚ A]
@[simp] lemma log_one : FormalLog.log (1 : PowerSeries A)=0 := by
  ext n
  simp [FormalLog.log]
end
end ElementaryPositivity.FormalLog
namespace ElementaryPositivity.QuantumTorus
open PowerSeries PowerSeriesSplit
noncomputable section
variable {R M I : Type*} [CommRing R] [Algebra ℚ R] [AddCommGroup M] [Fintype I]
variable (v : Rˣ) (Ω : M →+ M →+ ℤ) (C : (I → ℤ) →+ M)
local instance incomingTransportTraceRing : Ring (Torus v Ω) := Torus.instRing v Ω
local instance incomingTransportTraceAddCommMonoid : AddCommMonoid (Torus v Ω) := (Torus.instRing v Ω).toAddCommMonoid
local instance incomingTransportTraceAddGroup : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup

lemma chartNegative_log_positive (h : M →+ ℝ) (F : CompletedPositive v Ω C)
    (r : M) (hr : 0≤h r) (n : ℕ) :
    coeff n (FormalLog.log (chartNegative v Ω C h F).val) r=0 := by
  exact strict_log_support v Ω (V:=fun m=>h m<0)
    (fun a b ha hb=>by simpa only [map_add] using add_neg ha hb) _
    (chartNegative v Ω C h F).property.1
    (fun j m hm=>by by_contra hh; exact hm ((chart_three_support v Ω C h F).2.2 j m hh))
    n r (not_lt.mpr hr)

lemma chartNegative_log_negative_kernel (hΩ : ∀m,Ω m m=0) (r : M)
    (F : CompletedPositive v Ω C)
    (hf : ∀n,coeff n F.val∈supportedSubalgebra v Ω (kernelSupport Ω r))
    (h : M →+ ℝ) (hr : h r<0) (n : ℕ) :
    coeff n (FormalLog.log (chartNegative v Ω C h F).val) r=
      coeff n (FormalLog.log F.val) r := by
  let A:=chartPositive v Ω C h F
  let B:=chartZero v Ω C h F
  let D:=chartNegative v Ω C h F
  have hs:=chartThree_supported v Ω C h (kernelSupport Ω r) F hf
  have H1:=kernel_trace_log_product v Ω hΩ r A.val B.val A.property.1 B.property.1 hs.1 hs.2.1 n
  have H2:=kernel_trace_log_product v Ω hΩ r (A.val*B.val) D.val
    (by simp [A.property.1,B.property.1]) D.property.1
    (PowerSeriesSplit.mul_mem (supportedSubring v Ω (kernelSupport Ω r)) _ _ hs.1 hs.2.1) hs.2.2 n
  have hp : coeff n (FormalLog.log A.val) r=0:=by
    exact strict_log_support v Ω (V:=fun m=>0<h m)
      (fun a b ha hb=>by simpa only [map_add] using add_pos ha hb) A.val A.property.1
      (fun j m hm=>by by_contra hh; exact hm ((chart_three_support v Ω C h F).1 j m hh))
      n r (not_lt.mpr hr.le)
  have hz : coeff n (FormalLog.log B.val) r=0:=by
    exact strict_log_support v Ω (V:=fun m=>h m=0)
      (fun a b ha hb=>by rw [map_add,ha,hb,add_zero]) B.val B.property.1
      (fun j m hm=>by by_contra hh; exact hm ((chart_three_support v Ω C h F).2.1 j m hh))
      n r (ne_of_lt hr)
  rw [H1,hp,hz,zero_add,zero_add] at H2
  rw [show A.val*B.val*D.val=F.val from chart_three_factorization v Ω C h F] at H2
  exact H2.symm

lemma kernel_trace_log_inverse (hΩ : ∀m,Ω m m=0) (r : M)
    (F : PowerSeries (Torus v Ω)) (hf : constantCoeff F=1)
    (hs : ∀n,coeff n F∈supportedSubalgebra v Ω (kernelSupport Ω r)) (n : ℕ) :
    coeff n (FormalLog.log (invOfUnit F 1)) r= -coeff n (FormalLog.log F) r := by
  have hi : ∀j,coeff j (invOfUnit F 1)∈supportedSubalgebra v Ω (kernelSupport Ω r):=by
    intro j m hm
    by_contra hh
    exact hm (inverse_support_addSubmonoid v Ω (kernelSupport Ω r) F
      (fun k a ha=>by by_contra hn; exact ha (hs k a hn)) j m hh)
  have H:=kernel_trace_log_product v Ω hΩ r F (invOfUnit F 1) hf (by simp) hs hi n
  rw [mul_invOfUnit F 1 hf,FormalLog.log_one,map_zero,Finsupp.zero_apply] at H
  exact eq_neg_of_add_eq_zero_right H.symm

lemma incoming_negative_ratio_log (hΩ : ∀m,Ω m m=0) (r : M)
    (F : CompletedPositive v Ω C) (x y : M →+ ℝ) (N : ℕ)
    (hx : ∀n≤N,∀m,HasRootDegree C n m →
      (0 < incomingCovector Ω r m → 0<x m) ∧ (incomingCovector Ω r m<0 → x m<0))
    (hy : ∀n≤N,∀m,HasRootDegree C n m →
      (0 < incomingCovector Ω r m → 0<y m) ∧ (incomingCovector Ω r m<0 → y m<0))
    (hxr : 0≤x r) (hyr : y r<0) :
    ∀n≤N,coeff n (FormalLog.log ((chartNegative v Ω C y F).val*
        invOfUnit (chartNegative v Ω C x F).val 1)) r=
      coeff n (FormalLog.log (chartZero v Ω C (incomingCovector Ω r) F).val) r := by
  let B:=chartZero v Ω C (incomingCovector Ω r) F
  let D:=chartNegative v Ω C (incomingCovector Ω r) F
  let X:=chartNegative v Ω C x B
  let Y:=chartNegative v Ω C y B
  have Hx:=chart_negative_refinement v Ω C (incomingCovector Ω r) x x F N (by
    intro n hn m hm
    exact ⟨(hx n hn m hm).1,(hx n hn m hm).2,fun _=>⟨id,id,id⟩⟩)
  have Hy:=chart_negative_refinement v Ω C (incomingCovector Ω r) y y F N (by
    intro n hn m hm
    exact ⟨(hy n hn m hm).1,(hy n hn m hm).2,fun _=>⟨id,id,id⟩⟩)
  have hi:=FormalLog.inverse_coeff_congr _ _ (chartNegative v Ω C x F).property.1
    (by change constantCoeff (X.val*D.val)=1; simp [X.property.1,D.property.1]) N Hx
  have hinv : invOfUnit (X.val*D.val) 1=invOfUnit D.val 1*invOfUnit X.val 1:=by
    apply left_inv_eq_right_inv (PowerSeries.invOfUnit_mul _ 1 (by simp [X.property.1,D.property.1]))
    simp only [mul_assoc,←mul_assoc D.val,PowerSeries.mul_invOfUnit D.val 1 D.property.1,
      one_mul,PowerSeries.mul_invOfUnit X.val 1 X.property.1]
  have he : ∀n≤N,coeff n ((chartNegative v Ω C y F).val*invOfUnit (chartNegative v Ω C x F).val 1)=
      coeff n (Y.val*invOfUnit X.val 1):=by
    intro n hn
    have H:=FormalLog.mul_coeff_congr _ _ _ _ n
      (fun j hj=>Hy j (hj.trans hn)) (fun j hj=>hi j (hj.trans hn))
    rw [hinv,mul_assoc,←mul_assoc D.val,PowerSeries.mul_invOfUnit D.val 1 D.property.1,one_mul] at H
    exact H
  have hB:=incoming_chart_supported v Ω C r F
  have hsX:=(chartThree_supported v Ω C x (kernelSupport Ω r) B hB).2.2
  have hsY:=(chartThree_supported v Ω C y (kernelSupport Ω r) B hB).2.2
  have hsI : ∀j,coeff j (invOfUnit X.val 1)∈supportedSubalgebra v Ω (kernelSupport Ω r):=by
    intro j m hm
    by_contra hh
    exact hm (inverse_support_addSubmonoid v Ω _ X.val
      (fun k a ha=>by by_contra hn; exact ha (hsX k a hn)) j m hh)
  intro n hn
  rw [FormalLog.log_coeff_congr _ _ n (fun j hj=>he j (hj.trans hn)),
    kernel_trace_log_product v Ω hΩ r Y.val (invOfUnit X.val 1) Y.property.1 (by simp) hsY hsI n,
    kernel_trace_log_inverse v Ω hΩ r X.val X.property.1 hsX n,
    chartNegative_log_positive v Ω C x B r hxr n,neg_zero,add_zero]
  exact chartNegative_log_negative_kernel v Ω C hΩ r B hB y hyr n
end
end ElementaryPositivity.QuantumTorus

end

end OAI
