import Mathlib.Analysis.Calculus.DerivativeTest
import Mathlib.Analysis.Calculus.LocalExtr.Basic

namespace OAI

/-! The minimum principle on a twelve-dimensional radial ball. -/

open Set Filter Topology
namespace DefocusingNLS

theorem radial_local_min_second_nonneg (f : ℝ → ℝ) (x : ℝ)
    (hf : ContinuousAt f x) (hmin : IsLocalMin f x) :
    0 ≤ deriv (deriv f) x := by
  by_contra! hneg
  have hmax := isLocalMax_of_deriv_deriv_neg hneg hmin.deriv_eq_zero hf
  have heq : f =ᶠ[𝓝 x] fun _ => f x := by
    filter_upwards [hmin,hmax] with y hy hy'
    exact le_antisymm hy' hy
  have hz := heq.deriv.deriv_eq
  have hc : deriv (fun _ : ℝ => f x) = fun _ => 0 := by
    funext y
    simp only [deriv_const]
  rw [hc,deriv_const] at hz
  linarith

theorem radial_minimum_principle_drift (R lo : ℝ) (hR : 0 < R)
    (B : ℝ → ℝ) (hB : ∀ r ∈ Ioo 0 R, 0 < B r) (A : ℝ → ℝ)
    (hA : Differentiable ℝ A) (hzero : deriv A 0=0) (hboundary : lo ≤ A R)
    (hLap : ∀ r ∈ Ioo 0 R, A r < lo →
      deriv (deriv A) r+B r*deriv A r ≤ 0) :
    ∀ r ∈ Icc 0 R, lo ≤ A r := by
  by_contra! hbad
  obtain ⟨r,hr,hrlo⟩ := hbad
  let ε := (lo-A r)/(2*(R+1))
  have hε : 0 < ε := by dsimp only [ε]; positivity
  have heq : ε*(2*(R+1))=lo-A r := by
    dsimp only [ε]
    field_simp [ne_of_gt (show 0 < R+1 by linarith)]
  let F : ℝ → ℝ := fun t => A t+ε*(R-t)
  have hF : Continuous F := hA.continuous.add (continuous_const.mul (continuous_const.sub continuous_id))
  have hFr : F r < lo := by
    dsimp only [F]
    nlinarith [mul_nonneg hε.le hr.1]
  have hd (t : ℝ) : HasDerivAt F (deriv A t-ε) t := by
    convert! (hA t).hasDerivAt.add (((hasDerivAt_id t).const_sub R).const_mul ε) using 1
    ring
  have hdd (t : ℝ) : deriv (deriv F) t=deriv (deriv A) t := by
    rw [show deriv F=fun s => deriv A s-ε from funext (fun s => (hd s).deriv)]
    exact deriv_sub_const ε
  obtain ⟨c,hc,hmin⟩ := isCompact_Icc.exists_isMinOn
    (nonempty_Icc.2 hR.le) hF.continuousOn
  have hcm : F c < lo := (hmin hr).trans_lt hFr
  have hcR : c < R := by
    apply lt_of_le_of_ne hc.2
    intro he
    subst c
    simp only [F,sub_self,mul_zero,add_zero] at hcm
    exact hcm.not_ge hboundary
  have hc0 : 0 < c := by
    apply lt_of_le_of_ne hc.1
    intro he
    have hc_eq : c=0 := he.symm
    subst c
    have hdir : R-0 ∈ posTangentConeAt (Icc 0 R) 0 :=
      sub_mem_posTangentConeAt_of_segment_subset (segment_eq_Icc hR.le ▸ Subset.rfl)
    have hnonneg : 0 ≤ (deriv A 0-ε)*(R-0) := by
      simpa only [ContinuousLinearMap.smulRight_apply,one_apply_eq_self,mul_comm]
        using! hmin.isLocalMinOn.hasFDerivWithinAt_nonneg (hd 0).hasDerivWithinAt hdir
    rw [hzero] at hnonneg
    nlinarith
  have hlocal : IsLocalMin F c := hmin.isLocalMin (Icc_mem_nhds hc0 hcR)
  have hz : deriv A c=ε := by
    have hz := hlocal.deriv_eq_zero
    rw [(hd c).deriv] at hz
    linarith
  have hAc : A c < lo := by
    have hp : 0 ≤ ε*(R-c) := mul_nonneg hε.le (sub_nonneg.2 hc.2)
    dsimp only [F] at hcm
    linarith
  have hineq := hLap c ⟨hc0,hcR⟩ hAc
  rw [hz] at hineq
  have hsecond := radial_local_min_second_nonneg F c hF.continuousAt hlocal
  rw [hdd] at hsecond
  have hp : 0 < B c*ε := mul_pos (hB c ⟨hc0,hcR⟩) hε
  linarith

theorem radial_minimum_principle (R lo : ℝ) (hR : 0 < R) (A : ℝ → ℝ)
    (hA : Differentiable ℝ A) (hzero : deriv A 0=0) (hboundary : lo ≤ A R)
    (hLap : ∀ r ∈ Ioo 0 R, A r < lo →
      deriv (deriv A) r+11/r*deriv A r ≤ 0) :
    ∀ r ∈ Icc 0 R, lo ≤ A r :=
  radial_minimum_principle_drift R lo hR (fun r => 11/r)
    (fun r hr => div_pos (by norm_num) hr.1) A hA hzero hboundary hLap

end DefocusingNLS

end OAI
