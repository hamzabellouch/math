import Mathlib
import OAI.Analysis.BiholderTransport.Regularity.OuterBounds

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace WeakMTWTransport

lemma deriv_eq_of_eqOn_interval {f g : ℝ → ℝ} {a b x : ℝ}
    (hab : a<b) (hx : x∈Icc a b) (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x)
    (he : EqOn f g (Icc a b))  :  deriv f x=deriv g x  :=  by
  exact (uniqueDiffOn_Icc hab x hx).eq_deriv _ hf.hasDerivAt.hasDerivWithinAt
    (hg.hasDerivAt.hasDerivWithinAt.congr (fun y hy=>he hy) (he hx))

lemma outerJ_affine_integral {K M η : ℝ} (hK : 1≤K) (hη : 0<η)  :
    outerJ K M η (1/(128*(K+1)))-outerJ K M η 0=
      M+3-1/(32768*(K+1))  :=  by
  let h : ℝ := 1/(128*(K+1))
  have hh : 0<h := by dsimp only [h]; positivity
  have he :  (∫s in (0 : ℝ)..h,outerW K M η s)=
      ∫s in (0 : ℝ)..h,(128*(M+3)*(K+1)-(K+1)*s)  :=  by
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le hh.le] at hs
    exact outerW_affine hK hη (by linarith [hs.1]) hs.2
  have hd : ∀s : ℝ,HasDerivAt (fun z : ℝ=>128*(M+3)*(K+1)*z-(K+1)*z^2/2)
      (128*(M+3)*(K+1)-(K+1)*s) s := by
    intro s
    convert! ((hasDerivAt_id s).const_mul (128*(M+3)*(K+1))).sub
      ((((hasDerivAt_id s).pow 2).const_mul (K+1)).div_const 2) using 1
    simp only [id_eq]
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _=>hd s)
    ((continuous_const.sub (continuous_const.mul continuous_id)).intervalIntegrable _ _)] at he
  have H := outerJ_add_integral K M η 0 h
  have heq : 128*(M+3)*(K+1)*h-(K+1)*h^2/2-
      (128*(M+3)*(K+1)*(0 : ℝ)-(K+1)*(0 : ℝ)^2/2)=M+3-1/(32768*(K+1)) := by
    dsimp only [h]
    field_simp [show K+1≠0 by linarith]
    ring
  rw [heq] at he
  linarith only [H,he]

lemma outerJ_barrier {K M η : ℝ} (hK : 1≤K) (_ : 2≤M) (hη : 0<η)  :
    outerJ K M η 0+M+1 < outerJ K M η (1/(128*(K+1)))  :=  by
  have H := outerJ_affine_integral hK hη (M := M)
  have hh : 1/(32768*(K+1)) < (1 : ℝ)  :=  by
    apply (div_lt_iff₀ (by positivity  :  0<32768*(K+1))).mpr
    linarith
  linarith only [H,hh]

lemma outerProfile_forces_affine {K M η s : ℝ} (hK : 1≤K) (hM : 2≤M) (hη : 0<η)
    (hs : s≤1-η) (hcap : outerProfile K M η s≤M)  :  s<1/(128*(K+1))  :=  by
  rw [outerProfile_left hη hs] at hcap
  by_contra hh
  have HM := (outerJ_monotone hK hM hη) (le_of_not_gt hh)
  have HB := outerJ_barrier hK hM hη
  rw [outerJ_zero] at HB
  linarith only [hcap,HM,HB]

lemma outerProfile_derivatives_left {K M η s : ℝ} (hη : 0<η) (hs : s≤1-η)  :
    deriv (outerProfile K M η) s=outerW K M η s ∧
    iteratedDeriv 2 (outerProfile K M η) s=deriv (outerW K M η) s  :=  by
  have hd : ∀x∈Iic (1-η),deriv (outerProfile K M η) x=deriv (outerJ K M η) x := by
    intro x hx
    exact (uniqueDiffOn_Iic (1-η) x hx).eq_deriv _
      (((outerProfile_contDiff K M η).differentiable (by simp) x).hasDerivAt.hasDerivWithinAt)
      ((((outerJ_contDiff K M η).differentiable (by simp) x).hasDerivAt.hasDerivWithinAt).congr
        (fun y hy=>outerProfile_left hη hy) (outerProfile_left hη hx))
  have hdiff : deriv (outerJ K M η)=outerW K M η := funext (fun x=>(outerJ_hasDerivAt K M η x).deriv)
  constructor
  · rw [hd s hs,hdiff]
  · simp only [iteratedDeriv_succ,iteratedDeriv_zero]
    exact (uniqueDiffOn_Iic (1-η) s hs).eq_deriv _
      ((((contDiff_infty_iff_deriv.mp (outerProfile_contDiff K M η)).2).differentiable (by simp) s).hasDerivAt.hasDerivWithinAt)
      ((((outerW_contDiff K M η).differentiable (by simp) s).hasDerivAt.hasDerivWithinAt).congr
        (fun y hy=>by rw [hd y hy,hdiff]) (by rw [hd s hs,hdiff]))

lemma outerProfile_curvature {K M η s : ℝ} (hK : 1≤K) (hM : 2≤M) (hη : 0<η)
    (hs : -2 * η ≤ s) (hs' : s ≤ 1 - η) (hcap : outerProfile K M η s≤M)  :
    0<deriv (outerProfile K M η) s ∧ iteratedDeriv 2 (outerProfile K M η) s≤ -K  :=  by
  have hhi := outerProfile_forces_affine hK hM hη hs' hcap
  have hab : -2*η<1/(128*(K+1)) := by
    have hp : 0<1/(128*(K+1)) := by positivity
    linarith
  have hder := deriv_eq_of_eqOn_interval hab ⟨hs,hhi.le⟩
    ((outerW_contDiff K M η).differentiable (by simp) s)
    ((((hasDerivAt_id s).const_mul (K+1)).const_sub (128*(M+3)*(K+1))).differentiableAt)
    (fun y hy=>outerW_affine hK hη hy.1 hy.2)
  have hf : deriv (fun x : ℝ=>128*(M+3)*(K+1)-(K+1)*x) s= -(K+1) := by
    simp
  simp only [id_eq] at hder
  rw [hf] at hder
  obtain ⟨H1,H2⟩ := outerProfile_derivatives_left hη hs'
  rw [H1,H2,outerW_affine hK hη hs hhi.le,hder]
  have hh : 1/(128*(K+1)) < 128*(M+3) := by
    apply (div_lt_iff₀ (by positivity  :  0<128*(K+1))).mpr
    nlinarith
  constructor <;> nlinarith
end WeakMTWTransport

end

end OAI
