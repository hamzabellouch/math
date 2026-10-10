import Mathlib
import OAI.Probability.SKBarriers.Gaussian.GaussianMassDerivative

namespace OAI

section

noncomputable section
open scoped Topology
open Set
namespace SK.Analytic

theorem dslope_deriv_bound {f : ℝ → ℝ} (hf : ∀ x, AnalyticAt ℝ f x)
    {K : ℝ} (hK : 0 ≤ K) (hb : ∀ x ∈ Icc (0:ℝ) 1, |iteratedDeriv 2 f x| ≤ K)
    {a : ℝ} (ha : a ∈ Icc (0:ℝ) 1) :
    DifferentiableAt ℝ (dslope f 0) a ∧ |deriv (dslope f 0) a| ≤ K := by
  by_cases ha0 : a = 0
  · subst a
    have H := hasDerivAt_dslope_zero_of_analytic (hf 0)
    refine ⟨H.differentiableAt,?_⟩
    rw [H.deriv,abs_div,abs_of_pos (by norm_num : (0:ℝ)<2)]
    have H0 := hb 0 (by constructor <;> norm_num)
    linarith
  · have ha' : 0 < a := lt_of_le_of_ne ha.1 (Ne.symm ha0)
    have hfd : Differentiable ℝ f := fun x => (hf x).differentiableAt
    obtain ⟨r,hr,hrf⟩ := exists_deriv_eq_slope f ha' hfd.continuous.continuousOn hfd.differentiableOn
    have hdd : Differentiable ℝ (deriv f) := fun x => (hf x).deriv.differentiableAt
    have hLip := (convex_Icc (0:ℝ) 1).norm_image_sub_le_of_norm_deriv_le
      (fun x _ => hdd x) (fun x hx => by
        simpa only [iteratedDeriv_succ,iteratedDeriv_one,iteratedDeriv_zero,Real.norm_eq_abs] using hb x hx)
      (show r ∈ Icc (0:ℝ) 1 from ⟨hr.1.le,hr.2.le.trans ha.2⟩) ha
    have H := ((hfd a).hasDerivAt.sub_const (f 0)).div (hasDerivAt_id a) ha0
    have he : dslope f 0 =ᶠ[𝓝 a] (fun t => (f t-f 0)/t) := by
      filter_upwards [eventually_ne_nhds ha0] with t ht
      simp only [dslope_of_ne _ ht,slope_def_field,sub_zero]
    have H' := H.congr_of_eventuallyEq he
    refine ⟨H'.differentiableAt,?_⟩
    rw [H'.deriv]
    simp only [id_eq]
    have heq : (deriv f a*a-(f a-f 0)*1)/a^2 = (deriv f a-deriv f r)/a := by
      rw [hrf,sub_zero]
      field_simp
    rw [heq,abs_div,abs_of_pos ha']
    rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_of_pos (sub_pos.mpr hr.2)] at hLip
    apply (div_le_iff₀ ha').mpr
    exact hLip.trans (mul_le_mul_of_nonneg_left (by linarith [hr.1]) hK)

theorem dslope_mass_lipschitz {f : ℝ → ℝ} (hf : ∀ x, AnalyticAt ℝ f x)
    {K : ℝ} (hK : 0 ≤ K) (hb : ∀ x ∈ Icc (0:ℝ) 1, |iteratedDeriv 2 f x| ≤ K)
    {a b : ℝ} (ha : a ∈ Icc (0:ℝ) 1) (hb' : b ∈ Icc (0:ℝ) 1) :
    |dslope f 0 b-dslope f 0 a| ≤ K*|b-a| := by
  have H := (convex_Icc (0:ℝ) 1).norm_image_sub_le_of_norm_deriv_le
    (fun x hx => (dslope_deriv_bound hf hK hb hx).1)
    (fun x hx => by simpa only [Real.norm_eq_abs] using (dslope_deriv_bound hf hK hb hx).2) ha hb'
  simpa only [Real.norm_eq_abs] using H

end SK.Analytic

end
end

end OAI
