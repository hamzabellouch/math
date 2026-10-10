import Mathlib
import OAI.Probability.SKBarriers.Scalar.ScalarHierarchy
import OAI.Probability.SKBarriers.Gaussian.GaussianMassStability
import OAI.Probability.SKBarriers.Scalar.DslopeLipschitz

namespace OAI

section

noncomputable section
open scoped Topology NNReal
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic
section Gaussian
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem gaussianStep_mass_lipschitz {f : E × ℝ → ℝ} (hf : BoundedDerivs f)
    (x : E) {v B : ℝ} (hv : 0 ≤ v) (hvB : v ≤ B)
    (hfv : ∀ y, |f (x,y)-f (x,0)| ≤ v * |y|)
    {a b : ℝ} (ha : a ∈ Icc (0:ℝ) 1) (hb : b ∈ Icc (0:ℝ) 1) :
    |gaussianStep b f x-gaussianStep a f x| ≤ gaussianMassBound B*v^2 * |b-a| := by
  have han (m : ℝ) : AnalyticAt ℝ (cgf (fun y => f (x,y)) (gaussianReal 0 1)) m :=
    analyticAt_cgf (hf.mem_interior_integrableExpSet_section x m)
  have hvar (m : ℝ) (hm : m ∈ Icc (0:ℝ) 1) :
      |iteratedDeriv 2 (cgf (fun y => f (x,y)) (gaussianReal 0 1)) m| ≤ gaussianMassBound B*v^2 := by
    rw [← variance_tilted_mul (hf.mem_interior_integrableExpSet_section x m),abs_of_nonneg (variance_nonneg _ _)]
    exact gaussianStepLaw_variance_bound hf x hv hvB (by rw [abs_of_nonneg hm.1]; exact hm.2) hfv
  have H := dslope_mass_lipschitz han (mul_nonneg (gaussianMassBound_pos B).le (sq_nonneg v)) hvar ha hb
  rw [← gaussianStep_mass_eq_dslope hf x] at H
  exact H

theorem boundedDerivs_constant (c : ℝ) : BoundedDerivs (fun _ : E => c) := by
  refine ⟨contDiff_const,0,0,le_rfl,le_rfl,?_,?_⟩
  · intro x; simp
  · intro x
    have h : fderiv ℝ (fun _ : E => c) = fun _ => (0 : E →L[ℝ] ℝ) := by
      funext y; exact fderiv_const_apply c
    simp only [h, fderiv_const_apply, ContinuousLinearMap.opNorm_zero, le_refl]

theorem gaussianStep_mono {f g : E × ℝ → ℝ} (hf : BoundedDerivs f) (hg : BoundedDerivs g)
    {m : ℝ} (hm : 0 ≤ m) (hfg : ∀ z, f z ≤ g z) (x : E) :
    gaussianStep m f x ≤ gaussianStep m g x := by
  by_cases hm0 : m=0
  · simp only [gaussianStep,hm0,ite_true]
    exact integral_mono (hf.hasExpGrowth.integrable_gaussian_section hf.1.continuous x)
      (hg.hasExpGrowth.integrable_gaussian_section hg.1.continuous x) (fun y => hfg (x,y))
  · simp only [gaussianStep,ite_eq_right hm0,positiveGaussianLogStep]
    apply div_le_div_of_nonneg_right _ hm
    apply Real.log_le_log (integral_exp_pos (hf.exp_integrable m x))
    exact integral_mono (hf.exp_integrable m x) (hg.exp_integrable m x)
      (fun y => Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hfg (x,y)) hm))

theorem gaussianStep_uniform_nonexpansive {f g : E × ℝ → ℝ} (hf : BoundedDerivs f) (hg : BoundedDerivs g)
    {m ε : ℝ} (hm : 0 ≤ m) (hfg : ∀ z, |f z-g z| ≤ ε) (x : E) :
    |gaussianStep m f x-gaussianStep m g x| ≤ ε := by
  have hg' : BoundedDerivs (fun z => g z+ε) := hg.add (boundedDerivs_constant ε)
  have hf' : BoundedDerivs (fun z => f z+ε) := hf.add (boundedDerivs_constant ε)
  have H₁ := gaussianStep_mono hf hg' hm (fun z => by linarith [(abs_le.mp (hfg z)).2]) x
  have H₂ := gaussianStep_mono hg hf' hm (fun z => by linarith [(abs_le.mp (hfg z)).1]) x
  have he₁ := congrFun (gaussianStep_add_prefix hg (fun _ => ε) m) x
  have he₂ := congrFun (gaussianStep_add_prefix hf (fun _ => ε) m) x
  rw [he₁] at H₁
  rw [he₂] at H₂
  exact abs_le.mpr ⟨by linarith,by linarith⟩
end Gaussian

theorem scalarStep_mass_lipschitz {f : ℝ → ℝ} (hf : BoundedDerivs f)
    (hLip : LipschitzWith 1 f) {v B : ℝ} (hvB : |v| ≤ B)
    {a b : ℝ} (ha : a ∈ Icc (0:ℝ) 1) (hb : b ∈ Icc (0:ℝ) 1) (x : ℝ) :
    |scalarStep b v f x-scalarStep a v f x| ≤ gaussianMassBound B*v^2 * |b-a| := by
  let L : (ℝ × ℝ) →L[ℝ] ℝ := ContinuousLinearMap.fst ℝ ℝ ℝ+v • ContinuousLinearMap.snd ℝ ℝ ℝ
  have hbnd (y : ℝ) : |f (x+v*y)-f (x+v*0)| ≤ |v| * |y| := by
    have H := hLip.norm_sub_le (x+v*y) (x+v*0)
    simpa only [NNReal.coe_one,one_mul,Real.norm_eq_abs,mul_zero,add_zero,add_sub_cancel_left,abs_mul] using H
  have H := gaussianStep_mass_lipschitz (hf.compCLM L) x (abs_nonneg v) hvB hbnd ha hb
  change |scalarStep b v f x-scalarStep a v f x| ≤ gaussianMassBound B*|v|^2 * |b-a| at H
  simpa only [sq_abs] using H

theorem scalarStep_uniform_nonexpansive {f g : ℝ → ℝ} (hf : BoundedDerivs f) (hg : BoundedDerivs g)
    {m ε : ℝ} (hm : 0 ≤ m) (hfg : ∀ z, |f z-g z| ≤ ε) (v x : ℝ) :
    |scalarStep m v f x-scalarStep m v g x| ≤ ε := by
  let L : (ℝ × ℝ) →L[ℝ] ℝ := ContinuousLinearMap.fst ℝ ℝ ℝ+v • ContinuousLinearMap.snd ℝ ℝ ℝ
  exact gaussianStep_uniform_nonexpansive (hf.compCLM L) (hg.compCLM L) hm (fun z => hfg (L z)) x

end SK.Analytic

end
end

end OAI
