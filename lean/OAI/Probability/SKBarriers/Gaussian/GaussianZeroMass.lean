import Mathlib
import OAI.Probability.SKBarriers.Gaussian.BoundedDerivatives
import OAI.Probability.SKBarriers.Calculus.MarginalSecondDerivative
import OAI.Probability.SKBarriers.Hierarchy.HierarchyRegularity

namespace OAI

section
section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
noncomputable section
open MeasureTheory Set Filter
open scoped Topology Interval
noncomputable section
open MeasureTheory Set
open scoped Interval
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped Topology
namespace SK.Analytic
section ZeroMass
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem growth_of_fderiv_bound (f : E → ℝ) (hd : Differentiable ℝ f)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ x, ‖fderiv ℝ f x‖ ≤ C) : HasExpGrowth f := by
  refine ⟨‖f 0‖+C,1,add_nonneg (norm_nonneg _) hC,zero_le_one,?_⟩
  intro x
  rw [one_mul]
  apply (norm_le_of_fderiv_bound f hd C hb x).trans
  have he₀ : 1 ≤ Real.exp ‖x‖ := Real.one_le_exp (norm_nonneg _)
  have he₁ : ‖x‖ ≤ Real.exp ‖x‖ := (le_add_of_nonneg_right zero_le_one).trans (Real.add_one_le_exp _)
  calc
    ‖f 0‖+C*‖x‖ ≤ ‖f 0‖*Real.exp ‖x‖ + C*Real.exp ‖x‖ := by
      gcongr
      exact (le_mul_of_one_le_right (norm_nonneg _) he₀)
    _ = _ := by ring

theorem BoundedDerivs.gaussian_integral {f : E × ℝ → ℝ} (h : BoundedDerivs f) :
    BoundedDerivs (fun x => ∫ y, f (x,y) ∂gaussianReal 0 1) := by
  obtain ⟨hf,C,D,hC,hD,hb,hbb⟩ := h
  have hg := growth_of_fderiv_bound f (hf.differentiable (by norm_num)) hC hb
  have hg₁ := HasExpGrowth.of_bounded hC hb
  have hg₂ := HasExpGrowth.of_bounded hD hbb
  refine ⟨contDiff_two_gaussian_integral_fderiv f hf hg hg₁ hg₂,C,D,hC,hD,?_,?_⟩
  · intro x
    apply (norm_fderiv_gaussian_integral_le f (hf.of_le (by norm_num)) hg hg₁ x).trans
    calc
      _ ≤ ∫ _, C ∂gaussianReal 0 1 := by
        apply integral_mono_of_nonneg (ae_of_all _ (fun y => norm_nonneg _)) (integrable_const _)
        exact ae_of_all _ (fun y => hb (x,y))
      _ = C := by simp
  · intro x
    apply (norm_fderiv_fderiv_gaussian_integral_le f hf hg hg₁ hg₂ x).trans
    calc
      _ ≤ ∫ _, D ∂gaussianReal 0 1 := by
        apply integral_mono_of_nonneg
          (ae_of_all _ (fun y => ContinuousLinearMap.opNorm_nonneg (fderiv ℝ (fderiv ℝ f) (x,y))))
          (integrable_const _)
        exact ae_of_all _ (fun y => hbb (x,y))
      _ = D := by simp

theorem gaussian_integral_convex {f : E × ℝ → ℝ} (hc : ConvexOn ℝ univ f)
    (hf : BoundedDerivs f) : ConvexOn ℝ univ (fun x => ∫ y, f (x,y) ∂gaussianReal 0 1) := by
  obtain ⟨hf,C,D,hC,hD,hb,hbb⟩ := hf
  have hg := growth_of_fderiv_bound f (hf.differentiable (by norm_num)) hC hb
  have hi := hg.integrable_gaussian_section hf.continuous
  refine ⟨convex_univ, ?_⟩
  intro x _ z _ a b ha hb hab
  simp only [smul_eq_mul]
  rw [← integral_const_mul, ← integral_const_mul, ← integral_add ((hi x).const_mul a) ((hi z).const_mul b)]
  apply integral_mono (hi _) (((hi x).const_mul a).add ((hi z).const_mul b))
  intro y
  have hh := hc.2 (mem_univ (x,y)) (mem_univ (z,y)) ha hb hab
  have he : a • (x,y)+b • (z,y) = (a • x+b • z,y) := by
    ext <;> simp only [Prod.smul_fst, Prod.smul_snd, Prod.fst_add, Prod.snd_add, smul_eq_mul]
    rw [← add_mul, hab, one_mul]
  simpa only [he, smul_eq_mul, Pi.add_apply] using hh

def gaussianStep (m : ℝ) (f : E × ℝ → ℝ) (x : E) : ℝ :=
  if m = 0 then ∫ y, f (x,y) ∂gaussianReal 0 1 else positiveGaussianLogStep m f x

def RegularConvex (f : E → ℝ) : Prop := BoundedDerivs f ∧ ConvexOn ℝ univ f

theorem RegularConvex.gaussianStep {f : E × ℝ → ℝ} (hf : RegularConvex f) {m : ℝ} (hm : 0 ≤ m) :
    RegularConvex (gaussianStep m f) := by
  rcases eq_or_lt_of_le hm with he | hm
  · subst m
    have heq : SK.Analytic.gaussianStep 0 f = (fun x => ∫ y, f (x,y) ∂gaussianReal 0 1) := by
      funext x
      simp only [SK.Analytic.gaussianStep, ite_true]
    rw [heq]
    exact ⟨hf.1.gaussian_integral, gaussian_integral_convex hf.2 hf.1⟩
  · have hne := hm.ne'
    have hb := hf.1.positiveGaussianLogStep m
    obtain ⟨hd,C,D,hC,hD,hb₁,hb₂⟩ := hf.1
    have hc := positiveGaussianLogStep_convex hf.2 (hd.differentiable (by norm_num)) C hC hb₁ hm
    have heq : SK.Analytic.gaussianStep m f = positiveGaussianLogStep m f := by
      funext x
      simp only [SK.Analytic.gaussianStep, ite_eq_right_iff.mpr fun he => (hne he).elim]
    rw [heq]
    exact ⟨hb,hc⟩

end ZeroMass
end SK.Analytic

end
end
end
end
end
end

end OAI
