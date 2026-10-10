import Mathlib
import OAI.Probability.SKBarriers.Gaussian.GaussianDomination

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
section TwiceDifferentiable
variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

omit [CompleteSpace F] in
theorem contDiff_two_gaussian_integral (f : E × ℝ → F)
    (f₁ : E × ℝ → E →L[ℝ] F) (f₂ : E × ℝ → E →L[ℝ] E →L[ℝ] F)
    (hf : Continuous f) (hf₁ : Continuous f₁) (hf₂ : Continuous f₂)
    (hg : HasExpGrowth f) (hg₁ : HasExpGrowth f₁) (hg₂ : HasExpGrowth f₂)
    (hd : ∀ x y, HasFDerivAt (fun z => f (z,y)) (f₁ (x,y)) x)
    (hd₁ : ∀ x y, HasFDerivAt (fun z => f₁ (z,y)) (f₂ (x,y)) x) :
    ContDiff ℝ 2 (fun x => ∫ y, f (x,y) ∂gaussianReal 0 1) := by
  have hc₁ : ContDiff ℝ 1 (fun x => ∫ y, f₁ (x,y) ∂gaussianReal 0 1) := by
    apply (contDiff_succ_iff_hasFDerivAt (n := 0)).mpr
    refine ⟨fun x => ∫ y, f₂ (x,y) ∂gaussianReal 0 1, ?_, ?_⟩
    · exact contDiff_zero.mpr (hg₂.continuous_gaussian_integral hf₂)
    · exact hasFDerivAt_gaussian_integral f₁ f₂ hf₁ hf₂ hg₁ hg₂ hd₁
  apply (contDiff_succ_iff_hasFDerivAt (n := 1)).mpr
  exact ⟨_, hc₁, hasFDerivAt_gaussian_integral f f₁ hf hf₁ hg hg₁ hd⟩

end TwiceDifferentiable

section GrowthAlgebra
variable {E F G : Type} [Norm E] [Norm F] [Norm G]

theorem HasExpGrowth.congr_bound {f : E → F} (hf : HasExpGrowth f)
    {g : E → G} {K : ℝ} (hK : 0 ≤ K) (hg : ∀ z, ‖g z‖ ≤ K*‖f z‖) : HasExpGrowth g := by
  obtain ⟨C,M,hC,hM,hf⟩ := hf
  refine ⟨K*C,M,mul_nonneg hK hC,hM,?_⟩
  intro z
  exact (hg z).trans ((mul_le_mul_of_nonneg_left (hf z) hK).trans_eq (mul_assoc _ _ _).symm)

theorem HasExpGrowth.of_bounded {f : E → F} {C : ℝ} (hC : 0 ≤ C)
    (hf : ∀ z, ‖f z‖ ≤ C) : HasExpGrowth f := by
  refine ⟨C,0,hC,le_rfl,?_⟩
  simpa only [zero_mul, Real.exp_zero, mul_one] using hf

theorem HasExpGrowth.norm {f : E → F} (hf : HasExpGrowth f) (hn : ∀ x, 0 ≤ ‖f x‖) :
    HasExpGrowth (fun x => ‖f x‖) := by
  obtain ⟨C,M,hC,hM,hf⟩ := hf
  refine ⟨C,M,hC,hM,?_⟩
  intro x
  simpa only [Real.norm_eq_abs, abs_of_nonneg (hn x)] using hf x

end GrowthAlgebra
end SK.Analytic

end
end
end
end
end
end

end OAI
