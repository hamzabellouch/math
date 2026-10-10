import Mathlib
import OAI.Probability.SKBarriers.Gaussian.FiberGaussianStein

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
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped Topology NNReal
namespace SK.Analytic
section GrowthOps
variable {E F : Type} [NormedAddCommGroup E] [NormedAddCommGroup F]

theorem HasExpGrowth.add {f g : E → F} (hf : HasExpGrowth f) (hg : HasExpGrowth g) :
    HasExpGrowth (fun z => f z+g z) := by
  obtain ⟨C,M,hC,hM,hf⟩ := hf
  obtain ⟨D,N,hD,hN,hg⟩ := hg
  refine ⟨C+D,M+N,add_nonneg hC hD,add_nonneg hM hN,fun z => ?_⟩
  calc
    ‖f z+g z‖ ≤ ‖f z‖+‖g z‖ := norm_add_le _ _
    _ ≤ C*Real.exp (M*‖z‖)+D*Real.exp (N*‖z‖) := add_le_add (hf z) (hg z)
    _ ≤ C*Real.exp ((M+N)*‖z‖)+D*Real.exp ((M+N)*‖z‖) :=
      add_le_add (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hN) (norm_nonneg z))) hC)
        (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hM) (norm_nonneg z))) hD)
    _ = _ := by ring

variable [NormedSpace ℝ F]
theorem HasExpGrowth.smul {f : E → ℝ} {g : E → F}
    (hf : HasExpGrowth f) (hg : HasExpGrowth g) : HasExpGrowth (fun z => f z • g z) := by
  obtain ⟨C,M,hC,hM,hf⟩ := hf
  obtain ⟨D,N,hD,hN,hg⟩ := hg
  refine ⟨C*D,M+N,mul_nonneg hC hD,add_nonneg hM hN,fun z => ?_⟩
  rw [norm_smul]
  calc
    ‖f z‖*‖g z‖ ≤ (C*Real.exp (M*‖z‖))*(D*Real.exp (N*‖z‖)) :=
      mul_le_mul (hf z) (hg z) (norm_nonneg _) (mul_nonneg hC (Real.exp_pos _).le)
    _ = _ := by rw [add_mul,Real.exp_add]; ring
end GrowthOps

theorem fiberGaussian_tilted_weighted_stein (n : ℕ) (V g : ParameterSpace n → ℝ)
    (hV : BoundedDerivs V) (hg : ContDiff ℝ 1 g)
    (hgg : HasExpGrowth g) (hgg' : HasExpGrowth (fderiv ℝ g)) (x : ℝ) (i : Fin n) :
    (∫ z, coordinateProjection n i z*g z ∂(fiberGaussian n x).tilted V) =
      (∫ z, fderiv ℝ g z (coordinateAxis n i) ∂(fiberGaussian n x).tilted V) +
      ∫ z, g z*fderiv ℝ V z (coordinateAxis n i) ∂(fiberGaussian n x).tilted V := by
  have he := (hV.1.exp).of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)
  have hge : HasExpGrowth (fun z => Real.exp (V z)) := by
    simpa only [one_mul] using (hV.exp_growths 1).1
  have hge' : HasExpGrowth (fderiv ℝ (fun z => Real.exp (V z))) := by
    simpa only [one_mul] using (hV.exp_growths 1).2.1
  have hde (z) : fderiv ℝ (fun z => g z*Real.exp (V z)) z =
      g z • fderiv ℝ (fun z => Real.exp (V z)) z +
      Real.exp (V z) • fderiv ℝ g z := by
    exact fderiv_mul (hg.differentiable (by norm_num) z) (he.differentiable (by norm_num) z)
  have hprod : HasExpGrowth (fderiv ℝ (fun z => g z*Real.exp (V z))) := by
    have heq := funext hde
    rw [heq]
    exact (hgg.smul hge').add (hge.smul hgg')
  have H := fiberGaussian_stein n _ (hg.mul he) (hgg.mul hge) hprod x i
  have hdV : HasExpGrowth (fderiv ℝ V) := by
    obtain ⟨_,C,D,hC,hD,hb,hbb⟩ := hV
    exact HasExpGrowth.of_bounded hC hb
  have i₁ : Integrable (fun z => fderiv ℝ g z (coordinateAxis n i)*Real.exp (V z))
      (fiberGaussian n x) :=
    ((hgg'.derivative_eval _).mul hge).integrable_fiberGaussian n
      (((hg.continuous_fderiv (by norm_num)).clm_apply continuous_const).mul he.continuous) x
  have i₂ : Integrable (fun z => g z*fderiv ℝ V z (coordinateAxis n i)*Real.exp (V z))
      (fiberGaussian n x) :=
    ((hgg.mul (hdV.derivative_eval _)).mul hge).integrable_fiberGaussian n
      ((hg.continuous.mul ((hV.1.continuous_fderiv (by norm_num)).clm_apply continuous_const)).mul
        he.continuous) x
  simp only [integral_tilted_real_eq_div]
  rw [← add_div]
  congr 1
  rw [← integral_add i₁ i₂]
  calc
    (∫ z, coordinateProjection n i z*g z*Real.exp (V z) ∂fiberGaussian n x) =
        ∫ z, coordinateProjection n i z*(g z*Real.exp (V z)) ∂fiberGaussian n x := by
      congr 1; funext z; ring
    _ = _ := H
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with z
      rw [hde,((hV.1.differentiable (by norm_num) z).hasFDerivAt.exp).fderiv]
      simp only [add_apply,smul_apply,smul_eq_mul]
      ring
end SK.Analytic

end
end
end
end
end
end
end

end OAI
