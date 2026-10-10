import Mathlib
import OAI.Probability.SKBarriers.Gaussian.FiberGaussian

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
section GaussianGrowth
variable {E F : Type} [NormedAddCommGroup E] [NormedAddCommGroup F]

theorem HasExpGrowth.mul {f g : E → ℝ} (hf : HasExpGrowth f) (hg : HasExpGrowth g) :
    HasExpGrowth (fun x => f x*g x) := by
  obtain ⟨C,M,hC,hM,hf⟩ := hf
  obtain ⟨D,N,hD,hN,hg⟩ := hg
  refine ⟨C*D,M+N,mul_nonneg hC hD,add_nonneg hM hN,?_⟩
  intro x
  rw [norm_mul]
  calc
    _ ≤ (C*Real.exp (M*‖x‖))*(D*Real.exp (N*‖x‖)) :=
      mul_le_mul (hf x) (hg x) (norm_nonneg _) (by positivity)
    _ = _ := by rw [add_mul,Real.exp_add]; ring

theorem HasExpGrowth.norm_id : HasExpGrowth (fun x : E => ‖x‖) := by
  refine ⟨1,1,zero_le_one,zero_le_one,?_⟩
  intro x
  simp only [Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _),one_mul]
  exact le_trans (by linarith) (Real.add_one_le_exp ‖x‖)

theorem HasExpGrowth.section_right {f : E × ℝ → F} (hf : HasExpGrowth f) (y : ℝ) :
    HasExpGrowth (fun x => f (x,y)) := by
  obtain ⟨C,M,hC,hM,hf⟩ := hf
  refine ⟨C*Real.exp (M*|y|),M,by positivity,hM,?_⟩
  intro x
  apply (hf (x,y)).trans
  rw [mul_assoc,← Real.exp_add,← mul_add]
  apply mul_le_mul_of_nonneg_left _ hC
  apply Real.exp_le_exp.mpr
  apply mul_le_mul_of_nonneg_left _ hM
  rw [Prod.norm_def,Real.norm_eq_abs]
  exact max_le (le_add_of_nonneg_left (abs_nonneg y))
    (le_add_of_nonneg_right (norm_nonneg x))

theorem HasExpGrowth.integrable_gaussianMeasure [NormedSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {μ : Measure E} [IsGaussian μ] {f : E → F}
    (hf : HasExpGrowth f) (hc : Continuous f) : Integrable f μ := by
  obtain ⟨C,M,hC,hM,hf⟩ := hf
  obtain ⟨a,ha,hi⟩ := IsGaussian.exists_integrable_exp_sq μ
  apply (hi.const_mul (C*Real.exp (M^2/a))).mono' hc.aestronglyMeasurable
  filter_upwards [] with x
  apply (hf x).trans
  rw [mul_assoc,← Real.exp_add]
  apply mul_le_mul_of_nonneg_left _ hC
  apply Real.exp_le_exp.mpr
  have he : (M^2/a)*a = M^2 := div_mul_cancel₀ _ ha.ne'
  have hs := sq_nonneg (a*‖x‖-M/2)
  nlinarith [sq_nonneg M]

end GaussianGrowth

instance fiberGaussian_isGaussian : (n : ℕ) → (x : ℝ) → IsGaussian (fiberGaussian n x)
  | 0, x => inferInstanceAs (IsGaussian (Measure.dirac x))
  | n+1, x => by
      let := fiberGaussian_isGaussian n x
      exact inferInstanceAs (IsGaussian ((fiberGaussian n x).prod (gaussianReal 0 1)))

theorem HasExpGrowth.integrable_fiberGaussian {F : Type} [NormedAddCommGroup F]
    (n : ℕ) {f : ParameterSpace n → F} (hg : HasExpGrowth f) (hf : Continuous f) (x : ℝ) :
    Integrable f (fiberGaussian n x) := hg.integrable_gaussianMeasure hf

def coordinateAxis : (n : ℕ) → Fin n → ParameterSpace n
  | 0, i => Fin.elim0 i
  | n+1, i => Fin.lastCases (0,1) (fun j => (coordinateAxis n j,0)) i

@[simp] theorem coordinateAxis_last (n : ℕ) : coordinateAxis (n+1) (Fin.last n) = (0,1) := by
  simp [coordinateAxis]

@[simp] theorem coordinateAxis_castSucc (n : ℕ) (i : Fin n) :
    coordinateAxis (n+1) i.castSucc = (coordinateAxis n i,0) := by simp [coordinateAxis]

section LinearGrowth
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem HasExpGrowth.linear (L : E →L[ℝ] ℝ) : HasExpGrowth L := by
  apply (HasExpGrowth.norm_id (E := E)).congr_bound (norm_nonneg L)
  intro x
  simpa only [Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _)] using L.le_opNorm x

theorem HasExpGrowth.derivative_eval {f : E → ℝ} (h : HasExpGrowth (fderiv ℝ f)) (u : E) :
    HasExpGrowth (fun x => fderiv ℝ f x u) := h.clm (ContinuousLinearMap.apply ℝ ℝ u)

end LinearGrowth
end SK.Analytic
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped Topology NNReal

end
end
end
end
end
end
end

end OAI
