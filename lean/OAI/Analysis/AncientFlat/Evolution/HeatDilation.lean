import OAI.Analysis.AncientFlat.Kernel.ClassicalBase
import OAI.Analysis.AncientFlat.Evolution.DilationCore

namespace OAI
noncomputable section
open Set Filter MeasureTheory
open scoped ZeroAtInfty
namespace BiharmonicKernel
open C0Convolution ParametrixDilation
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
lemma scaleConvolve_dil (k : V → ℂ) (hk : Integrable k) (r s : ℝ) (f : C₀(V,ℂ)) :
    scaleConvolve k r (dil s f)=dil s (scaleConvolve k (Real.exp (-s/4)*r) f) := by
  rw [scaleConvolve,scaleConvolve,← (dil s).integral_comp_comm
    (integrable_scaled_translated k hk (Real.exp (-s/4)*r) f)]
  apply integral_congr_ae
  filter_upwards with y
  rw [map_smul]
  congr 1
  ext x
  simp only [C0Convolution.translate_apply,dil_apply,smul_sub,smul_smul]
lemma evolution_dil (t s : ℝ) (f : C₀(V,ℂ)) :
    evolution t (dil s f)=dil s (evolution (Real.exp (-s)*t) f) := by
  unfold evolution
  rw [scaleConvolve_dil _ (heatKernel (V := V) 1 zero_lt_one).integrable]
  congr 2
  rw [Real.sqrt_mul (Real.exp_pos _).le,
    Real.sqrt_mul (Real.sqrt_nonneg _),←Real.exp_half,←Real.exp_half]
  congr 2
  ring
end BiharmonicKernel

end

end OAI
