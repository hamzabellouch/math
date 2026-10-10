import OAI.Analysis.FreeEntropy.RandomHeatConvergence

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
namespace FiniteEntropySeparation
variable {n d : ℕ}
 def matrixHeatLaw (μ : Measure (MatrixCoordinates n d)) (s : ℝ) : Measure (MatrixCoordinates n d) :=
    volume.withDensity (fun x => ENNReal.ofReal (smoothedDensity μ (s/d) x))
 theorem matrixHeatLaw_eq (hd : 0<d) (μ : Measure (MatrixCoordinates n d)) [IsFiniteMeasure μ]
    {s : ℝ} (hs : 0<s) :
    matrixHeatLaw μ s = (μ.prod (productGaussian (MatrixIndex n d))).map (fun z => heatCoordinates z.1 s z.2) := by
  have hsd : 0<s/(d:ℝ) := div_pos hs (by exact_mod_cast hd)
  rw [matrixHeatLaw,← smoothedLaw_eq μ hsd,normalLaw_eq_scaled hsd]
  have he : μ.prod ((productGaussian (MatrixIndex n d)).map (fun x => Real.sqrt (s/d) • WithLp.toLp 2 x)) =
      (μ.prod (productGaussian (MatrixIndex n d))).map (Prod.map id (fun x => Real.sqrt (s/d) • WithLp.toLp 2 x)) := by
    convert Measure.map_prod_map μ (productGaussian (MatrixIndex n d)) measurable_id
      (show Measurable (fun x : MatrixIndex n d → ℝ => Real.sqrt (s/d) • WithLp.toLp 2 x) from
        (show Continuous (WithLp.toLp 2 : (MatrixIndex n d → ℝ) → MatrixCoordinates n d) from PiLp.continuous_toLp 2 _).measurable.const_smul (Real.sqrt (s/d))) using 1
    rw [Measure.map_id]
  rw [he,Measure.map_map (show Measurable (fun z : MatrixCoordinates n d × MatrixCoordinates n d => z.1+z.2) from by fun_prop)
    (show Measurable (Prod.map id (fun x : MatrixIndex n d → ℝ => Real.sqrt (s/d) • WithLp.toLp 2 x)) from
      measurable_id.prodMap ((show Continuous (WithLp.toLp 2 : (MatrixIndex n d → ℝ) → MatrixCoordinates n d) from PiLp.continuous_toLp 2 _).measurable.const_smul (Real.sqrt (s/d))))]
  congr 1
  funext z
  simp only [Function.comp_apply,Prod.map_fst,Prod.map_snd,id_eq,heatCoordinates,Real.sqrt_div hs.le]
 theorem matrixHeatLaw_probability (hd : 0<d) (μ : Measure (MatrixCoordinates n d)) [IsProbabilityMeasure μ]
    {s : ℝ} (hs : 0<s) : IsProbabilityMeasure (matrixHeatLaw μ s) := by
  rw [matrixHeatLaw_eq hd μ hs]
  infer_instance
 theorem integral_matrixHeatLaw (μ : Measure (MatrixCoordinates n d)) [IsFiniteMeasure μ]
    {s : ℝ} (hs : 0<s) (hd : 0<d) (f : MatrixCoordinates n d → ℝ) :
    (∫x,f x ∂matrixHeatLaw μ s) = ∫x,smoothedDensity μ (s/d) x*f x := by
  have hp : ∀x,0 ≤ smoothedDensity μ (s/d) x := fun x => integral_nonneg (fun y => (normalKernel_pos _ _).le)
  rw [matrixHeatLaw,integral_withDensity_eq_integral_toReal_smul]
  · simp only [ENNReal.toReal_ofReal (hp _),smul_eq_mul]
  · exact ENNReal.measurable_ofReal.comp (smoothedDensity_continuous μ (div_pos hs (by exact_mod_cast hd))).measurable
  · exact ae_of_all _ (fun _ => ENNReal.ofReal_lt_top)
end FiniteEntropySeparation

end

end OAI
