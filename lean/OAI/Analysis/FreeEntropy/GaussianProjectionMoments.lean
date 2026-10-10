import OAI.Analysis.FreeEntropy.BlockEvent

namespace OAI

universe u1

noncomputable section
open MeasureTheory ProbabilityTheory Finset
namespace FiniteEntropySeparation
variable {ι : Type u1} [Fintype ι] [DecidableEq ι]
 theorem productGaussian_coordinate_second {ι : Type u1} [Fintype ι] [DecidableEq ι] (i : ι) :
    (∫x : ι → ℝ,x i^2 ∂productGaussian ι)=1 := by
  have hm := measurePreserving_eval (fun _ : ι => gaussianReal 0 1) i
  have he := integral_map hm.measurable.aemeasurable
    (show AEStronglyMeasurable (fun x : ℝ => x^2) (Measure.map (Function.eval i) (productGaussian ι)) from (continuous_id.pow 2).aestronglyMeasurable)
  change (∫y : ℝ,y^2 ∂Measure.map (Function.eval i) (Measure.pi (fun _ : ι => gaussianReal 0 1)))=_ at he
  rw [hm.map_eq,gaussian_square_integral] at he
  exact he.symm
 theorem normalLaw_coordinateMask_integrable {s : ℝ} (hs : 0<s) (m : Finset ι) :
    Integrable (fun x => ‖coordinateMask m x‖^2) (normalLaw s) := by
  rw [normalLaw_eq_scaled hs]
  apply (integrable_map_measure (((coordinateMask_continuous m).norm.pow 2).aestronglyMeasurable) (by fun_prop : AEMeasurable (fun x : ι → ℝ => Real.sqrt s • WithLp.toLp 2 x) _)).mpr
  change Integrable (fun x : ι → ℝ => ‖coordinateMask m (Real.sqrt s • WithLp.toLp 2 x)‖^2) (productGaussian ι)
  simp only [coordinateMask_sq,PiLp.smul_apply,smul_eq_mul,mul_pow,Real.sq_sqrt hs.le,← mul_sum]
  exact (integrable_finsetSum _ (fun i _ => ((IsRealPolynomial.coord i).pow 2).integrable)).const_mul s
 theorem normalLaw_coordinateMask_integral {s : ℝ} (hs : 0<s) (m : Finset ι) :
    (∫x,‖coordinateMask m x‖^2 ∂normalLaw s)=s*m.card := by
  rw [normalLaw_eq_scaled hs]
  have hm : AEStronglyMeasurable (fun x : EuclideanSpace ℝ ι => ‖coordinateMask m x‖^2) (Measure.map (fun x : ι → ℝ => Real.sqrt s • WithLp.toLp 2 x) (productGaussian ι)) := ((coordinateMask_continuous m).norm.pow 2).aestronglyMeasurable
  rw [integral_map (by fun_prop) hm]
  simp only [coordinateMask_sq,PiLp.smul_apply,smul_eq_mul,mul_pow,Real.sq_sqrt hs.le,← mul_sum]
  rw [integral_const_mul,integral_finsetSum _ (fun i _ => ((IsRealPolynomial.coord i).pow 2).integrable)]
  simp only [productGaussian_coordinate_second,sum_const,mul_one,nsmul_eq_mul]
 theorem normalLaw_coordinateMask_markov {s r : ℝ} (hs : 0<s) (hr : 0<r) (m : Finset ι) :
    (normalLaw s) {x | r≤‖coordinateMask m x‖} ≤ ENNReal.ofReal (s*m.card/r^2) := by
  have hz : 0<r^2 := sq_pos_of_pos hr
  let F : EuclideanSpace ℝ ι → ℝ := fun x => ‖coordinateMask m x‖^2/r^2
  have hF := (normalLaw_coordinateMask_integrable hs m).div_const (r^2)
  have hh := hF.measure_le_integral (ae_of_all _ (fun x => div_nonneg (sq_nonneg _) hz.le))
    (s := {x | r≤‖coordinateMask m x‖}) (fun x hx => by
      dsimp at hx
      rw [le_div_iff₀ hz,one_mul]
      exact pow_le_pow_left₀ hr.le hx 2)
  simpa only [integral_div,normalLaw_coordinateMask_integral hs m] using hh
end FiniteEntropySeparation

end

end OAI
