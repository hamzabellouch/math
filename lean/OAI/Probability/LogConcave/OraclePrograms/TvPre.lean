import Mathlib
import OAI.Probability.LogConcave.OraclePrograms.FullTape
import OAI.Probability.LogConcave.Sampling.ProdMapEventReal

namespace OAI

section
noncomputable section
namespace LogConcaveSampling.OracleCompiler
open MeasureTheory ProbabilityTheory Coupling Function
open scoped Classical NNReal

variable {d : ℕ}

lemma ReservedProgram.tv_of_pre {F : Point d → ℝ} {lam : ℝ≥0} (hF : Primitive F lam)
    (S : ReservedProgram d) (x : Point d) {r η e : ℝ}
    (hr : 0≤r) (hl : (lam:ℝ)*r^2<1) (hη : 0<η) (he : 0≤e)
    (hres : S.reserve=η/2)
    (hpre : SquaredAt (gaussianTape d S.slots)
      ((gibbs (primitivePotential F x r)).prod (stdGaussian (Point d)))
      (fun g => S.pre.run F (x,g)) (fun z => z.1+(Real.sqrt 3*η/2) • z.2)
      (e^2*(circuitD F x)^2)) :
    TVAtMost ((gaussianTape d S.full.slots).map (fun g => S.full.program.run F (x,g)))
      (((gibbs (primitivePotential F x r)).prod (stdGaussian (Point d))).map
        (fun z => z.1+η • z.2)) (2*e*circuitD F x/η) := by
  let := probability_gibbs_of_partition
    (partition_pos_of_continuous (hF.continuous_potential x r)).ne'
    (partition_ne_top_of_integrable (hF.integrable_exp_neg_potential x hr hl))
  have hV : Measurable (fun z => (F z,gradient F z)) :=
    hF.smooth.continuous.measurable.prodMk hF.gradient_lipschitz.continuous.measurable
  have hf : Measurable (fun g => S.pre.run F (x,g)) :=
    (S.pre.measurable_run F hV).comp (by fun_prop)
  have hh := hpre.gaussian_smoothing hf (by fun_prop) (show 0<η/2 by positivity)
  have hfull : ((gaussianTape d S.slots).prod (stdGaussian (Point d))).map
      (fun z => S.pre.run F (x,z.1)+(η/2) • z.2)=
      (gaussianTape d S.full.slots).map (fun g => S.full.program.run F (x,g)) := by
    let f : (Fin (S.slots+1) → Point d) → Point d := fun g => S.full.program.run F (x,g)
    have hfm : Measurable f :=
      (S.full.program.measurable_run F hV).comp (measurable_const.prodMk measurable_id)
    have hp := ReservedProgram.fullTape_preserving (d:=d) S.slots
    have heq : (fun z : (Fin S.slots → Point d) × Point d =>
        S.pre.run F (x,z.1)+(η/2) • z.2)=f ∘ ReservedProgram.fullTape S.slots := by
      funext z
      dsimp only [f,comp_apply]
      rw [ReservedProgram.full_run]
      simp only [ReservedProgram.fullTape,Fin.append_left,Fin.append_right,hres]
    exact (congrArg (fun k => ((gaussianTape d S.slots).prod (stdGaussian (Point d))).map k) heq).trans
      ((Measure.map_map hfm hp.measurable).symm.trans (congrArg (Measure.map f) hp.map_eq))
  have hnoise := smoothing_add_gaussian
    ((gibbs (primitivePotential F x r)).prod (stdGaussian (Point d))) (gibbs (primitivePotential F x r))
    (fun z => z.1+(Real.sqrt 3*η/2) • z.2) id (by fun_prop) measurable_id
    (Real.sqrt 3*η/2) (η/2) η (by
      rw [div_pow,mul_pow,Real.sq_sqrt (by norm_num : (0:ℝ)≤3),div_pow]; ring) rfl
  rw [hfull,hnoise] at hh
  have hs : Real.sqrt (e^2*(circuitD F x)^2)=e*circuitD F x := by
    rw [←mul_pow,Real.sqrt_sq (mul_nonneg he (circuitD_nonneg F x))]
  have heq : e*circuitD F x/(η/2)=2*e*circuitD F x/η := by ring
  simpa only [id_eq,hs,heq] using hh

end LogConcaveSampling.OracleCompiler

end

end

end OAI
