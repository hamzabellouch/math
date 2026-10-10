import OAI.Analysis.CircleDomains.Sobolev.NonnegativeMaximalL2

namespace OAI

/-! The exact planar L² maximal input, including a finite nonnegative
representative and the average bound for every positive fixed radius. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

theorem planarMaximalL2 : PlanarMaximalL2 := by
  refine ⟨20, by norm_num, ?_⟩
  intro g hg
  let f : ℂ → ℝ := hg.aestronglyMeasurable.mk g
  have hf : Measurable f := hg.aestronglyMeasurable.stronglyMeasurable_mk.measurable
  have heq : g =ᵐ[volume] f := hg.aestronglyMeasurable.ae_eq_mk
  have hf2 : MemLp f 2 volume := hg.ae_eq heq
  obtain ⟨m, hm, hm0, hm2, hE, hav⟩ := nonnegative_maximal_L2 hf.norm
    (fun x => norm_nonneg (f x)) hf2.norm
  have hsq : (∫ x, ‖f x‖^2) = ∫ x, g x^2 := by
    apply integral_congr_ae
    filter_upwards [heq] with x hx
    rw [← hx, Real.norm_eq_abs, sq_abs]
  refine ⟨m, hm, hm0, hm2, ?_, ?_⟩
  · rw [hsq] at hE
    exact hE.trans (mul_le_mul_of_nonneg_right (by norm_num) (integral_nonneg fun x => sq_nonneg (g x)))
  · intro r hr
    have hev (x : ℂ) : (∫ y in ball x r, ‖g y‖) = ∫ y in ball x r, ‖f y‖ :=
      integral_congr_ae (heq.restrict (s := ball x r) |>.fun_comp norm)
    filter_upwards [hav r hr] with x hx
    rwa [hev x]

end CircleDomainRigidity

end

end OAI
