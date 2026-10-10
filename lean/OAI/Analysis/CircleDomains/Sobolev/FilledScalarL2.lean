import OAI.Analysis.CircleDomains.Sobolev.FilledScalarGlobalEnergy

namespace OAI

/-! The two ordinary differential components of the finite filled scalar
are in planar L², with the source energy as their combined bound. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem memLp_partials_of_integrable_euclidean_energy {f : ℂ → ℝ}
    (h : Integrable (euclideanGradientEnergy f)) :
    MemLp (fun z => fderiv ℝ f z 1) 2 volume ∧
      MemLp (fun z => fderiv ℝ f z Complex.I) 2 volume := by
  have hm₁ := measurable_fderiv_apply_const ℝ f (1 : ℂ)
  have hm₂ := measurable_fderiv_apply_const ℝ f Complex.I
  constructor
  · apply (memLp_two_iff_integrable_sq hm₁.aestronglyMeasurable).mpr
    apply h.mono' (hm₁.pow_const 2).aestronglyMeasurable
    exact Eventually.of_forall fun z => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact le_add_of_nonneg_right (sq_nonneg _)
  · apply (memLp_two_iff_integrable_sq hm₂.aestronglyMeasurable).mpr
    apply h.mono' (hm₂.pow_const 2).aestronglyMeasurable
    exact Eventually.of_forall fun z => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact le_add_of_nonneg_left (sq_nonneg _)

open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩
variable [MeasurableSpace C(PathTime, Sphere)]
namespace RetainedRealCircleModel
variable {d : PathCodeData Sphere Sphere} {π : Sphere → Sphere} {m : ℕ}
  {Q : Fin m → PhysicalRealCoordinate d π} (R : RetainedRealCircleModel d π Q)

 theorem eventually_filled_partials_memLp (i : Fin m) :
    ∀ᶠ n in atTop, ∀ F : R.HoleFilling i n,
      MemLp (fun z => fderiv ℝ F.filled z 1) 2 volume ∧
        MemLp (fun z => fderiv ℝ F.filled z Complex.I) 2 volume := by
  filter_upwards [R.eventually_filled_global_energy i] with n hn F
  exact memLp_partials_of_integrable_euclidean_energy (hn F).1

end RetainedRealCircleModel
end CircleDomainRigidity

end

end OAI
