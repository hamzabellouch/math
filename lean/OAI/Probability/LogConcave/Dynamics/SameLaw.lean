import Mathlib
import OAI.Probability.LogConcave.Dynamics.Squared
import OAI.Probability.LogConcave.Dynamics.NormSubSqThree

namespace OAI

section
noncomputable section
namespace LogConcaveSampling.Coupling
open MeasureTheory ProbabilityTheory Function
open scoped Classical

variable {Ω Γ : Type*} [MeasurableSpace Ω] [MeasurableSpace Γ]
  [StandardBorelSpace Γ] [Nonempty Γ] {d : ℕ}

theorem SquaredAt.of_same_law (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ν : Measure Γ) [IsProbabilityMeasure ν] (f : Ω → Point d) (g : Γ → Point d)
    (hf : Measurable f) (hg : Measurable g) (hlaw : μ.map f=ν.map g) :
    SquaredAt μ ν f g 0 := by
  let J : Γ → Point d × Γ := fun z => (g z,z)
  have hJ : Measurable J := hg.prodMk measurable_id
  let ι := ν.map J
  have : IsProbabilityMeasure ι := inferInstance
  have hl : ι.fst=ν.map g := by
    change (ν.map J).map Prod.fst=_
    rw [Measure.map_map measurable_fst hJ]
    rfl
  have hr : ι.snd=ν := by
    change (ν.map J).map Prod.snd=_
    rw [Measure.map_map measurable_snd hJ]
    exact Measure.map_id
  let Λ := lift μ ι f hf
  have hlink : μ.map f=ι.fst := hlaw.trans hl.symm
  have hm : Measurable (fun z : Point d × Γ => ‖z.1-g z.2‖^2) := by fun_prop
  have hi : Integrable (fun z : Point d × Γ => ‖z.1-g z.2‖^2) ι := by
    apply (integrable_map_measure hm.aestronglyMeasurable hJ.aemeasurable).mpr
    change Integrable (fun z => ‖g z-g z‖^2) ν
    simpa only [sub_self,norm_zero,zero_pow (by decide : 2≠0)] using
      (integrable_const (0 : ℝ) : Integrable (fun _ : Γ => (0 : ℝ)) ν)
  have he : (∫z : Point d × Γ,‖z.1-g z.2‖^2 ∂ι)=0 := by
    rw [integral_map hJ.aemeasurable hm.aestronglyMeasurable]
    simp [J]
  obtain ⟨hI,hE⟩ := lift_integrable μ ι f hf hlink _ hi
  refine ⟨Λ,inferInstance,lift_fst μ ι f hf,?_,hI,hE.trans_le he.le⟩
  have hh := congrArg (Measure.map Prod.snd) (lift_map μ ι f hf hlink)
  rw [Measure.map_map measurable_snd (by fun_prop)] at hh
  exact hh.trans hr

lemma SquaredAt.change_ideal {W : Type*} [MeasurableSpace W]
    {μ : Measure Ω} {ν : Measure W} [IsProbabilityMeasure ν]
    (θ : Measure Γ) [IsProbabilityMeasure θ]
    {f : Ω → Point d} {g : W → Point d} (h : Γ → Point d)
    (hf : Measurable f) (hg : Measurable g) (hh : Measurable h)
    {B : ℝ} (hc : SquaredAt μ ν f g B) (hlaw : ν.map g=θ.map h) :
    SquaredAt μ θ f h (2*B) := by
  have hzero := SquaredAt.of_same_law ν θ g h hg hh hlaw
  simpa only [mul_zero,add_zero] using hc.trans hf hg hh hzero

end LogConcaveSampling.Coupling

end

end

end OAI
