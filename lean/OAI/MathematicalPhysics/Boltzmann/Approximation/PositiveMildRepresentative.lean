import OAI.MathematicalPhysics.Boltzmann.Approximation.MildRenormalization

namespace OAI

/-! # A nonnegative strongly continuous representative with the exact initial trace -/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace BoltzmannNonuniqueness.MildCollisionSolution

def positiveEvolution (T : ℝ) (f₀ : Density) (g : (ℝ × Position) × Velocity → ℝ) : Evolution :=
  fun t p => max (evolution T f₀ g t p) 0

variable {T : ℝ} {f₀ : Density} {g : (ℝ × Position) × Velocity → ℝ}

theorem evolution_measurable (S : MildCollisionSolution T f₀ g) (hf₀ : Measurable f₀) :
    Measurable (fun z : ℝ × Phase => evolution T f₀ g z.1 z.2) := by
  have hm := (hf₀.comp measurable_snd).add
    (Published.timePrimitive_measurable (volume.restrict (Icc 0 T)) S.characteristicSource_measurable)
  exact hm.comp (TorusFlight.back_measurePreserving (volume.restrict (Icc 0 T))).measurable

theorem positiveEvolution_measurable (S : MildCollisionSolution T f₀ g) (hf₀ : Measurable f₀) :
    Measurable (fun z : ℝ × Phase => positiveEvolution T f₀ g z.1 z.2) :=
  (S.evolution_measurable hf₀).max measurable_const

theorem positiveEvolution_nonnegative (t : ℝ) (p : Phase) : 0 ≤ positiveEvolution T f₀ g t p :=
  le_max_right _ _

theorem positiveEvolution_eq_ae (S : MildCollisionSolution T f₀ g) :
    TorusFlight.regroup g =ᵐ[(volume.restrict (Icc 0 T)).prod (volume : Measure Phase)]
      (fun z => positiveEvolution T f₀ g z.1 z.2) := by
  filter_upwards [S.evolution_eq_ae] with z hz
  change TorusFlight.regroup g z = max (evolution T f₀ g z.1 z.2) 0
  rw [← hz]
  exact (max_eq_left (S.nonnegative ((z.1,z.2.1),z.2.2))).symm

theorem positiveEvolution_initial (hT : 0 ≤ T) (hf₀ : ∀ p, 0 ≤ f₀ p) (p : Phase) :
    positiveEvolution T f₀ g 0 p = f₀ p := by
  rw [positiveEvolution,evolution_initial hT,max_eq_left (hf₀ p)]

theorem positiveEvolution_strong_continuity (S : MildCollisionSolution T f₀ g)
    (hT : 0 ≤ T) (hf₀m : Measurable f₀) (hf₀ : Integrable f₀)
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    Tendsto (fun s => eLpNorm (fun p => positiveEvolution T f₀ g s p-positiveEvolution T f₀ g t p)
      1 volume) (𝓝[Icc 0 T] t) (𝓝 0) := by
  have hm s : Measurable (fun p => positiveEvolution T f₀ g s p) :=
    (S.positiveEvolution_measurable hf₀m).comp (measurable_const.prodMk measurable_id)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (S.evolution_strong_continuity hT hf₀ ht) (fun _ => zero_le)
  intro s
  apply eLpNorm_mono ((hm s).sub (hm t)).aestronglyMeasurable
  intro p
  exact abs_max_sub_max_le_abs _ _ _

theorem positiveEvolution_integrable (S : MildCollisionSolution T f₀ g)
    (hf₀m : Measurable f₀) (hf₀ : Integrable f₀) (t : ℝ) :
    Integrable (positiveEvolution T f₀ g t) := by
  have hi := (TorusFlight.flight_measurePreserving (-t)).integrable_comp_of_integrable
    (TorusFlight.characteristicProfile_integrable hf₀ S.characteristicSource_measurable
      S.characteristicSource_integrable t)
  apply hi.norm.mono'
    (((S.positiveEvolution_measurable hf₀m).comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable)
  filter_upwards [] with p
  change ‖max (evolution T f₀ g t p) 0‖ ≤ ‖evolution T f₀ g t p‖
  simp only [Real.norm_eq_abs]
  simpa only [sub_zero,max_self] using abs_max_sub_max_le_abs (evolution T f₀ g t p) 0 0

end BoltzmannNonuniqueness.MildCollisionSolution

end

end OAI
