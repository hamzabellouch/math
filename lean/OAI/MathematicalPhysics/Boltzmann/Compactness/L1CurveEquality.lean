import OAI.MathematicalPhysics.Boltzmann.Compactness.StrongMildRepresentative
import Mathlib.MeasureTheory.Measure.OpenPos

namespace OAI

/-! # Spacetime equality determines a strongly continuous L¹ curve at every time -/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace BoltzmannNonuniqueness

theorem strong_ae_eq_all_times {T : ℝ} (hT : 0 < T) {F G : Evolution}
    (hFi : ∀ t, Integrable (F t)) (hGi : ∀ t, Integrable (G t))
    (hFc : ∀ t ∈ Icc 0 T,
      Tendsto (fun s => eLpNorm (fun p => F s p-F t p) 1 volume) (𝓝[Icc 0 T] t) (𝓝 0))
    (hGc : ∀ t ∈ Icc 0 T,
      Tendsto (fun s => eLpNorm (fun p => G s p-G t p) 1 volume) (𝓝[Icc 0 T] t) (𝓝 0))
    (he : (fun z : ℝ × Phase => F z.1 z.2) =ᵐ[(volume.restrict (Icc 0 T)).prod volume]
      (fun z => G z.1 z.2)) : ∀ t ∈ Icc 0 T, F t =ᵐ[volume] G t := by
  let F₁ (t : ℝ) : Lp ℝ 1 (volume : Measure Phase) := (memLp_one_iff_integrable.mpr (hFi t)).toLp (F t)
  let G₁ (t : ℝ) : Lp ℝ 1 (volume : Measure Phase) := (memLp_one_iff_integrable.mpr (hGi t)).toLp (G t)
  have hFrep t : F₁ t =ᵐ[volume] F t := (memLp_one_iff_integrable.mpr (hFi t)).coeFn_toLp
  have hGrep t : G₁ t =ᵐ[volume] G t := (memLp_one_iff_integrable.mpr (hGi t)).coeFn_toLp
  have hFcont : ContinuousOn F₁ (Icc 0 T) := by
    intro t ht
    apply tendsto_iff_edist_tendsto_0.mpr
    have hedist s : edist (F₁ s) (F₁ t) = eLpNorm (fun p => F s p-F t p) 1 volume := by
      rw [Lp.edist_def]
      exact eLpNorm_congr_ae ((hFrep s).sub (hFrep t))
    simpa only [hedist] using hFc t ht
  have hGcont : ContinuousOn G₁ (Icc 0 T) := by
    intro t ht
    apply tendsto_iff_edist_tendsto_0.mpr
    have hedist s : edist (G₁ s) (G₁ t) = eLpNorm (fun p => G s p-G t p) 1 volume := by
      rw [Lp.edist_def]
      exact eLpNorm_congr_ae ((hGrep s).sub (hGrep t))
    simpa only [hedist] using hGc t ht
  have he₁ : F₁ =ᵐ[volume.restrict (Icc 0 T)] G₁ := by
    filter_upwards [Measure.ae_ae_of_ae_prod he] with t ht
    change F t =ᵐ[volume] G t at ht
    exact Lp.ext ((hFrep t).trans (ht.trans (hGrep t).symm))
  have heq := Measure.eqOn_Icc_of_ae_eq (volume : Measure ℝ) (ne_of_lt hT)
    he₁ hFcont hGcont
  intro t ht
  have hrep : F₁ t =ᵐ[volume] G₁ t := by rw [heq ht]
  exact (hFrep t).symm.trans (hrep.trans (hGrep t))

namespace MildCollisionSolution

theorem evolution_eq_positive_each_time {T : ℝ} {f₀ : Density}
    {g : (ℝ × Position) × Velocity → ℝ}
    (S : MildCollisionSolution T f₀ g) (hT : 0 < T)
    (hf₀m : Measurable f₀) (hf₀i : Integrable f₀) :
    ∀ t ∈ Icc 0 T, evolution T f₀ g t =ᵐ[volume] positiveEvolution T f₀ g t := by
  have hi t : Integrable (evolution T f₀ g t) :=
    (TorusFlight.flight_measurePreserving (-t)).integrable_comp_of_integrable
      (TorusFlight.characteristicProfile_integrable hf₀i S.characteristicSource_measurable
        S.characteristicSource_integrable t)
  exact strong_ae_eq_all_times hT hi (S.positiveEvolution_integrable hf₀m hf₀i)
    (fun t ht => S.evolution_strong_continuity hT.le hf₀i ht)
    (fun t ht => S.positiveEvolution_strong_continuity hT.le hf₀m hf₀i ht)
    (S.evolution_eq_ae.symm.trans S.positiveEvolution_eq_ae)

end MildCollisionSolution
end BoltzmannNonuniqueness

end

end OAI
