import OAI.MathematicalPhysics.Boltzmann.Approximation.PositiveRestrictedChain
import OAI.MathematicalPhysics.Boltzmann.Branching.CharacteristicCutoffGeometry
import OAI.MathematicalPhysics.Boltzmann.Compactness.EntropyDissipationAverage

namespace OAI

section

/-! # The scalar entropy budget survives almost-everywhere slice convergence -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology
namespace BoltzmannNonuniqueness

theorem scalarEntropy_trace_bound {U : ℝ × Phase → ℝ} (hUm : Measurable U)
    {s : ℕ → ℝ} {t : ℝ} {C : ℝ≥0∞}
    (hc : ∀ᵐ p ∂(volume : Measure Phase), Tendsto (fun n => U (s n,p)) atTop (𝓝 (U (t,p))))
    (hb : ∀ n, (∫⁻ p : Phase, ENNReal.ofReal (scalarRelativeEntropy (maxwellian p.2) (U (s n,p)))) ≤ C) :
    (∫⁻ p : Phase, ENNReal.ofReal (scalarRelativeEntropy (maxwellian p.2) (U (t,p)))) ≤ C := by
  have hmm : Measurable (fun p : Phase => maxwellian p.2) := by unfold maxwellian; fun_prop
  have hum n : Measurable (fun p : Phase => U (s n,p)) :=
    hUm.comp (measurable_const.prodMk measurable_id)
  have hgm n : Measurable (fun p : Phase => scalarRelativeEntropy (maxwellian p.2) (U (s n,p))) :=
    (((hum n).mul (hum n).log).sub ((hum n).mul (measurable_const.add hmm.log))).add hmm
  apply lintegral_of_ae_tendsto_le hgm _ hb
  filter_upwards [hc] with p hp
  exact ((scalarRelativeEntropy_continuous (maxwellian p.2)).tendsto _).comp hp

end BoltzmannNonuniqueness

end

end

section

/-! # A fixed nonnegative dissipation budget survives entropy trace limits -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology
namespace BoltzmannNonuniqueness

theorem scalarEntropy_joint_trace_bound {U : ℝ × Phase → ℝ} (hUm : Measurable U)
    {s : ℕ → ℝ} {t : ℝ} {C d : ℝ≥0∞}
    (hc : ∀ᵐ p ∂(volume : Measure Phase), Tendsto (fun n => U (s n,p)) atTop (𝓝 (U (t,p))))
    (hb : ∀ n, (∫⁻ p : Phase, ENNReal.ofReal (scalarRelativeEntropy (maxwellian p.2) (U (s n,p))))+d ≤ C) :
    (∫⁻ p : Phase, ENNReal.ofReal (scalarRelativeEntropy (maxwellian p.2) (U (t,p))))+d ≤ C := by
  let H n := ∫⁻ p : Phase, ENNReal.ofReal (scalarRelativeEntropy (maxwellian p.2) (U (s n,p)))
  have hmm : Measurable (fun p : Phase => maxwellian p.2) := by unfold maxwellian; fun_prop
  have hum n : Measurable (fun p : Phase => U (s n,p)) :=
    hUm.comp (measurable_const.prodMk measurable_id)
  have hgm n : Measurable (fun p : Phase => scalarRelativeEntropy (maxwellian p.2) (U (s n,p))) :=
    (((hum n).mul (hum n).log).sub ((hum n).mul (measurable_const.add hmm.log))).add hmm
  have hlim : (∫⁻ p : Phase, ENNReal.ofReal (scalarRelativeEntropy (maxwellian p.2) (U (t,p)))) ≤
      liminf H atTop := by
    calc
      _ = ∫⁻ p : Phase, liminf (fun n => ENNReal.ofReal
          (scalarRelativeEntropy (maxwellian p.2) (U (s n,p)))) atTop := by
        apply lintegral_congr_ae
        filter_upwards [hc] with p hp
        exact (ENNReal.tendsto_ofReal (((BoltzmannNonuniqueness.scalarRelativeEntropy_continuous
          (maxwellian p.2)).tendsto _).comp hp)).liminf_eq.symm
      _ ≤ _ := lintegral_liminf_le (fun n => (hgm n).ennreal_ofReal)
  have hadd : liminf H atTop+d ≤ liminf (fun n => H n+d) atTop := by
    simpa only [liminf_const] using ennreal_liminf_add_nat H (fun _ => d)
  exact (add_le_add hlim le_rfl).trans (hadd.trans
    (liminf_le_of_frequently_le (Eventually.of_forall hb).frequently))

end BoltzmannNonuniqueness

end

end

end OAI
