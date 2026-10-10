import Mathlib
import OAI.Analysis.CoulombRadii.RadialBounds.SpatialAnnulus
import OAI.Analysis.CoulombRadii.RandomFields.PhysicalLikelihoodBridge
import OAI.Analysis.CoulombRadii.RandomFields.PosteriorShellError

namespace OAI

section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
noncomputable section
namespace NeutralAtom
lemma packet_ball_containment {g : Position → ℝ} (hg : ∀ x,1<‖x‖ → g x=0)
    {c r₀ s R : ℝ} (hc : 0<c) (hr₀ : 0<r₀) (hs : 0<s) (hrR : r₀ ≤ R)
    (hq : c*s^packetExponent ≤ 1/4) {z y : Position}
    (hz : z∈Metric.ball (0:Position) (R/2)) (hK : packetKernel g c r₀ s z y≠0) :
    y∈Metric.ball (0:Position) R := by
  have hR : 0<R := hr₀.trans_le hrR
  have hzn : ‖z‖<R/2 := by simpa using hz
  have hmax : max ‖z‖ r₀ ≤ R := max_le (by linarith) hrR
  have hd := (packetKernel_support g hg hc hr₀ hs z y hK).trans
    ((packetWidth_le c r₀ s hc.le hr₀ hs z).trans
      (mul_le_mul_of_nonneg_left hmax (by positivity)))
  have hq' := mul_le_mul_of_nonneg_right hq hR.le
  have hdiff := norm_sub_norm_le y z
  simp only [Metric.mem_ball,dist_zero_right]
  linarith only [hd,hq',hdiff,hzn,hR]

lemma physical_interior_packet_transfer {n J : ℕ} {ψ : Wavefunction n} {g : Gradient n}
    (hd : FormDomain ψ g) (hn : normSquared ψ=1) (rads : Fin J → ℝ) (j : ℕ)
    {g₀ : Position → ℝ} (hg : Continuous g₀) (hm : (∫ x,g₀ x^2)=1)
    (hgs : ∀ x,1<‖x‖ → g₀ x=0) {c r₀ s R : ℝ}
    (hc : 0<c) (hr₀ : 0<r₀) (hs : 0<s) (hrR : r₀ ≤ R) (hq : c*s^packetExponent ≤ 1/4) :
    letI := rawLaw_isProbability hd.2.2.1 hn
    let P := observationLaw J (rawLaw ψ)
    (∫ x,rawCount (Metric.ball (0:Position) (R/2)) x ∂rawLaw ψ) ≤
      ∫ o,(∫ y in Metric.ball (0:Position) R,
        conditionalPacketDensity P Prod.fst (tailObservation rads j) g₀ c r₀ s (tailObservation rads j o) y) ∂P := by
  have := rawLaw_isProbability hd.2.2.1 hn
  dsimp only
  let P := observationLaw J (rawLaw ψ)
  have hraw := observationLaw_rawProjection (J:=J) (rawLaw ψ)
  have He := conditional_packet_event_mass P (rawLaw ψ) hraw (measurable_tailObservation rads j)
    hg hm hc hr₀ hs (Metric.ball (0:Position) R) (B:=univ) MeasurableSet.univ
  simp only [Measure.restrict_univ] at He
  rw [He]
  have hF : Measurable (rawCount (n:=n) (Metric.ball (0:Position) (R/2))) := measurable_rawCount measurableSet_ball
  have HI := integral_map hraw.measurable.aemeasurable (hF.aestronglyMeasurable (μ:=P.map Prod.fst))
  rw [hraw.map_eq] at HI
  rw [HI]
  apply integral_mono (hraw.integrable_comp_of_integrable ((rawCount_memLp hd.2.2.1 hn measurableSet_ball).integrable (by norm_num)))
    (hraw.integrable_comp_of_integrable ((packetMass_memLp hg hm hc hr₀ hs _ (rawLaw ψ)).integrable (by norm_num)))
  intro o
  exact rawCount_le_packetMass g₀ hm hc hr₀ hs _ _
    (fun z y hz hK => packet_ball_containment hgs hc hr₀ hs hrR hq hz hK) o.1

lemma raw_population_asH1 {n : ℕ} {ψ : Wavefunction n} {g : Gradient n}
    (hd : FormDomain ψ g) {S : Set Position} (hS : MeasurableSet S) :
    (∫ x,rawCount S x ∂rawLaw ψ)=
      Coulomb.expectedPopulation (asH1 ψ g hd.2.1 hd.2.2.1 hd.2.2.2.1) S := by
  rw [integral_rawLaw hd.2.2.1,rawExpectation_eq_stateWeightedIntegral hd.2.2.1
    (measurable_rawCount hS) (C:=(n:ℝ)) (fun x => by
      rw [Real.norm_of_nonneg (rawCount_nonneg S x)]; exact rawCount_le_number S x)]
  rw [Coulomb.expectedPopulation_eq _ hS]
  change stateWeightedIntegral ψ (fun x => ∑ i : Fin n,S.indicator (fun _ => (1:ℝ)) (x i))=_
  simpa only [Coulomb.potentialForm,Coulomb.localCount,position_flattenConfiguration,rawCount] using
    (asH1_potentialForm ψ g hd.2.1 hd.2.2.1 hd.2.2.2.1 (Coulomb.localCount S)).symm
end NeutralAtom
end

end

end OAI
