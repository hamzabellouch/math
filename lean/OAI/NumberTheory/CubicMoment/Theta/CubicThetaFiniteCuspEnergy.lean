import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCuspExteriorMass
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaFiniteCusps

namespace OAI

/-! Exact summation of the sharp cusp estimates. Distinct cusp classes
are disjoint already at height one, so no covering multiplicity is lost
in the gradient coefficient. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators MatrixGroups
namespace CubicFirstMoment

lemma cubicThetaIntegral_cover_le {K U : Set CubicThetaQuotient}
    (hK : MeasurableSet K) (hU : MeasurableSet U) (hcover : K∪U=univ)
    {f : CubicThetaQuotient → ℝ} (hf : Integrable f cubicThetaQuotientMeasure)
    (hn : ∀ q, 0≤f q) :
    (∫ q, f q ∂cubicThetaQuotientMeasure)≤
      (∫ q in K, f q ∂cubicThetaQuotientMeasure)+
      ∫ q in U, f q ∂cubicThetaQuotientMeasure := by
  rw [← integral_indicator hK,← integral_indicator hU,
    ← integral_add (hf.indicator hK) (hf.indicator hU)]
  apply integral_mono hf ((hf.indicator hK).add (hf.indicator hU))
  intro q
  dsimp only [Pi.add_apply]
  have hq : q∈K∪U := by rw [hcover]; trivial
  rcases hq with hq | hq
  · rw [indicator_of_mem hq]
    exact le_add_of_nonneg_right (indicator_nonneg (fun x hx => hn x) q)
  · rw [indicator_of_mem hq]
    exact le_add_of_nonneg_left (indicator_nonneg (fun x hx => hn x) q)

lemma cubicThetaFiniteCusps_energy_le (T : Finset SL(2,Eisenstein))
    (hT : (T : Set SL(2,Eisenstein)).PairwiseDisjoint
      (fun δ => cubicThetaCuspNeighborhood δ 1)) (F : cubicThetaSmoothTests) :
    (∑ δ∈T, ∫ q in cubicThetaCuspNeighborhood δ 1,
      cubicThetaQuotientEnergy F q ∂cubicThetaQuotientMeasure)≤
    ∫ q, cubicThetaQuotientEnergy F q ∂cubicThetaQuotientMeasure := by
  rw [← integral_biUnion_finset T (fun δ hδ => cubicThetaCuspNeighborhood_measurable δ (le_refl 1))
    hT (fun δ hδ => (cubicThetaGradientEnergy_integrable F).integrableOn)]
  exact setIntegral_le_integral (cubicThetaGradientEnergy_integrable F)
    (Filter.Eventually.of_forall (cubicThetaQuotientEnergy_nonneg F))

lemma cubicThetaFiniteCusps_mass_le (S T : Finset SL(2,Eisenstein))
    (hcover : cubicThetaQuotientCore S 2∪(⋃ δ∈T,cubicThetaCuspNeighborhood δ 2)=univ)
    (hT : (T : Set SL(2,Eisenstein)).PairwiseDisjoint
      (fun δ => cubicThetaCuspNeighborhood δ 2)) (F : cubicThetaSmoothTests) :
    (∫ q, cubicThetaSectionNorm F q^2 ∂cubicThetaQuotientMeasure)≤
    (∫ q in cubicThetaQuotientCore S 2, cubicThetaSectionNorm F q^2 ∂cubicThetaQuotientMeasure)+
    ∑ δ∈T, ∫ q in cubicThetaCuspNeighborhood δ 2,
      cubicThetaSectionNorm F q^2 ∂cubicThetaQuotientMeasure := by
  have hU : MeasurableSet (⋃ δ∈T,cubicThetaCuspNeighborhood δ 2) :=
    T.measurableSet_biUnion (fun δ hδ => cubicThetaCuspNeighborhood_measurable δ (by norm_num))
  have h := cubicThetaIntegral_cover_le (cubicThetaQuotientCore_compact S 2).measurableSet
    hU hcover (cubicThetaMass_integrable F) (fun q => sq_nonneg _)
  rwa [integral_biUnion_finset T (fun δ hδ => cubicThetaCuspNeighborhood_measurable δ (by norm_num))
    hT (fun δ hδ => (cubicThetaMass_integrable F).integrableOn)] at h

end CubicFirstMoment

end

end OAI
