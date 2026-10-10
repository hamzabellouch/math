import Mathlib
import OAI.Analysis.CoulombIonization.RadialBounds.UnshiftedCellCountBarrier

namespace OAI

open MeasureTheory Filter Set
open scoped Topology BigOperators
noncomputable section
namespace CoulombAtom
attribute [local irreducible] formEnergy energy

lemma priceEnergy_zero (E : ℕ → ℝ) : priceEnergy E 0 = sInf (Set.range E) := by
  simp only [priceEnergy,zero_mul,add_zero]

lemma corePriceExcess_le_zero_add (Z : ℕ) {N : ℕ} (ψ : FormVector N)
    {lam : ℝ} (hlam : 0 < lam) :
    corePriceExcess Z lam ψ ≤ corePriceExcess Z 0 ψ+lam*N*formMass ψ := by
  have hp := mul_le_mul_of_nonneg_right (quantum_unpriced_le_price Z hlam) (formMass_nonneg ψ)
  simp only [corePriceExcess,zero_mul,add_zero,priceEnergy_zero]
  linarith only [hp]

namespace CoreObservationGraph

lemma excess_le_zero_add (G : CoreObservationGraph) (Z : ℕ) {lam : ℝ} (hlam : 0 < lam) :
    G.excess Z lam ≤ G.excess Z 0+lam*G.coreSize*G.mass := by
  rw [excess,excess,mass,←coreLawAverage_mass G.sobolev]
  unfold coreLawAverage
  rw [Finset.mul_sum,←Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro t _
  rw [←integral_const_mul,←integral_add (coreSlice_priceExcess_integrable G.sobolev t Z 0)
    ((G.sobolev.coreSlice_mass_integrable t).const_mul _)]
  exact integral_mono (coreSlice_priceExcess_integrable G.sobolev t Z lam)
    ((coreSlice_priceExcess_integrable G.sobolev t Z 0).add
      ((G.sobolev.coreSlice_mass_integrable t).const_mul _))
    (fun u => corePriceExcess_le_zero_add Z _ hlam)

lemma fieldMoment_tendsto_zero (G : CoreObservationGraph) (Z : ℕ) (y : Space)
    {lam : ℕ → ℝ} (hlam : ∀ n, 0 ≤ lam n) (ht : Tendsto lam atTop (𝓝 0)) :
    Tendsto (fun n => G.fieldMoment Z (lam n) y) atTop (𝓝 (G.fieldMoment Z 0 y)) := by
  unfold fieldMoment coreLawAverage
  apply tendsto_finsetSum
  intro t ht'
  apply tendsto_integral_of_dominated_convergence
    (fun u => ((Z:ℝ)/‖y‖)^2*formMass (coreSlice G.vector t u))
  · intro n
    exact (coreFieldSquare_coreSlice_integrable G.sobolev t (Nat.cast_nonneg Z) (hlam n) y).aestronglyMeasurable
  · exact (G.sobolev.coreSlice_mass_integrable t).const_mul _
  · intro n
    apply ae_of_all
    intro u
    rw [Real.norm_of_nonneg (coreFieldSquare_nonneg _ _ _ _)]
    exact coreFieldSquare_le_nuclear _ (Nat.cast_nonneg Z) (hlam n) y
  · apply ae_of_all
    intro u
    have hc : Continuous (fun l : ℝ => coreFieldSquare Z l y (coreSlice G.vector t u)) := by
      unfold coreFieldSquare normalizedCoreField
      fun_prop
    exact hc.continuousAt.tendsto.comp ht

end CoreObservationGraph
namespace CoreObservationEnsemble

def coreParticleMoment (E : CoreObservationEnsemble) : ℝ :=
  ∑ i, (E.graph i).coreSize*(E.graph i).mass

lemma coreParticleMoment_nonneg (E : CoreObservationEnsemble) : 0 ≤ E.coreParticleMoment :=
  Finset.sum_nonneg (fun i _ => mul_nonneg (Nat.cast_nonneg _) (E.graph i).mass_nonneg)

lemma excess_le_zero_add (E : CoreObservationEnsemble) (Z : ℕ) {lam : ℝ} (hlam : 0 < lam) :
    E.excess Z lam ≤ E.excess Z 0+lam*E.coreParticleMoment := by
  unfold excess coreParticleMoment
  rw [Finset.mul_sum,←Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  simpa only [mul_assoc] using (E.graph i).excess_le_zero_add Z hlam

lemma fieldMoment_tendsto_zero (E : CoreObservationEnsemble) (Z : ℕ) (y : Space)
    {lam : ℕ → ℝ} (hlam : ∀ n, 0 ≤ lam n) (ht : Tendsto lam atTop (𝓝 0)) :
    Tendsto (fun n => E.fieldMoment Z (lam n) y) atTop (𝓝 (E.fieldMoment Z 0 y)) := by
  exact tendsto_finsetSum _ (fun i _ => (E.graph i).fieldMoment_tendsto_zero Z y hlam ht)

end CoreObservationEnsemble

 theorem ensemble_unshifted_local_field_scale (E : CoreObservationEnsemble) (Z : ℕ)
    (y : Space) {a D : ℝ} (ha : 0 < a) (hs : 12*a ≤ ‖y‖)
    (hm : E.mass = 1) (hD : 0 ≤ D) (he : E.excess Z 0 ≤ D) :
    E.fieldMoment Z 0 y ≤ localFieldUniversalConstant*
      localFieldScale a D (E.countMoment y (8*a)) := by
  have hh (lam : ℝ) (hlam : 0 < lam) :
      E.fieldMoment Z lam y ≤ localFieldUniversalConstant*
        localFieldScale a (D+lam*E.coreParticleMoment) (E.countMoment y (8*a)) := by
    have hb := E.excess_le_zero_add Z hlam
    have hex : E.excess Z lam ≤ D+lam*E.coreParticleMoment := by linarith only [hb,he]
    have hd : 0 ≤ D+lam*E.coreParticleMoment :=
      add_nonneg hD (mul_nonneg hlam.le E.coreParticleMoment_nonneg)
    exact (ensemble_local_field_scale E y ha hs hm (Nat.cast_nonneg Z) hlam).trans
      (mul_le_mul_of_nonneg_left (localFieldScale_mono ha (max_le hex hd) le_rfl)
        localFieldUniversalConstant_pos.le)
  let eps (n : ℕ) : ℝ := 1/((n:ℝ)+1)
  have hp (n : ℕ) : 0 < eps n := by dsimp [eps]; positivity
  have ht : Tendsto eps atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hc : Continuous (fun t : ℝ => localFieldUniversalConstant*
      localFieldScale a (D+t*E.coreParticleMoment) (E.countMoment y (8*a))) := by
    unfold localFieldScale
    fun_prop
  have ht' : Tendsto (fun n => localFieldUniversalConstant*
      localFieldScale a (D+eps n*E.coreParticleMoment) (E.countMoment y (8*a))) atTop
      (𝓝 (localFieldUniversalConstant*localFieldScale a D (E.countMoment y (8*a)))) := by
    simpa only [Function.comp_def,zero_mul,add_zero] using hc.continuousAt.tendsto.comp ht
  exact le_of_tendsto_of_tendsto (E.fieldMoment_tendsto_zero Z y (fun n => (hp n).le) ht) ht'
    (Eventually.of_forall (fun n => hh (eps n) (hp n)))

end CoulombAtom

end

end OAI
