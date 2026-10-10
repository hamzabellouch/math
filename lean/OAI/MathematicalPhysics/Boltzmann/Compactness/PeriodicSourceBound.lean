import OAI.MathematicalPhysics.Boltzmann.Jets.PeriodicJetFamilies
import OAI.MathematicalPhysics.Boltzmann.Branching.WeightedNetLoss

namespace OAI

/-! # A cellwise velocity estimate gives a spacetime almost-everywhere bound -/

noncomputable section

open MeasureTheory MeasureTheory.Measure Set
open BoltzmannNonuniqueness.WeightedTranslation

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem ae_bound_of_cell {T : ℝ} {k : ℝ × JetPrototype.Phase → ℝ} {w : ℝ → ℝ}
    (hkm : Measurable k) (hwm : Measurable w)
    (hperiodic : ∀ n, pull (displacement n) k = k)
    (hcell : ∀ t ∈ Ioc 0 T, ∀ x : Velocity, (∀ j, |x j| ≤ 1) →
      ∀ᵐ v : Velocity, k (t,(JetPeriodicDatum.spatialMap x,v)) ≤ w t) :
    ∀ᵐ u ∂WeightedLocal.spacetimeVolume, u.1 ∈ Ioc 0 T → k u ≤ w u.1 := by
  have hall (t : ℝ) (ht : t ∈ Ioc 0 T) (y : JetPrototype.Space) :
      ∀ᵐ v : Velocity, k (t,(y,v)) ≤ w t := by
    obtain ⟨n,x,hx,he⟩ := exists_shift_in_cell y
    filter_upwards [hcell t ht x hx] with v hv
    have hk := congrFun (hperiodic n) (t,(y,v))
    change k (t,(y-displacement n,v)) = k (t,(y,v)) at hk
    rw [he] at hk
    rwa [← hk]
  have hgood : MeasurableSet {u : ℝ × JetPrototype.Phase |
      u.1 ∈ Ioc 0 T → k u ≤ w u.1} := by
    simp only [imp_iff_not_or]
    exact (measurableSet_Ioc.preimage measurable_fst).compl.union
      (measurableSet_le hkm (hwm.comp measurable_fst))
  apply (ae_prod_iff_ae_ae hgood).mpr
  apply ae_of_all
  intro t
  have hslice : MeasurableSet {p : JetPrototype.Phase |
      t ∈ Ioc 0 T → k (t,p) ≤ w t} :=
    hgood.preimage (measurable_const.prodMk measurable_id)
  apply (ae_prod_iff_ae_ae hslice).mpr
  apply ae_of_all
  intro y
  by_cases ht : t ∈ Ioc 0 T
  · filter_upwards [hall t ht y] with v hv
    exact fun _ => hv
  · exact ae_of_all _ (fun _ h => (ht h).elim)

end BoltzmannNonuniqueness.JetCopyDatum

end

end OAI
