import OAI.Probability.FreeIsing.Estimates.FiniteMarginals
import OAI.Probability.FreeIsing.Estimates.LawUniqueness
import OAI.Probability.FreeIsing.Trees.ConnectedHull

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem367

theorem HasFreeIsingLaw.finite_of_connected {d : ℕ} {theta : ℝ}
    {mu : Measure (TreeVertex d → IsingSpin)} (hmu : HasFreeIsingLaw theta mu)
    (D : Finset (TreeVertex d)) (hD : ConnectedFinset D) : IsFiniteMeasure mu := by
  classical
  constructor
  have hmass := hmu.restrict_finset D hD Finset.univ
  rw [Finset.coe_univ, Measure.map_apply D.measurable_restrict MeasurableSet.univ,
    Set.preimage_univ] at hmass
  rw [hmass]
  exact ENNReal.sum_lt_top.mpr (fun eta _ => ENNReal.ofReal_lt_top)

theorem HasFreeIsingLaw.unique {d : ℕ} {theta : ℝ}
    {mu nu : Measure (TreeVertex d → IsingSpin)}
    (hmu : HasFreeIsingLaw theta mu) (hnu : HasFreeIsingLaw theta nu) : mu = nu := by
  let : Nonempty IsingSpin := ⟨IsingSpin.neg⟩
  let : IsFiniteMeasure mu :=
    hmu.finite_of_connected (ConnectedHull.hull ∅) (ConnectedHull.connected_hull ∅)
  apply measure_eq_of_cofinal_cylinders ConnectedFinset exists_connectedFinset_superset
  intro D hD eta
  exact (hmu D hD eta).trans (hnu D hD eta).symm

end Problem367

end

end OAI
