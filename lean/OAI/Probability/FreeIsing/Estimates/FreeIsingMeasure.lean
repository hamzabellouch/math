import OAI.Probability.FreeIsing.Estimates.FreeLawUnique
import OAI.Probability.FreeIsing.Trees.BroadcastJointLaw

namespace OAI

noncomputable section
open MeasureTheory
namespace Problem367

def freeIsingMeasure (d : ℕ) (theta : ℝ) : Measure (TreeVertex d → IsingSpin) :=
  (labelMeasure d).map (RootedBroadcast.factor theta)

instance freeIsingMeasure_probability (d : ℕ) (theta : ℝ) :
    IsProbabilityMeasure (freeIsingMeasure d theta) := by
  let : IsProbabilityMeasure (labelMeasure d) := by
    unfold labelMeasure
    infer_instance
  unfold freeIsingMeasure
  infer_instance

theorem freeIsingMeasure_hasFreeIsingLaw (d : ℕ) {theta : ℝ}
    (h0 : -1 ≤ theta) (h1 : theta ≤ 1) :
    HasFreeIsingLaw theta (freeIsingMeasure d theta) :=
  RootedBroadcast.hasFreeIsingLaw_of_root_nonroot_joint h0 h1
    (RootedBroadcast.map_factor_rest d theta)

theorem exists_freeIsingLaw (d : ℕ) {theta : ℝ} (h0 : -1 ≤ theta) (h1 : theta ≤ 1) :
    ∃ mu : Measure (TreeVertex d → IsingSpin), IsProbabilityMeasure mu ∧ HasFreeIsingLaw theta mu :=
  ⟨freeIsingMeasure d theta, inferInstance, freeIsingMeasure_hasFreeIsingLaw d h0 h1⟩

theorem HasFreeIsingLaw.eq_freeIsingMeasure {d : ℕ} {theta : ℝ}
    {mu : Measure (TreeVertex d → IsingSpin)} (hmu : HasFreeIsingLaw theta mu)
    (h0 : -1 ≤ theta) (h1 : theta ≤ 1) : mu = freeIsingMeasure d theta :=
  hmu.unique (freeIsingMeasure_hasFreeIsingLaw d h0 h1)

end Problem367

end

end OAI
