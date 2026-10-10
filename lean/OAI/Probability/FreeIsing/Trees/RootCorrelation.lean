import OAI.Probability.FreeIsing.Spins.Moments
import OAI.Probability.FreeIsing.Stochastic.FiniteLawIntegral
import OAI.Probability.FreeIsing.Trees.PathCylinders

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem367

theorem HasFreeIsingLaw.root_correlation {d : ℕ} {theta : ℝ}
    {mu : Measure (TreeVertex d → IsingSpin)}
    (hmu : HasFreeIsingLaw theta mu) (hlo : -1 ≤ theta) (hhi : theta ≤ 1)
    (v : TreeVertex d) :
    ∫ x, spinSign (x (ConnectedHull.root d)) * spinSign (x v) ∂mu =
      theta ^ v.1.length := by
  let := hmu.isProbabilityMeasure
  have h := integral_spinPath_of_cylinderLaw hlo hhi (ConnectedHull.path v)
    (fun eta => ConnectedHull.freeLaw_path_cylinder hmu v eta)
  simpa only [ConnectedHull.path, Fin.val_zero, Fin.val_last,
    ConnectedHull.prefix_zero, ConnectedHull.prefix_length] using h

theorem HasFreeIsingLaw.factor_root_correlation {d : ℕ} {theta : ℝ}
    {Phi : (TreeVertex d → ℝ) → (TreeVertex d → IsingSpin)}
    (hPhi : Measurable Phi) (hmu : HasFreeIsingLaw theta (Measure.map Phi (labelMeasure d)))
    (hlo : -1 ≤ theta) (hhi : theta ≤ 1) (v : TreeVertex d) :
    ∫ U, spinSign (Phi U (ConnectedHull.root d)) * spinSign (Phi U v) ∂labelMeasure d =
      theta ^ v.1.length := by
  have hm : Measurable (fun x : TreeVertex d → IsingSpin =>
      spinSign (x (ConnectedHull.root d)) * spinSign (x v)) := by
    have hs : Measurable spinSign := measurable_spinToReal
    exact (hs.comp (measurable_pi_apply _)).mul (hs.comp (measurable_pi_apply _))
  exact (integral_map hPhi.aemeasurable hm.aestronglyMeasurable).symm.trans
    (hmu.root_correlation hlo hhi v)

theorem HasFreeIsingLaw.factor_action_root_correlation {d : ℕ} {theta : ℝ}
    {Phi : (TreeVertex d → ℝ) → (TreeVertex d → IsingSpin)}
    (hPhi : Measurable Phi) (hmu : HasFreeIsingLaw theta (Measure.map Phi (labelMeasure d)))
    (hlo : -1 ≤ theta) (hhi : theta ≤ 1) (g : TreeAut d)
    (hequiv : ∀ᵐ U ∂labelMeasure d, Phi (relabel g U) = relabel g (Phi U)) :
    ∫ U, spinSign (Phi U (ConnectedHull.root d)) *
      spinSign (Phi (relabel g U) (ConnectedHull.root d)) ∂labelMeasure d =
        theta ^ (g.toEquiv.symm (ConnectedHull.root d)).1.length := by
  calc
    _ = ∫ U, spinSign (Phi U (ConnectedHull.root d)) *
        spinSign (Phi U (g.toEquiv.symm (ConnectedHull.root d))) ∂labelMeasure d := by
      apply integral_congr_ae
      filter_upwards [hequiv] with U hU
      rw [hU]
      rfl
    _ = _ := hmu.factor_root_correlation hPhi hlo hhi _

end Problem367

end

end OAI
