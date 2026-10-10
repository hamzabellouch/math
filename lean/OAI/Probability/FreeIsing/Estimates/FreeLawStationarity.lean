import OAI.Probability.FreeIsing.Estimates.CylinderAutomorphism
import OAI.Probability.FreeIsing.Estimates.FreeLawUnique
import OAI.Probability.FreeIsing.Estimates.RelabelMeasure

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem367

theorem HasFreeIsingLaw.map_relabel_eq {d : ℕ} {theta : ℝ}
    {mu : Measure (TreeVertex d → IsingSpin)}
    (hmu : HasFreeIsingLaw theta mu) (g : TreeAut d) :
    mu.map (relabel g) = mu :=
  (hmu.map_relabel g).unique hmu

theorem HasFreeIsingLaw.measurePreserving_relabel {d : ℕ} {theta : ℝ}
    {mu : Measure (TreeVertex d → IsingSpin)}
    (hmu : HasFreeIsingLaw theta mu) (g : TreeAut d) :
    MeasurePreserving (relabel g) mu mu :=
  ⟨Problem367.measurable_relabel g, hmu.map_relabel_eq g⟩

theorem HasFreeIsingLaw.integral_relabel {d : ℕ} {theta : ℝ}
    {mu : Measure (TreeVertex d → IsingSpin)}
    (hmu : HasFreeIsingLaw theta mu) (g : TreeAut d)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : (TreeVertex d → IsingSpin) → E) :
    (∫ x, f (relabel g x) ∂mu) = ∫ x, f x ∂mu := by
  apply (hmu.measurePreserving_relabel g).integral_comp
  convert (MeasurableEquiv.piCongrLeft
    (fun _ : TreeVertex d => IsingSpin) g.toEquiv).measurableEmbedding using 1
  funext x v
  obtain ⟨u, rfl⟩ := g.toEquiv.surjective v
  simp [MeasurableEquiv.piCongrLeft_apply_apply, relabel]

theorem HasFreeIsingLaw.integral_pair_image {d : ℕ} {theta : ℝ}
    {mu : Measure (TreeVertex d → IsingSpin)}
    (hmu : HasFreeIsingLaw theta mu) (g : TreeAut d)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : IsingSpin → IsingSpin → E) (u v : TreeVertex d) :
    (∫ x, f (x (g.toEquiv u)) (x (g.toEquiv v)) ∂mu) =
      ∫ x, f (x u) (x v) ∂mu := by
  simpa only [relabel, Equiv.symm_apply_apply] using
    (hmu.integral_relabel g (fun x => f (x (g.toEquiv u)) (x (g.toEquiv v)))).symm

end Problem367

end

end OAI
