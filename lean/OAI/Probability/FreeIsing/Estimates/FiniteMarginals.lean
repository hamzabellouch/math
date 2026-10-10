import OAI.Probability.FreeIsing.Model

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem367

def extendFiniteSpin {d : ℕ} (D : Finset (TreeVertex d))
    (eta : D → IsingSpin) : TreeVertex d → IsingSpin := by
  classical
  exact fun v => if hv : v ∈ D then eta ⟨v, hv⟩ else IsingSpin.neg

@[simp]
theorem extendFiniteSpin_apply {d : ℕ} (D : Finset (TreeVertex d))
    (eta : D → IsingSpin) (v : D) : extendFiniteSpin D eta v = eta v := by
  classical
  simp [extendFiniteSpin]

@[simp]
theorem restrict_extendFiniteSpin {d : ℕ} (D : Finset (TreeVertex d))
    (eta : D → IsingSpin) : D.restrict (extendFiniteSpin D eta) = eta := by
  funext v
  exact extendFiniteSpin_apply D eta v

theorem HasFreeIsingLaw.restrict_atom {d : ℕ} {theta : ℝ}
    {mu : Measure (TreeVertex d → IsingSpin)} (hmu : HasFreeIsingLaw theta mu)
    (D : Finset (TreeVertex d)) (hD : ConnectedFinset D) (eta : D → IsingSpin) :
    (mu.map D.restrict) {eta} = freeCylinderWeight theta D (extendFiniteSpin D eta) := by
  classical
  rw [Measure.map_apply D.measurable_restrict (measurableSet_singleton eta)]
  convert hmu D hD (extendFiniteSpin D eta) using 1
  congr 1
  ext x
  change D.restrict x = eta ↔ ∀ v ∈ D, x v = extendFiniteSpin D eta v
  constructor
  · intro hx v hv
    have h := congrFun hx ⟨v, hv⟩
    simpa [Finset.restrict_def, extendFiniteSpin, hv] using h
  · intro hx
    funext v
    simpa [Finset.restrict_def, extendFiniteSpin] using hx v v.property

theorem HasFreeIsingLaw.restrict_finset {d : ℕ} {theta : ℝ}
    {mu : Measure (TreeVertex d → IsingSpin)} (hmu : HasFreeIsingLaw theta mu)
    (D : Finset (TreeVertex d)) (hD : ConnectedFinset D)
    (A : Finset (D → IsingSpin)) :
    (mu.map D.restrict) A =
      ∑ eta ∈ A, freeCylinderWeight theta D (extendFiniteSpin D eta) := by
  rw [← sum_measure_singleton]
  exact Finset.sum_congr rfl (fun eta _ => hmu.restrict_atom D hD eta)

theorem HasFreeIsingLaw.cylinder_of_subset {d : ℕ} {theta : ℝ}
    {mu : Measure (TreeVertex d → IsingSpin)} (hmu : HasFreeIsingLaw theta mu)
    (D E : Finset (TreeVertex d)) (hE : ConnectedFinset E) (hDE : D ⊆ E)
    (eta : TreeVertex d → IsingSpin) :
    mu {x | ∀ v ∈ D, x v = eta v} =
      ∑ xi ∈ (Finset.univ.filter fun xi : E → IsingSpin =>
        ∀ v : D, xi ⟨v, hDE v.property⟩ = eta v),
        freeCylinderWeight theta E (extendFiniteSpin E xi) := by
  classical
  let A : Finset (E → IsingSpin) := Finset.univ.filter fun xi =>
    ∀ v : D, xi ⟨v, hDE v.property⟩ = eta v
  have hevent : {x : TreeVertex d → IsingSpin | ∀ v ∈ D, x v = eta v} =
      E.restrict ⁻¹' (A : Set (E → IsingSpin)) := by
    ext x
    simp [A, Finset.restrict_def]
  rw [hevent, ← Measure.map_apply E.measurable_restrict A.measurableSet]
  exact hmu.restrict_finset E hE A

end Problem367

end

end OAI
