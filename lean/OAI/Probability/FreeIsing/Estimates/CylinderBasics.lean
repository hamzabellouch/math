import OAI.Probability.FreeIsing.Model

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem367

theorem connectedFinset_singleton {d : ℕ} (v : TreeVertex d) :
    ConnectedFinset {v} := by
  classical
  refine ⟨Finset.singleton_nonempty v, ?_⟩
  intro x hx y hy
  simp only [Finset.mem_singleton] at hx hy
  subst x
  subst y
  exact Relation.ReflTransGen.refl

@[simp] theorem inducedEdges_singleton {d : ℕ} (v : TreeVertex d) :
    inducedEdges {v} = ∅ := by
  classical
  ext e
  simp [inducedEdges]
  rintro rfl
  simp

@[simp] theorem freeCylinderWeight_singleton {d : ℕ} (θ : ℝ)
    (v : TreeVertex d) (η : TreeVertex d → IsingSpin) :
    freeCylinderWeight θ {v} η = ENNReal.ofReal (1 / 2 : ℝ) := by
  classical
  simp [freeCylinderWeight]

theorem HasFreeIsingLaw.marginal {d : ℕ} {θ : ℝ}
    {μ : Measure (TreeVertex d → IsingSpin)} (hμ : HasFreeIsingLaw θ μ)
    (v : TreeVertex d) (s : IsingSpin) :
    μ {x | x v = s} = ENNReal.ofReal (1 / 2 : ℝ) := by
  classical
  simpa using hμ {v} (connectedFinset_singleton v) (fun _ => s)

end Problem367

end

end OAI
