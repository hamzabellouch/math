import OAI.Probability.FirstPassage.PassageTime

namespace OAI

namespace PlanarFPP

def reverseSteps (ds : List Step) : List Step := ds.reverse.map Step.reverse

@[simp] theorem reverseSteps_nil : reverseSteps [] = [] := rfl
@[simp] theorem reverseSteps_cons (d : Step) (ds : List Step) :
    reverseSteps (d :: ds) = reverseSteps ds ++ [d.reverse] := by
  simp [reverseSteps]

@[simp] theorem displacement_reverseSteps (ds : List Step) :
    displacement (reverseSteps ds) = -displacement ds := by
  induction ds with
  | nil => simp
  | cons d ds ih => simp [ih, add_comm]

theorem pathCost_reverse (τ : Edge → ℝ) (p : Vertex) (ds : List Step) :
    pathCost τ (p + displacement ds) (reverseSteps ds) = pathCost τ p ds := by
  induction ds generalizing p with
  | nil => simp [pathCost]
  | cons d ds ih =>
    rw [reverseSteps_cons, displacement_cons, pathCost_append]
    have ha : p + (d.delta + displacement ds) = (p + d.delta) + displacement ds :=
      (add_assoc _ _ _).symm
    rw [ha, ih, displacement_reverseSteps]
    have hb : p + d.delta + displacement ds + -displacement ds = p + d.delta := by
      simp [add_assoc]
    rw [hb]
    simp [pathCost, Step.edge_reverse, add_comm]

theorem passageTime_symm (τ : Edge → ℝ) (hτ : ∀ e, 0 ≤ τ e) (p q : Vertex) :
    passageTime τ p q = passageTime τ q p := by
  have hle : ∀ p q, passageTime τ p q ≤ passageTime τ q p := by
    intro p q
    apply le_csInf (path_costs_nonempty τ q p)
    rintro t ⟨ds, hend, rfl⟩
    have hfinish : p + displacement (reverseSteps ds) = q := by
      rw [displacement_reverseSteps, ← hend]
      simp [add_assoc]
    have hc := passageTime_le_cost τ hτ p q (reverseSteps ds) hfinish
    rw [← hend, pathCost_reverse] at hc
    simpa only [hend] using hc
  exact le_antisymm (hle p q) (hle q p)

end PlanarFPP

end OAI
