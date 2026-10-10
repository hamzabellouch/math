import OAI.Analysis.MassAction.Model
import OAI.Analysis.MassAction.CutFlux

namespace OAI

/-! Application of the finite directed-cut inequality to the exact qualified
mass-action vector field. -/

noncomputable section

namespace Problem326

open scoped BigOperators

/-- Pairing the mass-action field with a normal gives the corresponding
weighted difference of complex levels. -/
theorem dot_massAction_eq_flux {d : ℕ} (N : ReactionNetwork d)
    (κ : Reaction N → ℝ) (x r : Fin d → ℝ) :
    dot r (massAction N κ x) =
      ∑ e : Reaction N, κ e * monomial x e.val.1 *
        (dot r (fun i => (e.val.2 i : ℝ)) - dot r (fun i => (e.val.1 i : ℝ))) := by
  classical
  simp only [dot, massAction, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- All-pairs monomial domination for the network supplies an inward
mass-action derivative in the specified direction. Positivity of species
and rates is the only analytical input to this finite estimate. -/
theorem massAction_inward_of_monomial_order {d : ℕ} (N : ReactionNetwork d)
    (κ : Reaction N → ℝ) (x r : Fin d → ℝ) (δ : ℝ)
    (hweak : WeaklyReversible N) (hx : PositiveState x)
    (hκ : ∀ e, 0 < κ e) (hδ : 0 ≤ δ)
    (horder : ∀ y ∈ N.complexes, ∀ z ∈ N.complexes,
      dot r (fun i => (y i : ℝ)) < dot r (fun i => (z i : ℝ)) →
      monomial x z ≤ δ * monomial x y)
    (hrate : ∀ e, δ * (∑ f, κ f) < κ e) :
    0 ≤ dot r (massAction N κ x) := by
  classical
  rw [dot_massAction_eq_flux]
  apply CutFlux.total_flux_nonneg_of_source_order
    (fun e : Reaction N => e.val.1) (fun e : Reaction N => e.val.2)
    (fun y => dot r (fun i => (y i : ℝ))) (monomial x) κ δ
  · intro e
    apply Relation.TransGen.mono (r := HasReaction N) ?_ _ _ (hweak e)
    intro y z hyz
    exact ⟨⟨(y, z), hyz⟩, rfl, rfl⟩
  · intro y
    exact Finset.prod_pos fun i _ => pow_pos (hx i) (y i)
  · exact hκ
  · exact hδ
  · intro e f hef
    exact horder e.val.1 (N.source_mem e.val e.property)
      f.val.1 (N.source_mem f.val f.property) hef
  · exact hrate

end Problem326

end

end OAI
