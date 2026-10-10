import OAI.MeasureTheory.Falconer.Angular.AngularNearNeighbors

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ComplexConjugate
attribute [local instance] Classical.propDecidable

noncomputable def angularPairTerm (U V : CellPath → ℂ) (row col : CellPath × CellPath) : ℂ :=
  (U row.1 * conj (U col.1)) * (V row.2 * conj (V col.2))

noncomputable def angularRestrictedSum (C : Finset (CellPath × CellPath))
    (G : (CellPath × CellPath) → (CellPath × CellPath) → Prop)
    (U V : CellPath → ℂ) : ℂ :=
  ∑ row ∈ C, ∑ col ∈ C, if G row col then angularPairTerm U V row col else 0

theorem angularRestrictedSum_complement (C : Finset (CellPath × CellPath))
    (G : (CellPath × CellPath) → (CellPath × CellPath) → Prop) (U V : CellPath → ℂ) :
    angularRestrictedSum C G U V + angularRestrictedSum C (fun row col => ¬ G row col) U V =
      ∑ row ∈ C, ∑ col ∈ C, angularPairTerm U V row col := by
  simp only [angularRestrictedSum,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro row _
  apply Finset.sum_congr rfl
  intro col _
  by_cases h : G row col <;> simp [h]

theorem angularRestrictedSum_schur (C : Finset (CellPath × CellPath))
    (G : (CellPath × CellPath) → (CellPath × CellPath) → Prop)
    (U V : CellPath → ℂ) (d : ℝ)
    (hr : ∀ row ∈ C, ((C.filter (G row)).card : ℝ) ≤ d)
    (hc : ∀ col ∈ C, ((C.filter (fun row => G row col)).card : ℝ) ≤ d) :
    ‖angularRestrictedSum C G U V‖ ≤ d * ∑ row ∈ C, ‖U row.1‖^2*‖V row.2‖^2 := by
  classical
  have hh := finset_bipartite_schur C C G
    (fun row => ‖U row.1‖*‖V row.2‖) (fun row => ‖U row.1‖*‖V row.2‖) d hr hc
  have hn : ‖angularRestrictedSum C G U V‖ ≤
      ∑ row ∈ C, ∑ col ∈ C, if G row col then
        (‖U row.1‖*‖V row.2‖)*(‖U col.1‖*‖V col.2‖) else 0 := by
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro row _
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro col _
    by_cases hg : G row col
    · simp only [hg,↓reduceIte,angularPairTerm,norm_mul,Complex.norm_conj]
      exact le_of_eq (by ring)
    · simp [hg]
  apply hn.trans (hh.trans_eq ?_)
  simp only [mul_pow]
  ring

theorem angularNearSum_bound (Q₁ Q₂ : DyadicSquare) (hQ₁ : Q₁.side = 1) (hQ₂ : Q₂.side = 1)
    (p : ℕ) (C : Finset (CellPath × CellPath))
    (hC : C ⊆ (dyadicPaths p) ×ˢ (dyadicPaths p)) (U V : CellPath → ℂ) :
    ‖angularRestrictedSum C (angularNear Q₁ Q₂ p) U V‖ ≤
      3748096 * ∑ row ∈ C, ‖U row.1‖^2*‖V row.2‖^2 := by
  apply angularRestrictedSum_schur
  · intro row _
    exact angularNear_degree Q₁ Q₂ hQ₁ hQ₂ p C hC row
  · intro col _
    simp_rw [angularNear_symm Q₁ Q₂ p _ col]
    exact angularNear_degree Q₁ Q₂ hQ₁ hQ₂ p C hC col

end PlanarFalconer

end OAI
