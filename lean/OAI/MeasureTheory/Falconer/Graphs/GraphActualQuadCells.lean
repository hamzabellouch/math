import OAI.MeasureTheory.Falconer.Graphs.GraphNonedgeIndexCount
import OAI.MeasureTheory.Falconer.Estimates.ProfileMassError

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

def graphQuadPath (q : GraphCellQuadIndex) (l : Fin 4) : CellPath :=
  ![q.1.1,q.1.2,q.2.1,q.2.2] l

noncomputable def graphQuadCells (Q : Fin 4 → DyadicSquare) (q : GraphCellQuadIndex) (l : Fin 4) : DyadicSquare :=
  (Q l).descendant (graphQuadPath q l)

theorem graphQuadPath_length {p : ℕ} {q : GraphCellQuadIndex} (hq : q ∈ graphCellQuadIndices p) (l : Fin 4) :
    (graphQuadPath q l).length = p := by
  simp only [graphCellQuadIndices,Finset.product_eq_sprod,Finset.mem_product,mem_dyadicPaths] at hq
  fin_cases l
  · exact hq.1.1
  · exact hq.1.2
  · exact hq.2.1
  · exact hq.2.2

theorem graphQuadCells_pos (Q : Fin 4 → DyadicSquare) (hQ : ∀ l, 0 < (Q l).side)
    (q : GraphCellQuadIndex) (l : Fin 4) : 0 < (graphQuadCells Q q l).side := by
  rw [graphQuadCells,DyadicSquare.descendant_side]
  exact div_pos (hQ l) (by positivity)

theorem graphQuadCells_side_le (Q : Fin 4 → DyadicSquare) (hQ : ∀ l, (Q l).side ≤ 1)
    {p : ℕ} {q : GraphCellQuadIndex} (hq : q ∈ graphCellQuadIndices p) (l : Fin 4) :
    (graphQuadCells Q q l).side ≤ (2:ℝ)^(-(p:ℝ)) := by
  rw [graphQuadCells,DyadicSquare.descendant_side,graphQuadPath_length hq l,
    Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2),Real.rpow_natCast]
  simpa only [one_div] using div_le_div_of_nonneg_right (hQ l) (by positivity : (0:ℝ) ≤ 2^p)

theorem graphQuadCells_profile_mass_le
    (Q : Fin 4 → DyadicSquare) (ρ : Fin 4 → Measure Plane) (N B : ℕ)
    (δ lam : ℝ) (mass : Fin 4 → ℝ → ℝ)
    (hd : ∀ l, RegularizedProfileData (Q l) (ρ l) N B δ lam (mass l))
    {p : ℕ} (hp : p ≤ N) {q : GraphCellQuadIndex} (hq : q ∈ graphCellQuadIndices p) (l : Fin 4) :
    (ρ l (graphQuadCells Q q l).carrier).toReal / ((2:ℝ)^N)^(-mass l p) ≤ ((2:ℝ)^N)^(3*lam) :=
  (hd l).normalized_cell_mass_le hp (graphQuadPath_length hq l)

end PlanarFalconer

end OAI
