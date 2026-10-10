import OAI.MeasureTheory.Falconer.Geometry.ProjectionRows
import Mathlib.Data.Int.Interval

namespace OAI

/-! Actual scale-delta covering cells for parameter projections. For a
family through a row, at most seven cells per row point are needed. -/
namespace Falconer
attribute [local instance] Classical.propDecidable

noncomputable def projectionCells (δ y : ℝ) (T : Finset (Space 2)) : Finset ℤ :=
  T.image fun l => ⌊lineParameterProjection y l/δ⌋

theorem floor_div_near {δ u v : ℝ} (hδ : 0 < δ) (huv : |u-v| ≤ 2*δ) :
    |⌊u/δ⌋-⌊v/δ⌋| ≤ (3 : ℤ) := by
  have hd : |u/δ-v/δ| ≤ 2 := by
    rw [← sub_div,abs_div,abs_of_pos hδ]
    exact (div_le_iff₀ hδ).2 huv
  have hu0 := Int.floor_le (u/δ)
  have hu1 := Int.lt_floor_add_one (u/δ)
  have hv0 := Int.floor_le (v/δ)
  have hv1 := Int.lt_floor_add_one (v/δ)
  have he : |(⌊u/δ⌋ : ℝ)-(⌊v/δ⌋ : ℝ)| ≤ 3 := by
    rw [abs_le] at hd ⊢
    constructor <;> linarith
  exact_mod_cast he

theorem projectionCells_mono (δ y : ℝ) {T U : Finset (Space 2)} (hTU : T ⊆ U) :
    projectionCells δ y T ⊆ projectionCells δ y U := Finset.image_subset_image hTU

theorem projectionCells_row_count {δ y : ℝ} (hδ : 0 < δ) {P : Finset (Space 2)}
    (hrow : ∀ x ∈ P, x 0 = y) (T : Space 2 → Finset (Space 2))
    (hchart : ∀ x ∈ P, InBoundedLineChart (T x))
    (hinc : ∀ x ∈ P, ∀ l ∈ T x, TubeIncident δ x l) :
    (projectionCells δ y (P.biUnion T)).card ≤ 7*P.card := by
  classical
  let S := fun x : Space 2 => Finset.Icc (⌊x 1/δ⌋-3) (⌊x 1/δ⌋+3)
  have hsub : projectionCells δ y (P.biUnion T) ⊆ P.biUnion S := by
    intro k hk
    obtain ⟨l,hl,rfl⟩ := Finset.mem_image.mp hk
    obtain ⟨x,hx,hxl⟩ := Finset.mem_biUnion.mp hl
    apply Finset.mem_biUnion.mpr
    refine ⟨x,hx,?_⟩
    have he := tube_projection_near hδ.le (hchart x hx l hxl).1 (hinc x hx l hxl)
    rw [hrow x hx] at he
    have hb := floor_div_near hδ he
    rw [abs_le] at hb
    apply Finset.mem_Icc.mpr
    dsimp [S]
    omega
  have hcard (x : Space 2) : (S x).card = 7 := by
    dsimp [S]
    rw [Int.card_Icc]
    have he : ⌊x 1/δ⌋+3+1-(⌊x 1/δ⌋-3) = (7 : ℤ) := by omega
    rw [he]
    rfl
  calc
    _ ≤ (P.biUnion S).card := Finset.card_le_card hsub
    _ ≤ ∑ x ∈ P, (S x).card := Finset.card_biUnion_le
    _ = 7*P.card := by simp [hcard,Nat.mul_comm]

theorem projectionCells_cell_contains {δ y : ℝ} (hδ : 0 < δ)
    {T : Finset (Space 2)} {l : Space 2} (hl : l ∈ T) :
    ∃ k ∈ projectionCells δ y T,
      (k : ℝ)*δ ≤ lineParameterProjection y l ∧
      lineParameterProjection y l < ((k : ℝ)+1)*δ := by
  refine ⟨⌊lineParameterProjection y l/δ⌋,Finset.mem_image.mpr ⟨l,hl,rfl⟩,?_,?_⟩
  · exact (le_div_iff₀ hδ).1 (Int.floor_le _)
  · exact (div_lt_iff₀ hδ).1 (Int.lt_floor_add_one _)

end Falconer

end OAI
