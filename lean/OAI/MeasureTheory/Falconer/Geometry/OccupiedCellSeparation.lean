import OAI.MeasureTheory.Falconer.Radial.OccupiedRadialTree

namespace OAI

/-! # Separation extends from the full source set to sufficiently small occupied cells -/

namespace Falconer
open Set MeasureTheory
variable {d : ℕ}
attribute [local instance] Classical.propDecidable

theorem exists_mem_cell_source (μ : Measure (Space d)) (A C : Set (Space d))
    (hA : μ Aᶜ = 0) (hC : 0 < μ C) : ∃ z ∈ C, z ∈ A := by
  by_contra hn
  have hsub : C ⊆ Aᶜ := by
    intro z hz hzA
    exact hn ⟨z,hz,hzA⟩
  exact (not_le_of_gt hC) ((measure_mono hsub).trans_eq hA)

theorem occupied_cell_separation (Q : DyadicCube d) (hQ : 0 < Q.side)
    (μ : Measure (Space d)) (A B : Set (Space d)) (hA : μ Aᶜ = 0)
    {s : ℝ} (hsep : ∀ z ∈ A, ∀ x ∈ B, s ≤ ‖z-x‖)
    {n : ℕ} (hsmall : Real.sqrt d*(Q.side/(2:ℝ)^n) ≤ s/2)
    {P : List (Fin d → Bool)} (hP : P ∈ Q.occupiedPaths μ n) :
    ∀ x ∈ B, ∀ y ∈ (Q.descendant P).carrier, s/2 ≤ ‖y-x‖ := by
  obtain ⟨z,hz,hzA⟩ := exists_mem_cell_source μ A (Q.descendant P).carrier hA
    (Finset.mem_filter.mp hP).2
  intro x hx y hy
  have hd := Q.occupied_diameter_bound hQ μ hP hz hy
  have ht := norm_sub_le_norm_sub_add_norm_sub z y x
  have hs := hsep z hzA x hx
  linarith

theorem occupied_cell_center_separation (Q : DyadicCube d) (hQ : 0 < Q.side)
    (μ : Measure (Space d)) (A B : Set (Space d)) (hA : μ Aᶜ = 0)
    {s : ℝ} (hsep : ∀ z ∈ A, ∀ x ∈ B, s ≤ ‖z-x‖)
    {n : ℕ} (hsmall : Real.sqrt d*(Q.side/(2:ℝ)^n) ≤ s/2)
    {P : List (Fin d → Bool)} (hP : P ∈ Q.occupiedPaths μ n) :
    ∀ x ∈ B, s/2 ≤ ‖(Q.descendant P).center-x‖ := by
  intro x hx
  exact occupied_cell_separation Q hQ μ A B hA hsep hsmall hP x hx _
    ((Q.descendant P).center_mem (Q.descendant_side_pos hQ P))

end Falconer

end OAI
