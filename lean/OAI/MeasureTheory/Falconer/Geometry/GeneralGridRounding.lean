import OAI.MeasureTheory.Falconer.Geometry.GeneralTransverseGrid
import OAI.MeasureTheory.Falconer.Geometry.TripleGridRounding

namespace OAI

/-! # Bounded original point sets admit finite transverse lattice approximations -/

namespace Falconer
open Set Metric
variable {n : ℕ}

noncomputable def euclideanRound (δ : ℝ) (x : Space (n+1)) : Fin (n+1) → ℤ :=
  fun j => round (x j/δ)

theorem euclideanRound_distance {δ : ℝ} (hδ : 0 < δ) (x : Space (n+1)) :
    dist x (euclideanIntegerGrid δ (euclideanRound δ x)) ≤ ((n+1:ℕ):ℝ)*δ/2 := by
  rw [dist_eq_norm]
  have hh := coordinate_norm_le_card_mul (x-euclideanIntegerGrid δ (euclideanRound δ x))
    (r := δ/2) (fun i => round_mesh_error hδ (x i))
  nlinarith

noncomputable def integerGridBox (n L : ℕ) : Finset (Fin (n+1) → ℤ) :=
  Fintype.piFinset (fun _ => Finset.Icc (-(L:ℤ)) (L:ℤ))

theorem euclideanRound_mem_box {δ R : ℝ} (hδ : 0 < δ) (L : ℕ)
    (hL : R/δ+1 ≤ (L:ℝ)) (x : Space (n+1)) (hx : ‖x‖ ≤ R) :
    euclideanRound δ x ∈ integerGridBox n L := by
  apply Fintype.mem_piFinset.mpr
  intro i
  exact Finset.mem_Icc.mpr (round_bound hδ L hL (x i) ((PiLp.norm_apply_le x i).trans hx))

noncomputable def roundedEuclideanGrid (E : Set (Space (n+1))) (δ : ℝ) (L : ℕ) :
    Finset (Fin (n+1) → ℤ) := by
  classical
  exact (integerGridBox n L).filter (fun z => ∃ x ∈ E, euclideanRound δ x = z)

theorem roundedEuclideanGrid_mem {E : Set (Space (n+1))} {δ R : ℝ} (hδ : 0 < δ)
    (L : ℕ) (hL : R/δ+1 ≤ (L:ℝ)) (hE : ∀ x ∈ E, ‖x‖ ≤ R)
    {x : Space (n+1)} (hx : x ∈ E) : euclideanRound δ x ∈ roundedEuclideanGrid E δ L := by
  classical
  exact Finset.mem_filter.mpr ⟨euclideanRound_mem_box hδ L hL x (hE x hx),x,hx,rfl⟩

theorem roundedEuclideanGrid_original {E : Set (Space (n+1))} {δ : ℝ} {L : ℕ}
    {z : Fin (n+1) → ℤ} (hz : z ∈ roundedEuclideanGrid E δ L) :
    ∃ x ∈ E, euclideanRound δ x = z := by
  classical
  exact (Finset.mem_filter.mp hz).2

end Falconer

end OAI
