import OAI.Geometry.HeilbronnTriangle.PlaneRowTransport
import OAI.Geometry.HeilbronnTriangle.LatticePacking

namespace OAI


noncomputable section

namespace Problem355.PlaneRowTransport

open Matrix IntegralPlaneLattice

theorem card_matricesIn_le_of_minor
    (x z : Fin 3 → ℤ) (hz : x ⬝ᵥ z = 1)
    (Γ : Submodule ℤ (plane x)) [DiscreteTopology Γ] [IsZLattice ℝ Γ]
    (S : Finset (MatricesIn x Γ)) (R : ℝ) (hR : 0 ≤ R)
    (hnorm : ∀ A ∈ S, ∀ i, ‖castVec (A.val.val i)‖ ≤ R)
    (hminor : ∀ A ∈ S, ∃ i j s t : Fin 3,
      A.val.val i s * A.val.val j t - A.val.val i t * A.val.val j s ≠ 0) :
    (S.card : ℝ) ≤ (9 * Real.pi * R ^ 2 / ZLattice.covolume Γ) ^ 3 := by
  classical
  rw [← card_rowsIn_image x Γ S]
  apply LatticePacking.plane_spanning_triples_card_le (plane_finrank x z hz) Γ
    (S.image (rowsIn x Γ)) R hR
  · intro a ha i
    obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp ha
    exact hnorm A hA i
  · intro a ha
    obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨i, j, s, t, h⟩ := hminor A hA
    exact ⟨i, j, rows_pair_linearIndependent_of_minor x A.val i j s t h⟩

theorem card_matricesIn_le_of_projected_columns_ne
    (x z : Fin 3 → ℤ) (hz : x ⬝ᵥ z = 1)
    (Γ : Submodule ℤ (plane x)) [DiscreteTopology Γ] [IsZLattice ℝ Γ]
    (S : Finset (MatricesIn x Γ)) (N : ℝ) (hN : 0 ≤ N)
    (hcoord : ∀ A ∈ S, ∀ i j, |(A.val.val i j : ℝ)| ≤ 2 * N)
    (hdistinct : ∀ A ∈ S, ∃ s t : Fin 3,
      A.val.val 2 s ≠ 0 ∧ A.val.val 2 t ≠ 0 ∧
      projectedColumn A.val.val s ≠ projectedColumn A.val.val t) :
    (S.card : ℝ) ≤
      (9 * Real.pi * (4 * N) ^ 2 / ZLattice.covolume Γ) ^ 3 := by
  apply card_matricesIn_le_of_minor x z hz Γ S (4 * N) (by positivity)
  · intro A hA i
    exact norm_rows_le_four_mul x A.val i hN (hcoord A hA i)
  · intro A hA
    obtain ⟨s, t, hs, ht, hne⟩ := hdistinct A hA
    obtain ⟨i, _, hi⟩ := exists_minor_of_projected_columns_ne A.val.val s t hs ht hne
    exact ⟨i, 2, s, t, hi⟩

end Problem355.PlaneRowTransport

end

end OAI
