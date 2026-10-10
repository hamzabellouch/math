import OAI.Geometry.CylinderCovering.Nilpotent.Rows

namespace OAI

noncomputable section
open Set

namespace RuledApproximation

theorem translated_square_distance (R : Plane ≃ₗᵢ[ℝ] Plane)
    {τ : ℝ} (hτ : 0 ≤ τ) (l v : Plane) {x : Plane}
    (hx : x ∈ (fun z => l + τ • R z + v) '' unitSquare) :
    ‖x - (l + v)‖ ≤ Real.sqrt 2 * τ / 2 := by
  obtain ⟨z, hz, rfl⟩ := hx
  have he : l + τ • R z + v - (l + v) = τ • R z := by abel
  rw [he, norm_smul, Real.norm_eq_abs, abs_of_nonneg hτ, R.norm_map]
  have hb := mul_le_mul_of_nonneg_left (unitSquare_norm_le hz) hτ
  nlinarith

theorem nilpotent_sliding_rows_union (A : Plane →L[ℝ] Plane)
    (hA : A.comp A = 0) :
    ∃ R : Plane ≃ₗᵢ[ℝ] Plane,
      ∀ (q : Plane) (τ : ℝ), 0 < τ → ∀ s : ℝ,
        let center : ℤ → ℤ → Plane := fun i j => τ • R (vec2 i j)
        let tile : ℤ → ℤ → Set Plane := fun i j =>
          (fun z => center i j + τ • R z + s • (A (center i j) + q)) '' unitSquare
        (⋃ i : ℤ, ⋃ j : ℤ, tile i j) = univ ∧
          ∀ (i j : ℤ) (x : Plane), x ∈ tile i j →
            ‖x - (center i j + s • (A (center i j) + q))‖ ≤ Real.sqrt 2 * τ / 2 := by
  obtain ⟨R, hR⟩ := nilpotent_sliding_rows A hA
  refine ⟨R, ?_⟩
  intro q τ hτ s
  dsimp only
  constructor
  · apply eq_univ_of_forall
    intro x
    obtain ⟨i, j, z, hz, hx, _⟩ := hR q τ hτ s x
    exact mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨j, z, hz, hx.symm⟩⟩
  · intro i j x hx
    exact translated_square_distance R hτ.le _ _ hx

end RuledApproximation

end

end OAI
