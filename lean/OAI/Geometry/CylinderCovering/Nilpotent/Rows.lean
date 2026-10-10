import OAI.Geometry.RuledCovering.Main

namespace OAI

noncomputable section
open Set MeasureTheory
namespace RuledApproximation

lemma unitSquare_norm_le {z : Plane} (hz : z ∈ unitSquare) :
    ‖z‖ ≤ Real.sqrt 2 / 2 := by
  have h0 := abs_le.mp (hz 0)
  have h1 := abs_le.mp (hz 1)
  have hs0 : z 0 ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := by nlinarith
  have hs1 : z 1 ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := by nlinarith
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hn := Real.sqrt_nonneg (2 : ℝ)
  have he := norm_plane_sq z
  nlinarith [norm_nonneg z]

theorem nilpotent_sliding_rows (A : Plane →L[ℝ] Plane) (hA : A.comp A = 0) :
    ∃ R : Plane ≃ₗᵢ[ℝ] Plane, ∀ (q : Plane) (τ : ℝ), 0 < τ →
      ∀ (s : ℝ) (x : Plane), ∃ i j : ℤ, ∃ z ∈ unitSquare,
        let l := τ • R (vec2 i j)
        x = l + τ • R z + s • (A l + q) ∧
        ‖x - (l + s • (A l + q))‖ ≤ Real.sqrt 2 * τ / 2 := by
  obtain ⟨R,d,hR⟩ := nilpotent_frame A hA
  refine ⟨R, ?_⟩
  intro q τ hτ s x
  let u : Plane := τ⁻¹ • R.symm (x - s • q)
  obtain ⟨i,j,hi,hj⟩ := sliding_rows_cover (s*d) (u 0) (u 1)
  let z : Plane := vec2 (u 0 - ((i : ℝ) + s*d*j)) (u 1-j)
  have hz : z ∈ unitSquare := by
    intro k
    fin_cases k
    · exact hi
    · exact hj
  let l : Plane := τ • R (vec2 i j)
  have hul : τ • u = R.symm x - s • R.symm q := by
    dsimp [u]
    rw [smul_smul, mul_inv_cancel₀ hτ.ne', one_smul, map_sub, map_smul]
  have hal : R.symm (A l) = τ • vec2 (d * (j : ℝ)) 0 := by
    dsimp [l]
    rw [map_smul, map_smul, hR]
    rfl
  have hx : x = l + τ • R z + s • (A l + q) := by
    apply R.symm.injective
    simp only [map_add, map_smul, R.symm_apply_apply]
    rw [hal]
    have hxl : R.symm x = τ • u + s • R.symm q := by rw [hul]; abel
    rw [hxl]
    simp only [l, map_smul, R.symm_apply_apply]
    change τ • u + s • R.symm q =
      τ • vec2 i j + τ • z + s • (τ • vec2 (d * (j : ℝ)) 0 + R.symm q)
    ext k
    fin_cases k <;> simp [z,vec2] <;> ring
  refine ⟨i,j,z,hz,hx,?_⟩
  change ‖x - (l + s • (A l + q))‖ ≤ _
  have he : x - (l + s • (A l + q)) = τ • R z := by rw [hx]; abel
  rw [he, norm_smul, Real.norm_eq_abs, abs_of_pos hτ, R.norm_map]
  have hb := mul_le_mul_of_nonneg_left (unitSquare_norm_le hz) hτ.le
  nlinarith

end RuledApproximation

end

end OAI
