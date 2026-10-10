import OAI.Geometry.HeilbronnTriangle.IntegralPlaneLattice

namespace OAI


noncomputable section

namespace Problem355.IntegralPlaneRows

open Matrix Module IntegralPlaneLattice

def rows (x : Fin 3 → ℤ) (A : Matrix (Fin 3) (Fin 3) ℤ)
    (hAx : A.mulVec x = 0) : Fin 3 → lattice x := fun i =>
  kernelMap x ⟨A i, by
    change x ⬝ᵥ A i = 0
    rw [dotProduct_comm]
    exact congr_fun hAx i⟩

@[simp] theorem rows_apply (x : Fin 3 → ℤ) (A : Matrix (Fin 3) (Fin 3) ℤ)
    (hAx : A.mulVec x = 0) (i j : Fin 3) :
    (((rows x A hAx i : plane x) : Ambient) j) = (A i j : ℝ) := rfl

theorem finrank_span_rows (x : Fin 3 → ℤ) (A : Matrix (Fin 3) (Fin 3) ℤ)
    (hAx : A.mulVec x = 0) :
    finrank ℝ (Submodule.span ℝ (Set.range (fun i => (rows x A hAx i : plane x)))) =
      (A.map (Int.castRingHom ℝ)).rank := by
  let S := Submodule.span ℝ (Set.range (fun i => (rows x A hAx i : plane x)))
  let e : Ambient ≃ₗ[ℝ] (Fin 3 → ℝ) := WithLp.linearEquiv 2 ℝ _
  have hmap : (S.map (plane x).subtype).map e.toLinearMap =
      Submodule.span ℝ (Set.range (A.map (Int.castRingHom ℝ)).row) := by
    simp only [S, Submodule.map_span, ← Set.range_comp]
    rfl
  change finrank ℝ S = _
  calc
    finrank ℝ S = finrank ℝ (S.map (plane x).subtype) :=
      ((plane x).finrank_map_subtype_eq S).symm
    _ = finrank ℝ ((S.map (plane x).subtype).map e.toLinearMap) :=
      (e.finrank_map_eq _).symm
    _ = (A.map (Int.castRingHom ℝ)).rank := by
      rw [hmap, ← Matrix.rank_eq_finrank_span_row]

theorem span_rows_eq_top (x z : Fin 3 → ℤ) (hz : x ⬝ᵥ z = 1)
    (A : Matrix (Fin 3) (Fin 3) ℤ) (hAx : A.mulVec x = 0)
    (hrank : (A.map (Int.castRingHom ℝ)).rank = 2) :
    Submodule.span ℝ (Set.range (fun i => (rows x A hAx i : plane x))) = ⊤ := by
  apply Submodule.eq_top_of_finrank_eq
  rw [finrank_span_rows, hrank, plane_finrank x z hz]

theorem real_rank_eq_two_of_minor (x z : Fin 3 → ℤ) (hz : x ⬝ᵥ z = 1)
    (A : Matrix (Fin 3) (Fin 3) ℤ) (hAx : A.mulVec x = 0)
    (r c : Fin 2 → Fin 3) (hm : (A.submatrix r c).det ≠ 0) :
    (A.map (Int.castRingHom ℝ)).rank = 2 := by
  let B := A.map (Int.castRingHom ℝ)
  have hmR : (B.submatrix r c).det ≠ 0 := by
    change ((A.map (Int.castRingHom ℝ)).submatrix r c).det ≠ 0
    rw [Matrix.submatrix_map]
    change ((Int.castRingHom ℝ).mapMatrix (A.submatrix r c)).det ≠ 0
    rw [← RingHom.map_det]
    change ((A.submatrix r c).det : ℝ) ≠ 0
    exact_mod_cast hm
  have hr : (B.submatrix r c).rank = 2 := by
    simpa using Matrix.rank_of_isUnit (B.submatrix r c)
      ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hmR))
  have hlo : 2 ≤ B.rank := by
    have h := B.rank_submatrix_le r c
    rwa [hr] at h
  have hhi : B.rank ≤ 2 := by
    rw [← finrank_span_rows x A hAx]
    simpa only [plane_finrank x z hz] using
      (Submodule.finrank_le
        (Submodule.span ℝ (Set.range (fun i => (rows x A hAx i : plane x)))))
  exact le_antisymm hhi hlo

theorem span_rows_eq_top_of_minor (x z : Fin 3 → ℤ) (hz : x ⬝ᵥ z = 1)
    (A : Matrix (Fin 3) (Fin 3) ℤ) (hAx : A.mulVec x = 0)
    (r c : Fin 2 → Fin 3) (hm : (A.submatrix r c).det ≠ 0) :
    Submodule.span ℝ (Set.range (fun i => (rows x A hAx i : plane x))) = ⊤ :=
  span_rows_eq_top x z hz A hAx (real_rank_eq_two_of_minor x z hz A hAx r c hm)

end Problem355.IntegralPlaneRows

end

end OAI
