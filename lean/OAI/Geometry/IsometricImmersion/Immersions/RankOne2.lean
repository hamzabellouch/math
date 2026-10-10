import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Basic.Real.Basic

namespace OAI

noncomputable section
open scoped Matrix

namespace SmoothLocal.Geometry

theorem two_by_two_rank_pos {A : Matrix (Fin 2) (Fin 2) ℝ} (hA : A ≠ 0) :
    0 < A.rank := by
  apply Nat.pos_of_ne_zero
  intro hz
  have hrange : LinearMap.range A.mulVecLin = ⊥ :=
    Submodule.finrank_eq_zero.mp hz
  have hmap : A.mulVecLin = 0 := LinearMap.range_eq_bot.mp hrange
  apply hA
  ext i j
  have hv := congrArg
    (fun f : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ) => f (Pi.single j 1) i) hmap
  change A i j = 0
  simpa only [Matrix.mulVecLin_apply, Matrix.mulVec_single_one,
    Matrix.col_apply, LinearMap.zero_apply, Pi.zero_apply] using hv

theorem two_by_two_rank_eq_one_of_ne_zero_det_eq_zero
    {A : Matrix (Fin 2) (Fin 2) ℝ} (hA : A ≠ 0) (hdet : A.det = 0) :
    A.rank = 1 := by
  have hdetL : LinearMap.det A.mulVecLin = 0 := by
    rw [← Matrix.toLin'_apply', LinearMap.det_toLin']
    exact hdet
  have hker : LinearMap.ker A.mulVecLin ≠ ⊥ :=
    LinearMap.det_eq_zero_iff_ker_ne_bot.mp hdetL
  have hkpos : 0 < Module.finrank ℝ (LinearMap.ker A.mulVecLin) := by
    apply Nat.pos_of_ne_zero
    intro hz
    exact hker (Submodule.finrank_eq_zero.mp hz)
  have hnull : A.rank + Module.finrank ℝ (LinearMap.ker A.mulVecLin) = 2 := by
    simpa [Matrix.rank] using A.mulVecLin.finrank_range_add_finrank_ker
  have hrpos := two_by_two_rank_pos hA
  omega

theorem two_by_two_rank_eq_one_iff (A : Matrix (Fin 2) (Fin 2) ℝ) :
    A.rank = 1 ↔ A ≠ 0 ∧ A.det = 0 := by
  constructor
  · intro hr
    refine ⟨?_, ?_⟩
    · intro hz
      simp only [hz, Matrix.rank_zero] at hr
      omega
    · by_contra hd
      have hfull := Matrix.rank_of_det_ne_zero hd
      simp only [Fintype.card_fin] at hfull
      omega
  · rintro ⟨hA, hd⟩
    exact two_by_two_rank_eq_one_of_ne_zero_det_eq_zero hA hd

end SmoothLocal.Geometry

end

end OAI
