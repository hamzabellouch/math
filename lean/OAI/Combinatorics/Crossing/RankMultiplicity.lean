import OAI.Combinatorics.Crossing.PolynomialMinors
import Mathlib.LinearAlgebra.Matrix.Rank

namespace OAI

noncomputable section
namespace Zarankiewicz
open Polynomial
open scoped BigOperators
variable {κ : Type*} [Fintype κ] [DecidableEq κ]

theorem rank_deficiency_pow_dvd_det (M : Matrix κ κ ℝ[X]) (t : ℝ) :
    (X-C t)^(Fintype.card κ - ((evalRingHom t).mapMatrix M).rank) ∣ M.det := by
  classical
  let E : Matrix κ κ ℝ := (evalRingHom t).mapMatrix M
  obtain ⟨V, U, e, hV, hU, he⟩ := Matrix.exists_rank_normal_form E
  let T : Matrix κ κ ℝ[X] := C.mapMatrix V * M * C.mapMatrix U
  let emb : Fin (Fintype.card κ-E.rank) ↪ κ :=
    ⟨fun i => e.symm (Sum.inr i), fun i j h => Sum.inr_injective (e.symm.injective h)⟩
  let S : Finset κ := Finset.univ.map emb
  have hS : S.card = Fintype.card κ-E.rank := by simp [S]
  have evalC (A : Matrix κ κ ℝ) : (evalRingHom t).mapMatrix (C.mapMatrix A) = A := by
    funext i j
    exact eval_C
  have hT : (evalRingHom t).mapMatrix T = V * E * U := by
    simp only [T, map_mul, evalC]
    rfl
  have hz : ∀ j ∈ S, ∀ i, (T i j).eval t = 0 := by
    intro j hj i
    obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hj
    change ((evalRingHom t).mapMatrix T) i (emb a) = 0
    rw [hT, he]
    change (Matrix.fromBlocks 1 0 0 0) (e i) (e (e.symm (Sum.inr a))) = 0
    rw [Equiv.apply_symm_apply]
    cases e i <;> rfl
  have hd := pow_card_dvd_det_of_columns_vanish T t S hz
  rw [hS] at hd
  have hdet : T.det = C V.det * M.det * C U.det := by
    dsimp only [T]
    rw [Matrix.det_mul, Matrix.det_mul, ← RingHom.map_det, ← RingHom.map_det]
  rw [hdet] at hd
  have hu : IsUnit (C U.det : ℝ[X]) := isUnit_C.mpr ((Matrix.isUnit_iff_isUnit_det U).mp hU)
  have hv : IsUnit (C V.det : ℝ[X]) := isUnit_C.mpr ((Matrix.isUnit_iff_isUnit_det V).mp hV)
  exact hv.dvd_mul_left.mp (hu.dvd_mul_right.mp hd)

theorem pow_dvd_det_of_rank_le (M : Matrix κ κ ℝ[X]) (t : ℝ) (q : ℕ)
    (hq : q + ((evalRingHom t).mapMatrix M).rank ≤ Fintype.card κ) :
    (X-C t)^q ∣ M.det := by
  apply dvd_trans _ (rank_deficiency_pow_dvd_det M t)
  exact pow_dvd_pow _ (by omega)

end Zarankiewicz

end

end OAI
