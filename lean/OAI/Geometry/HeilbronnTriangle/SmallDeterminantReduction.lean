import Mathlib

namespace OAI


namespace Problem355.SmallDeterminantReduction

theorem cast_ne_zero_of_abs_lt (q : ℕ) (t : ℤ) (ht : t ≠ 0)
    (hsmall : |t| < (q : ℤ)) : (t : ZMod q) ≠ 0 := by
  intro hzero
  have hd := (ZMod.intCast_zmod_eq_zero_iff_dvd t q).mp hzero
  have hdabs : (q : ℤ) ∣ |t| := by
    obtain ⟨z, hz⟩ := hd
    refine ⟨|z|, ?_⟩
    rw [hz, abs_mul, abs_of_nonneg (Int.natCast_nonneg q)]
  have hle : (q : ℤ) ≤ |t| := Int.le_of_dvd (abs_pos.mpr ht) hdabs
  omega

theorem reduction_det_ne_zero {n : Type*} [Fintype n] [DecidableEq n]
    (q : ℕ) (A : Matrix n n ℤ) (hdet : A.det ≠ 0)
    (hsmall : |A.det| < (q : ℤ)) :
    (A.map (Int.castRingHom (ZMod q))).det ≠ 0 := by
  change ((Int.castRingHom (ZMod q)).mapMatrix A).det ≠ 0
  rw [← (Int.castRingHom (ZMod q)).map_det]
  exact cast_ne_zero_of_abs_lt q A.det hdet hsmall

theorem reduction_columns_linearIndependent {n : Type*} [Fintype n] [DecidableEq n]
    (q : ℕ) [Fact q.Prime] (A : Matrix n n ℤ) (hdet : A.det ≠ 0)
    (hsmall : |A.det| < (q : ℤ)) :
    LinearIndependent (ZMod q) (fun j i => (A i j : ZMod q)) := by
  exact Matrix.linearIndependent_cols_of_det_ne_zero
    (reduction_det_ne_zero q A hdet hsmall)

theorem reduction_columns_affineIndependent {n : Type*} [Fintype n] [DecidableEq n]
    (q : ℕ) [Fact q.Prime] (A : Matrix n n ℤ) (hdet : A.det ≠ 0)
    (hsmall : |A.det| < (q : ℤ)) :
    AffineIndependent (ZMod q) (fun j i => (A i j : ZMod q)) :=
  (reduction_columns_linearIndependent q A hdet hsmall).affineIndependent

end Problem355.SmallDeterminantReduction

end OAI
