import OAI.NumberTheory.DukePrimeDegree.Geometry.RootStableHolonomy
import OAI.NumberTheory.DukePrimeDegree.Dynamics.RootShearing

namespace OAI

/-!
# The three-root commutator rectangle

The two orders of the adjacent root translations differ by the product
of their parameters in the long root. Under a diagonal flow neutral on
the long root and contracting the first root, this is the exact limit.
-/

noncomputable section
open Set Filter Matrix
open scoped Topology

namespace DukePrimeDegree
open PrimeDegreePackets

lemma adjacent_root_conjugation
    {n : ℕ} {a b c : Fin n} (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    (r s : ℝ) :
    Matrix.SpecialLinearGroup.transvection hbc (-s) *
      Matrix.SpecialLinearGroup.transvection hab r *
      Matrix.SpecialLinearGroup.transvection hbc s =
    Matrix.SpecialLinearGroup.transvection hab r *
      Matrix.SpecialLinearGroup.transvection hac (r * s) := by
  apply Subtype.ext
  change ((1 : Matrix (Fin n) (Fin n) ℝ) + Matrix.single b c (-s)) *
      (1 + Matrix.single a b r) * (1 + Matrix.single b c s) =
    (1 + Matrix.single a b r) * (1 + Matrix.single a c (r * s))
  have h1 : Matrix.single b c (-s) * Matrix.single a b r = 0 :=
    Matrix.single_mul_single_of_ne (c := -s) (h := hac.symm) (i := b) (j := c) (k := a) (d := r)
  have h2 : Matrix.single b c (-s) * Matrix.single b c s = 0 :=
    Matrix.single_mul_single_of_ne (c := -s) (h := hbc.symm) (i := b) (j := c) (k := b) (d := s)
  have h3 : Matrix.single a b r * Matrix.single a c (r * s) = 0 :=
    Matrix.single_mul_single_of_ne (c := r) (h := hab.symm) (i := a) (j := b) (k := a) (d := r * s)
  simp only [mul_add, add_mul, one_mul, mul_one, h1, h2, h3,
    Matrix.single_mul_single_same, add_zero]
  rw [← Matrix.single_neg]
  abel

theorem adjacent_root_conjugate_limit
    {n : ℕ} {a b c : Fin n} (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    (ell : Fin n → ℝ) (hell : ∑ k, ell k = 0)
    (hneut : ell a = ell c) (hneg : ell a - ell b < 0) (r s : ℝ) :
    Tendsto (fun t : ℝ => diagonalOneParameter ell hell t *
      (Matrix.SpecialLinearGroup.transvection hbc (-s) *
        Matrix.SpecialLinearGroup.transvection hab r *
        Matrix.SpecialLinearGroup.transvection hbc s) * diagonalOneParameter ell hell (-t))
      atTop (𝓝 (Matrix.SpecialLinearGroup.transvection hac (r * s))) := by
  have he (t : ℝ) : diagonalOneParameter ell hell t *
      (Matrix.SpecialLinearGroup.transvection hbc (-s) *
        Matrix.SpecialLinearGroup.transvection hab r *
        Matrix.SpecialLinearGroup.transvection hbc s) * diagonalOneParameter ell hell (-t) =
      (diagonalOneParameter ell hell t * Matrix.SpecialLinearGroup.transvection hab r *
        diagonalOneParameter ell hell (-t)) * Matrix.SpecialLinearGroup.transvection hac (r * s) := by
    rw [adjacent_root_conjugation hab hbc hac]
    have hn := diagonal_conjugation_transvection ell hell hac (r * s) t
    simp only [hneut, sub_self, zero_mul, Real.exp_zero, one_mul] at hn
    calc
      _ = (diagonalOneParameter ell hell t * Matrix.SpecialLinearGroup.transvection hab r *
            diagonalOneParameter ell hell (-t)) *
          (diagonalOneParameter ell hell t * Matrix.SpecialLinearGroup.transvection hac (r * s) *
            diagonalOneParameter ell hell (-t)) := by
        rw [diagonalOneParameter_neg]
        group
      _ = _ := by rw [hn]
  simp_rw [he]
  simpa only [one_mul] using
    (root_conjugate_tendsto_one hab ell hell hneg r).mul_const
      (Matrix.SpecialLinearGroup.transvection hac (r * s))

end DukePrimeDegree

end

end OAI
