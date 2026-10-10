import OAI.Analysis.PureInfiniteness.JointSpectralQuadratic
import OAI.Analysis.PureInfiniteness.RectangularAlgebra
import OAI.Analysis.JiangSu.Nonunital.MatrixDiagonal

namespace OAI

/-! The sampled row error has a bound independent of the number of cells.
The coefficient diagonal contributes only its uniform norm bound. -/

noncomputable section
open scoped BigOperators ComplexOrder

namespace WeakPureInfiniteness

variable {A J : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [Fintype J]

omit [PartialOrder A] [StarOrderedRing A] in
lemma real_sample_square (x y : A) (hxy : Commute x y) (t : ℝ) :
    (x * y - (t : ℂ) • y) * (x * y - (t : ℂ) • y) =
      x * x * (y * y) - ((2 * t : ℝ) : ℂ) • (x * (y * y)) +
        ((t ^ 2 : ℝ) : ℂ) • (y * y) := by
  have h₁ : (x * y) * (x * y) = x * x * (y * y) := by
    calc
      _ = x * (y * x) * y := by simp only [mul_assoc]
      _ = x * (x * y) * y := by rw [hxy.eq.symm]
      _ = _ := by simp only [mul_assoc]
  have h₂ : y * (x * y) = x * (y * y) := by rw [← mul_assoc, hxy.eq.symm, mul_assoc]
  rw [mul_sub, sub_mul, sub_mul, smul_mul_assoc, mul_smul_comm,
    mul_smul_comm, smul_mul_assoc, smul_smul, h₁, h₂]
  rw [show ((2 * t : ℝ) : ℂ) = (t : ℂ) + (t : ℂ) by push_cast; ring, add_smul]
  simp only [mul_assoc, pow_two, Complex.ofReal_mul]
  abel

lemma sampled_error_square (a f : A) (ha : IsSelfAdjoint a) (hf : 0 ≤ f)
    (haf : Commute a f) (t : ℝ) :
    let e := a * CFC.sqrt f - (t : ℂ) • CFC.sqrt f
    e * star e = sampledQuadraticError a f t := by
  have hs : IsSelfAdjoint (CFC.sqrt f) := (CFC.sqrt_nonneg f).isSelfAdjoint
  have hc : Commute a (CFC.sqrt f) := (haf.symm.cfcₙ_nnreal _).symm
  have he : IsSelfAdjoint (a * CFC.sqrt f - (t : ℂ) • CFC.sqrt f) := by
    have hp : IsSelfAdjoint (a * CFC.sqrt f) := by
      change star (a * CFC.sqrt f) = a * CFC.sqrt f
      rw [star_mul, hs.star_eq, ha.star_eq, ← hc.eq]
    have ht : IsSelfAdjoint (t : ℂ) := by simp [isSelfAdjoint_iff]
    exact hp.sub (ht.smul hs)
  dsimp only
  rw [he.star_eq, real_sample_square a (CFC.sqrt f) hc t, CFC.sqrt_mul_sqrt_self f hf]
  rfl

def sampledErrorRow (a : A) (f : J → A) (t : J → ℝ) : CStarMatrix (Fin 1) J A :=
  CStarMatrix.ofMatrix (fun _ j => a * CFC.sqrt (f j) - (t j : ℂ) • CFC.sqrt (f j))

lemma sampledErrorRow_gram (a : A) (f : J → A) (t : J → ℝ)
    (ha : IsSelfAdjoint a) (hf : ∀ j, 0 ≤ f j) (haf : ∀ j, Commute a (f j)) :
    sampledErrorRow a f t * (sampledErrorRow a f t).conjTranspose =
      CStarMatrix.toOneByOne (Fin 1) ℂ A (∑ j, sampledQuadraticError a (f j) (t j)) := by
  ext i k
  have hi : i = 0 := Subsingleton.elim _ _
  have hk : k = 0 := Subsingleton.elim _ _
  subst i k
  change (∑ j, (a * CFC.sqrt (f j) - (t j : ℂ) • CFC.sqrt (f j)) *
    star (a * CFC.sqrt (f j) - (t j : ℂ) • CFC.sqrt (f j))) = _
  exact Finset.sum_congr rfl (fun j _ => sampled_error_square a (f j) ha (hf j) (haf j) (t j))

lemma sampledErrorRow_norm_sq (a : A) (f : J → A) (t : J → ℝ)
    (ha : IsSelfAdjoint a) (hf : ∀ j, 0 ≤ f j) (haf : ∀ j, Commute a (f j)) :
    ‖sampledErrorRow a f t‖ ^ 2 = ‖∑ j, sampledQuadraticError a (f j) (t j)‖ := by
  rw [← rectangular_norm_range, sampledErrorRow_gram a f t ha hf haf]
  exact NonUnitalStarAlgHom.norm_map
    (CStarMatrix.toOneByOne (Fin 1) ℂ A).toNonUnitalStarAlgHom
    (CStarMatrix.toOneByOne (Fin 1) ℂ A).injective _

lemma sampledErrorRow_coeff_norm_le [DecidableEq J] (a : A) (f : J → A) (t : J → ℝ) (d : J → A)
    (ha : IsSelfAdjoint a) (hf : ∀ j, 0 ≤ f j) (haf : ∀ j, Commute a (f j))
    (C q : ℝ) (hC : 0 ≤ C) (hq : 0 ≤ q) (hd : ∀ j, ‖d j‖ ≤ C)
    (herr : ‖∑ j, sampledQuadraticError a (f j) (t j)‖ ≤ q ^ 2) :
    ‖sampledErrorRow a f t * NonunitalGamma.diagonalHom d‖ ≤ q * C := by
  have he : ‖sampledErrorRow a f t‖ ≤ q := by
    have hs := (sampledErrorRow_norm_sq a f t ha hf haf).trans_le herr
    nlinarith [norm_nonneg (sampledErrorRow a f t)]
  have hdiag : ‖NonunitalGamma.diagonalHom d‖ ≤ C :=
    (NonUnitalStarAlgHom.norm_apply_le NonunitalGamma.diagonalHom d).trans
      ((pi_norm_le_iff_of_nonneg hC).mpr hd)
  exact (rectangular_norm_mul_le _ _).trans (mul_le_mul he hdiag (norm_nonneg _) hq)

end WeakPureInfiniteness

end

end OAI
