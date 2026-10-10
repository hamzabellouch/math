import OAI.Analysis.KadisonKastler.TwoCornerStrictContraction
import OAI.Analysis.KadisonKastler.BlockMatrices

namespace OAI

/-! # A strictly positive off-diagonal matrix corner

A positive lower bound on the off-diagonal entry gives the two quadratic
corner bounds used by the strict diagonal-contraction estimate.
-/

namespace KadisonKastler

noncomputable section

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem scalar_sq_le_star_mul_of_scalar_le (a : A) (δ : ℝ) (hδ : 0 ≤ δ)
    (ha : algebraMap ℝ A δ ≤ a) : algebraMap ℝ A (δ ^ 2) ≤ star a * a := by
  have hd : 0 ≤ algebraMap ℝ A δ := by
    simpa only [Algebra.algebraMap_eq_smul_one] using
      smul_nonneg hδ (zero_le_one : (0 : A) ≤ 1)
  have ha0 : 0 ≤ a := hd.trans ha
  have hsa := ha0.isSelfAdjoint
  have hs := (algebraMap_le_iff_le_spectrum hsa).mp ha
  have hsq := algebraMap_le_cfc (fun x : ℝ => x ^ 2) (δ ^ 2) a
    (fun x hx => pow_le_pow_left₀ hδ (hs x hx) 2) (ha := hsa)
  rw [cfc_pow_id (R := ℝ) a 2 hsa] at hsq
  simpa only [pow_two, hsa.star_eq] using hsq

end

end KadisonKastler

end OAI
