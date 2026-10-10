import OAI.NumberTheory.JointDickman.Arithmetic.CoarseResidueSmoothing

namespace OAI

/-! # A uniform pointwise bound for centered coarse arithmetic features -/
namespace JointDickman
open Finset

theorem norm_centered_coarse_weight_le {ι : Type*} [Fintype ι]
    (E : ι → Finset ℕ) (ζ : ι → ℂ) (hζ : ∀ i, ‖ζ i‖ = 1)
    (μ : ℂ) (hμ : ‖μ‖ ≤ 1) {m : ℕ} (hm : 0 < m)
    (B : ℕ) (b : Fin m) (n : ℕ) :
    ‖(binLabel E ζ n-μ)*(primeSiteWeight (auxiliaryPrimes B) (primeCoarseFeature m B b) n : ℂ)‖ ≤
      2/channelMesh m := by
  by_cases hn : n = 0
  · subst n
    simp only [ArithmeticFunction.map_zero,Complex.ofReal_zero,mul_zero,norm_zero]
    exact div_nonneg (by norm_num) (channelMesh_pos hm).le
  · rw [norm_mul,primeSiteWeight_apply _ _ hn,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (primeCoarseFeature_bounds hm b _).1]
    exact (mul_le_mul (norm_centered_binLabel_le_two E ζ hζ μ hμ n)
      (primeCoarseFeature_bounds hm b _).2 (primeCoarseFeature_bounds hm b _).1
      (by norm_num)).trans_eq (by ring)

end JointDickman

end OAI
