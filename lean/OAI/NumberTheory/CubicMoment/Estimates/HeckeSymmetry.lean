import OAI.NumberTheory.CubicMoment.Estimates.MellinWeights
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

namespace OAI

/-! The scalar factors on the symmetry line in the primitive Hecke
functional equation. These identities apply also to fixed infinity type.
They keep conductor-dependent phases outside the dual polynomial. -/

noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

def heckeGammaRatio (k t : ℝ) : ℂ :=
  Complex.Gamma ((k+1/2:ℝ) - (t:ℂ)*Complex.I) /
    Complex.Gamma ((k+1/2:ℝ) + (t:ℂ)*Complex.I)

lemma norm_heckeGammaRatio {k : ℝ} (hk : 0 ≤ k) (t : ℝ) :
    ‖heckeGammaRatio k t‖ = 1 := by
  have hre : 0 < (((k+1/2:ℝ):ℂ) + (t:ℂ)*Complex.I).re := by
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im]
    linarith
  have hne := Complex.Gamma_ne_zero_of_re_pos hre
  have hc : ((k+1/2:ℝ):ℂ) - (t:ℂ)*Complex.I =
      starRingEnd ℂ (((k+1/2:ℝ):ℂ) + (t:ℂ)*Complex.I) := by
    simp only [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I, mul_neg,
      sub_eq_add_neg]
  rw [heckeGammaRatio, hc, Complex.Gamma_conj, norm_div, Complex.norm_conj]
  exact div_self (norm_ne_zero_iff.mpr hne)

/-- `D` includes the fixed field factor in the completed L-function. -/
def heckeSymmetryFactor (ε : ℂ) (D Z k t τ : ℝ) : ℂ :=
  ε * mellinPhase (t-τ) D * mellinPhase τ Z * heckeGammaRatio k (τ-t)

lemma norm_heckeSymmetryFactor {ε : ℂ} (hε : ‖ε‖ = 1)
    (D Z k t τ : ℝ) (hk : 0 ≤ k) :
    ‖heckeSymmetryFactor ε D Z k t τ‖ = 1 := by
  simp [heckeSymmetryFactor, hε, norm_heckeGammaRatio hk]

/-- The entire character-dependent multiplier can be removed from the
square-sum norm before applying a common integral majorant. -/
lemma heckeSymmetry_square_sum {ι : Type*} (S : Finset ι)
    (ε : ι → ℂ) (D : ι → ℝ) (Z k t τ : ℝ) (v : ι → ℂ)
    (hε : ∀ i ∈ S, ‖ε i‖ = 1) (hk : 0 ≤ k) :
    (∑ i ∈ S, ‖heckeSymmetryFactor (ε i) (D i) Z k t τ * v i‖^2) =
      ∑ i ∈ S, ‖v i‖^2 := by
  apply Finset.sum_congr rfl
  intro i hi
  rw [norm_mul, norm_heckeSymmetryFactor (hε i hi) _ _ _ _ _ hk, one_mul]

end CubicFirstMoment

end

end OAI
