import OAI.NumberTheory.CubicMoment.Estimates.IdealDirichletBounds
import OAI.NumberTheory.CubicMoment.Angular.AngularHeckeGrowth
import OAI.NumberTheory.CubicMoment.Estimates.GammaInverseGrowth

namespace OAI

/-! A conductor-explicit polynomial bound in the fixed strip needed by
the local zero-free argument. The finite-order constant disappears under
Phragmen--Lindelof; only the actual functional-equation factors remain. -/
noncomputable section
open Set
namespace CubicFirstMoment

def heckeZeroFreeMajorant (A k : ℝ) (ε : ℂ) : ℝ :=
  (idealZetaTwo+‖ε‖*A^4*(k+7)^4*idealZetaTwo)*16*(9/2:ℝ)^4

lemma heckeZeroFreeMajorant_ge_zeta (A k : ℝ) (ε : ℂ) :
    idealZetaTwo ≤ heckeZeroFreeMajorant A k ε := by
  have h := idealZetaTwo_pos
  have hp : 0 ≤ ‖ε‖*A^4*(k+7)^4*idealZetaTwo := by positivity
  unfold heckeZeroFreeMajorant
  nlinarith

lemma heckeZeroFreeMajorant_pos (A k : ℝ) (ε : ℂ) :
    0 < heckeZeroFreeMajorant A k ε :=
  idealZetaTwo_pos.trans_le (heckeZeroFreeMajorant_ge_zeta A k ε)

theorem shifted_hecke_uniform_strip
    {χ χdual : EisensteinIdealExponent → ℂ}
    (hχ : ∀ ν, ‖χ ν‖ ≤ 1) (hχdual : ∀ ν, ‖χdual ν‖ ≤ 1)
    {A k : ℝ} (hA : 0 < A) (hk : 0 ≤ k) {ε : ℂ} {L Ldual : ℂ → ℂ}
    (hL : Differentiable ℂ L)
    (hs : ∀ s : ℂ, 1 < s.re → L s=normDirichletSeries χ idealExponentNorm s)
    (hds : ∀ s : ℂ, 1 < s.re → Ldual s=normDirichletSeries χdual idealExponentNorm s)
    (hFE : HeckeFunctionalEquation A k ε L Ldual)
    (hcomp : ShiftedCompletedHeckeFiniteOrder A k L) :
    ∀ z : ℂ, -(3/2:ℝ) ≤ z.re →
      ‖L z‖ ≤ heckeZeroFreeMajorant A k ε*(1+|z.im|)^4 := by
  let C : ℝ := idealZetaTwo+‖ε‖*A^4*(k+7)^4*idealZetaTwo
  have hS0 := idealZetaTwo_pos
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hS : idealZetaTwo ≤ C := le_add_of_nonneg_right (by positivity)
  have ha : ∀ z : ℂ, z.re=-(3/2:ℝ) → ‖L z‖ ≤ C*(1+|z.im|)^4 := by
    intro z hz
    have he : z=(1/2:ℂ)-(2:ℕ)+(z.im:ℂ)*Complex.I := by
      apply Complex.ext <;> norm_num
      linarith
    have hb := angular_hecke_left_boundary χdual hχdual hA hk hL hcomp hFE hds
      (m := 2) (by norm_num) z.im
    rw [←he] at hb
    have hb' : ‖L z‖ ≤ (‖ε‖*A^4*(k+7)^4*idealZetaTwo)*(1+|z.im|)^4 := by
      simpa only [idealZetaTwo,Nat.reduceMul,Nat.cast_ofNat,
        show k+3*(2:ℝ)+1=k+7 by ring] using! hb
    exact hb'.trans (mul_le_mul_of_nonneg_right (by dsimp [C]; linarith [idealZetaTwo_pos])
      (by positivity))
  have hb : ∀ z : ℂ, z.re=2 → ‖L z‖ ≤ C*(1+|z.im|)^4 := by
    intro z hz
    rw [hs z (by linarith)]
    exact (idealDirichlet_upper_bound χ hχ hz.ge).trans
      (hS.trans (le_mul_of_one_le_right hC (one_le_pow₀ (by linarith [abs_nonneg z.im]))))
  have hfin : FiniteVerticalOrder L (-(3/2:ℝ)) 2 :=
    shifted_completed_finiteVerticalOrder hA hL hcomp
      (gammaInverseFiniteOrder (-(3/2:ℝ)+k) (2+k))
  have hbound := polynomial_strip_of_finite_order (a := -(3/2:ℝ)) (b := 2)
    (by norm_num) hL hfin hC 4 ha hb
  intro z hz
  by_cases hz2 : z.re ≤ 2
  · simpa only [heckeZeroFreeMajorant,C,show 2-(-(3/2:ℝ))+1=9/2 by norm_num,
      show (2:ℝ)^4=16 by norm_num]
      using hbound z ⟨hz,hz2⟩
  · rw [hs z (by linarith)]
    exact (idealDirichlet_upper_bound χ hχ (by linarith)).trans
      ((heckeZeroFreeMajorant_ge_zeta A k ε).trans
        (le_mul_of_one_le_right (heckeZeroFreeMajorant_pos A k ε).le
          (one_le_pow₀ (by linarith [abs_nonneg z.im]))))

end CubicFirstMoment

end

end OAI
