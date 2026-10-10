import OAI.NumberTheory.CubicMoment.Theta.CubicThetaAngularPolynomialStrip
import OAI.NumberTheory.CubicMoment.Estimates.MellinHeckeContour

namespace OAI

/-! Smooth contour motion for the actual nonzero angular additive series.
Both analyticity and polynomial growth are derived from the arithmetic theta
transformation. The scale may be any positive real number. -/
noncomputable section
open MeasureTheory Set
open scoped ContDiff
namespace CubicFirstMoment

theorem cubicThetaAngularDirichletContinuation_contour {q : Eisenstein}
    (hq : primary q) (x y : Eisenstein) (hxy : q∣9*x*y-1) (rev : Bool)
    {k : ℕ} (hk : 0<k) (W : ℝ→ℂ) (hW : HasCompactSupport W)
    (hpos : tsupport W ⊆ Ioi 0) (hsm : ContDiff ℝ ∞ W)
    {a b Z : ℝ} (hab : a ≤ b) (hZ : 0<Z) :
    (∫ t : ℝ, mellin W (a+(t:ℂ)*Complex.I)*(Z:ℂ)^(a+(t:ℂ)*Complex.I)*
      cubicThetaAngularDirichletContinuation q x y rev k (a+(t:ℂ)*Complex.I)) =
    ∫ t : ℝ, mellin W (b+(t:ℂ)*Complex.I)*(Z:ℂ)^(b+(t:ℂ)*Complex.I)*
      cubicThetaAngularDirichletContinuation q x y rev k (b+(t:ℂ)*Complex.I) := by
  obtain ⟨C,N,hC,hpoly⟩ :=
    cubicThetaAngularDirichletContinuation_polynomial_strip hq x y hxy rev hk a b
  let L : ℂ→ℂ := fun s => (Z:ℂ)^s*cubicThetaAngularDirichletContinuation q x y rev k s
  let B := max (Z^a) (Z^b)*C
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hp (σ : ℝ) (hσ : σ∈Icc a b) (t : ℝ) :
      ‖L (σ+((t-0:ℝ):ℂ)*Complex.I)‖ ≤ B*(1+|t-0|)^N := by
    simp only [sub_zero]
    have hz : Z^σ ≤ max (Z^a) (Z^b) := by
      by_cases h : 1 ≤ Z
      · exact (Real.rpow_le_rpow_of_exponent_le h hσ.2).trans (le_max_right _ _)
      · exact (Real.rpow_le_rpow_of_exponent_ge hZ (le_of_not_ge h) hσ.1).trans
          (le_max_left _ _)
    have hd : ‖cubicThetaAngularDirichletContinuation q x y rev k
        (σ+(t:ℂ)*Complex.I)‖ ≤ C*(1+|t|)^N := by
      simpa using hpoly (σ+(t:ℂ)*Complex.I) (by simpa using hσ)
    dsimp only [L]
    rw [norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos hZ]
    simp only [Complex.add_re,Complex.ofReal_re,Complex.mul_re,Complex.ofReal_im,
      Complex.I_re,Complex.I_im,mul_zero,zero_mul,sub_zero,add_zero] at *
    calc
      _ ≤  max (Z^a) (Z^b)*(C*(1+|t|)^N) := mul_le_mul hz hd
        (_root_.norm_nonneg _) (by positivity)
      _ = _ := by dsimp [B]; ring
  have : NeZero (Z:ℂ) := ⟨Complex.ofReal_ne_zero.mpr hZ.ne'⟩
  have hLd : Differentiable ℂ L := (differentiable_const_cpow_of_neZero _).mul
    (cubicThetaAngularDirichletContinuation_entire hq x y rev k)
  have H := mellinHecke_contour_shift W hW hpos hsm hab (Z:=1) (by norm_num) 0
    L hLd hB N hp
  simpa only [sub_zero,Complex.ofReal_one,Complex.one_cpow,mul_one,L,mul_assoc] using H

end CubicFirstMoment

end

end OAI
