import OAI.Geometry.Kahler.HartogsTensorSymmetry

namespace OAI

open scoped ContDiff
open Set Filter Topology
open scoped ContDiff Matrix Matrix.Norms.Elementwise
noncomputable section

open Set Filter Topology
open scoped ContDiff Matrix Matrix.Norms.Elementwise
namespace PinchedHartogs

lemma normalPotential_curvature_split {f : Base → ℝ} (hf : ContDiffAt ℝ ∞ f 0)
    (lam : ℝ) (w : ℂ) (hn : normalLogWeight f w (0,w) < 0)
    (hG : (((lam : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) +
      (barrierX (normalLogWeight f w (0,w)) : ℂ) • baseHessian f 0)).det ≠ 0)
    (a b c d : Fin 3) :
    curvature (complexHessian (normalPotential f lam w)) (0,w) a b c d =
      -dbar (fun q => dz (fun r => complexHessian (normalPotential f lam w) r c d) q a) (0,w) b +
      (∑ e : Fin 2, ∑ k : Fin 2,
        (((lam : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) +
          (barrierX (normalLogWeight f w (0,w)) : ℂ) • baseHessian f 0)⁻¹) e k *
          dz (fun r => complexHessian (normalPotential f lam w) r c e.castSucc) (0,w) a *
          star (dz (fun r => complexHessian (normalPotential f lam w) r d k.castSucc) (0,w) b)) +
      (barrierQ (normalLogWeight f w (0,w)) : ℂ)⁻¹ *
        dz (fun r => complexHessian (normalPotential f lam w) r c 2) (0,w) a *
        star (dz (fun r => complexHessian (normalPotential f lam w) r d 2) (0,w) b) := by
  have hs := (normalPotential_contDiffAt hf lam w hn).of_le (m := 3) (WithTop.coe_le_coe.mpr le_top)
  unfold curvature
  simp_rw [dbar_complexHessian_conj hs]
  rw [normalPotential_hessian_block hf lam w hn,
    block3_inv hG (by exact_mod_cast (ne_of_gt (barrierQ_positive hn))), block3_contraction]
  ring

lemma normalPotential_curvature_HHHH {f : Base → ℝ} (hf : ContDiffAt ℝ ∞ f 0)
    (lam : ℝ) (w : ℂ) (hn : normalLogWeight f w (0,w) < 0)
    (hG : (((lam : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) +
      (barrierX (normalLogWeight f w (0,w)) : ℂ) • baseHessian f 0)).det ≠ 0)
    (a b c d : Fin 2) :
    curvature (complexHessian (normalPotential f lam w)) (0,w) a.castSucc b.castSucc c.castSucc d.castSucc =
      -(lam : ℂ) * ((1 : Matrix (Fin 2) (Fin 2) ℂ) a b * (1 : Matrix (Fin 2) (Fin 2) ℂ) c d +
        (1 : Matrix (Fin 2) (Fin 2) ℂ) a d * (1 : Matrix (Fin 2) (Fin 2) ℂ) c b) -
      (barrierQ (normalLogWeight f w (0,w)) : ℂ) *
        (baseHessian f 0 a b * baseHessian f 0 c d + baseHessian f 0 a d * baseHessian f 0 c b) -
      (barrierX (normalLogWeight f w (0,w)) : ℂ) * liftedFourth f (0,w) a.castSucc b.castSucc c.castSucc d.castSucc +
      (barrierX (normalLogWeight f w (0,w)) : ℂ)^2 *
      (∑ e : Fin 2, ∑ k : Fin 2,
        (((lam : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) +
          (barrierX (normalLogWeight f w (0,w)) : ℂ) • baseHessian f 0)⁻¹) e k *
          liftedThird f (0,w) a.castSucc c.castSucc e.castSucc *
          star (liftedThird f (0,w) b.castSucc d.castSucc k.castSucc)) := by
  rw [normalPotential_curvature_split hf lam w hn hG,
    normalPotential_fourth hf lam w hn, normalBarrier_fourth hf w hn]
  simp only [normalPotential_third hf lam w hn, verticalDelta_horizontal, horizontalIdentity_horizontal,
    liftedBarThird_conj (q := (0,w)) (hf.of_le (WithTop.coe_le_coe.mpr le_top)),
    liftedHessian_horizontal (q := (0,w)) (hf.of_le (WithTop.coe_le_coe.mpr le_top)),
    liftedThird_vertical_right (q := (0,w)) (hf.of_le (WithTop.coe_le_coe.mpr le_top)),
    mul_zero, zero_mul, zero_add, add_zero, star_mul, Complex.star_def, Complex.conj_ofReal]
  simp only [Fin.sum_univ_two]
  ring

lemma normalPotential_curvature_HHHV {f : Base → ℝ} (hf : ContDiffAt ℝ ∞ f 0)
    (lam : ℝ) (w : ℂ) (hn : normalLogWeight f w (0,w) < 0)
    (hG : (((lam : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) +
      (barrierX (normalLogWeight f w (0,w)) : ℂ) • baseHessian f 0)).det ≠ 0)
    (a b c : Fin 2) :
    curvature (complexHessian (normalPotential f lam w)) (0,w) a.castSucc b.castSucc c.castSucc 2 =
      (barrierQ (normalLogWeight f w (0,w)) : ℂ) * (-liftedThird f (0,w) a.castSucc c.castSucc b.castSucc +
        (barrierX (normalLogWeight f w (0,w)) : ℂ) * (∑ e : Fin 2, ∑ k : Fin 2,
          (((lam : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) + (barrierX (normalLogWeight f w (0,w)) : ℂ) • baseHessian f 0)⁻¹) e k * liftedThird f (0,w) a.castSucc c.castSucc e.castSucc *
            star (baseHessian f 0 b k))) := by
  rw [normalPotential_curvature_split hf lam w hn hG,
    normalPotential_fourth hf lam w hn, normalBarrier_fourth hf w hn]
  simp only [normalPotential_third hf lam w hn, verticalDelta_horizontal, verticalDelta_vertical,
    horizontalIdentity_horizontal, horizontalIdentity_vertical_right,
    liftedBarThird_conj (q := (0,w)) (hf.of_le (WithTop.coe_le_coe.mpr le_top)),
    liftedHessian_horizontal (q := (0,w)) (hf.of_le (WithTop.coe_le_coe.mpr le_top)),
    liftedHessian_vertical_left (q := (0,w)) (hf.of_le (WithTop.coe_le_coe.mpr le_top)),
    liftedHessian_vertical_right (q := (0,w)) (hf.of_le (WithTop.coe_le_coe.mpr le_top)),
    liftedThird_vertical_middle (q := (0,w)) (hf.of_le (WithTop.coe_le_coe.mpr le_top)),
    liftedThird_vertical_right (q := (0,w)) (hf.of_le (WithTop.coe_le_coe.mpr le_top)),
    liftedFourth_vertical_right (q := (0,w)) (hf.of_le (WithTop.coe_le_coe.mpr le_top)),
    mul_zero, zero_mul, zero_add, add_zero, mul_one, star_zero,
    star_mul, Complex.star_def, Complex.conj_ofReal]
  simp only [Fin.sum_univ_two]
  ring

lemma normalPotential_curvature_HVHV {f : Base → ℝ} (hf : ContDiffAt ℝ ∞ f 0)
    (lam : ℝ) (w : ℂ) (hn : normalLogWeight f w (0,w) < 0)
    (hG : (((lam : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) +
      (barrierX (normalLogWeight f w (0,w)) : ℂ) • baseHessian f 0)).det ≠ 0)
    (a b : Fin 2) :
    curvature (complexHessian (normalPotential f lam w)) (0,w) a.castSucc b.castSucc 2 2 =
      -(barrierQ (normalLogWeight f w (0,w)) : ℂ) * ((1 + 2 * (barrierX (normalLogWeight f w (0,w)) : ℂ)) * baseHessian f 0 a b -
        (barrierQ (normalLogWeight f w (0,w)) : ℂ) * (∑ e : Fin 2, ∑ k : Fin 2,
          (((lam : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) + (barrierX (normalLogWeight f w (0,w)) : ℂ) • baseHessian f 0)⁻¹) e k * baseHessian f 0 a e * star (baseHessian f 0 b k))) := by
  rw [normalPotential_curvature_split hf lam w hn hG,
    normalPotential_fourth hf lam w hn, normalBarrier_fourth hf w hn]
  simp only [normalPotential_third hf lam w hn, verticalDelta_horizontal, verticalDelta_vertical,
    horizontalIdentity_horizontal, horizontalIdentity_vertical_left, horizontalIdentity_vertical_right,
    liftedBarThird_conj (q := (0,w)) (hf.of_le (WithTop.coe_le_coe.mpr le_top)),
    liftedHessian_horizontal (q := (0,w)) (hf.of_le (WithTop.coe_le_coe.mpr le_top)),
    liftedHessian_vertical_left (q := (0,w)) (hf.of_le (WithTop.coe_le_coe.mpr le_top)),
    liftedHessian_vertical_right (q := (0,w)) (hf.of_le (WithTop.coe_le_coe.mpr le_top)),
    liftedThird_vertical_middle (q := (0,w)) (hf.of_le (WithTop.coe_le_coe.mpr le_top)),
    liftedFourth_vertical_middle (q := (0,w)) (hf.of_le (WithTop.coe_le_coe.mpr le_top)),
    mul_zero, zero_add, add_zero, mul_one, star_zero,
    star_mul, Complex.star_def, Complex.conj_ofReal]
  simp only [Fin.sum_univ_two, barrierThird, Complex.ofReal_mul, Complex.ofReal_add,
    Complex.ofReal_one, Complex.ofReal_ofNat]
  ring

lemma normalPotential_curvature_HHVV {f : Base → ℝ} (hf : ContDiffAt ℝ ∞ f 0)
    (lam : ℝ) (w : ℂ) (hn : normalLogWeight f w (0,w) < 0)
    (hG : (((lam : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) +
      (barrierX (normalLogWeight f w (0,w)) : ℂ) • baseHessian f 0)).det ≠ 0)
    (a c : Fin 2) :
    curvature (complexHessian (normalPotential f lam w)) (0,w) a.castSucc 2 c.castSucc 2 = 0 := by
  rw [normalPotential_curvature_split hf lam w hn hG,
    normalPotential_fourth hf lam w hn, normalBarrier_fourth hf w hn]
  simp only [normalPotential_third hf lam w hn, verticalDelta_horizontal, verticalDelta_vertical,
    horizontalIdentity_vertical_right,
    liftedBarThird_conj (q := (0,w)) (hf.of_le (WithTop.coe_le_coe.mpr le_top)),
    liftedHessian_horizontal (q := (0,w)) (hf.of_le (WithTop.coe_le_coe.mpr le_top)),
    liftedHessian_vertical_left (q := (0,w)) (hf.of_le (WithTop.coe_le_coe.mpr le_top)),
    liftedHessian_vertical_right (q := (0,w)) (hf.of_le (WithTop.coe_le_coe.mpr le_top)),
    liftedThird_vertical_left (q := (0,w)) (hf.of_le (WithTop.coe_le_coe.mpr le_top)),
    liftedThird_vertical_right (q := (0,w)) (hf.of_le (WithTop.coe_le_coe.mpr le_top)),
    liftedFourth_vertical_second (q := (0,w)) (hf.of_le (WithTop.coe_le_coe.mpr le_top)),
    mul_zero, zero_mul, zero_add, add_zero, mul_one, star_zero,
    Complex.star_def, Complex.conj_ofReal]
  simp

lemma normalPotential_curvature_HVVV {f : Base → ℝ} (hf : ContDiffAt ℝ ∞ f 0)
    (lam : ℝ) (w : ℂ) (hn : normalLogWeight f w (0,w) < 0)
    (hG : (((lam : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) +
      (barrierX (normalLogWeight f w (0,w)) : ℂ) • baseHessian f 0)).det ≠ 0)
    (a : Fin 2) :
    curvature (complexHessian (normalPotential f lam w)) (0,w) a.castSucc 2 2 2 = 0 := by
  rw [normalPotential_curvature_split hf lam w hn hG,
    normalPotential_fourth hf lam w hn, normalBarrier_fourth hf w hn]
  simp only [normalPotential_third hf lam w hn, verticalDelta_horizontal, verticalDelta_vertical,
    horizontalIdentity_vertical_right,
    liftedBarThird_conj (q := (0,w)) (hf.of_le (WithTop.coe_le_coe.mpr le_top)),
    liftedHessian_horizontal (q := (0,w)) (hf.of_le (WithTop.coe_le_coe.mpr le_top)),
    liftedHessian_vertical_left (q := (0,w)) (hf.of_le (WithTop.coe_le_coe.mpr le_top)),
    liftedHessian_vertical_right (q := (0,w)) (hf.of_le (WithTop.coe_le_coe.mpr le_top)),
    liftedThird_vertical_left (q := (0,w)) (hf.of_le (WithTop.coe_le_coe.mpr le_top)),
    liftedThird_vertical_middle (q := (0,w)) (hf.of_le (WithTop.coe_le_coe.mpr le_top)),
    liftedFourth_vertical_second (q := (0,w)) (hf.of_le (WithTop.coe_le_coe.mpr le_top)),
    mul_zero, zero_mul, zero_add, add_zero, mul_one, star_zero,
    Complex.star_def, Complex.conj_ofReal]
  simp

lemma normalPotential_curvature_VVVV {f : Base → ℝ} (hf : ContDiffAt ℝ ∞ f 0)
    (lam : ℝ) (w : ℂ) (hn : normalLogWeight f w (0,w) < 0)
    (hG : (((lam : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) +
      (barrierX (normalLogWeight f w (0,w)) : ℂ) • baseHessian f 0)).det ≠ 0) :
    curvature (complexHessian (normalPotential f lam w)) (0,w) 2 2 2 2 = -2 * (barrierQ (normalLogWeight f w (0,w)) : ℂ)^2 := by
  rw [normalPotential_curvature_split hf lam w hn hG,
    normalPotential_fourth hf lam w hn, normalBarrier_fourth hf w hn]
  simp only [normalPotential_third hf lam w hn, verticalDelta_horizontal, verticalDelta_vertical,
    horizontalIdentity_vertical_right,
    liftedBarThird_conj (q := (0,w)) (hf.of_le (WithTop.coe_le_coe.mpr le_top)),
    liftedHessian_vertical_left (q := (0,w)) (hf.of_le (WithTop.coe_le_coe.mpr le_top)),
    liftedThird_vertical_left (q := (0,w)) (hf.of_le (WithTop.coe_le_coe.mpr le_top)),
    liftedFourth_vertical_left (q := (0,w)) (hf.of_le (WithTop.coe_le_coe.mpr le_top)),
    mul_zero, zero_add, add_zero, mul_one, star_zero,
    Complex.star_def, Complex.conj_ofReal]
  have hq : (barrierQ (normalLogWeight f w (0,w)) : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt (barrierQ_positive hn))
  simp only [Finset.sum_const_zero, barrierThird, barrierFourth, Complex.ofReal_mul,
    Complex.ofReal_add, Complex.ofReal_one, Complex.ofReal_ofNat, Complex.ofReal_pow]
  field_simp
  simp only [barrierQ, Complex.ofReal_mul, Complex.ofReal_add, Complex.ofReal_one]
  ring

end PinchedHartogs

end

end OAI
