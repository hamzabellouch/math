import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.InverseFifthGrid

namespace OAI

/-! Far-grid inverse-fifth sums with the orbital cutoff radius retained.
The bound is independent of both box volume and mesh resolution. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

theorem inverseFifth_cutoff_cube_bound {h R : ℝ} (hh : 0 < h) (hR : 0 < R)
    (hhR : h ≤ R) (y b : Position) (hfar : 4*R ≤ ‖y-b‖) :
    h^3/‖y-b‖^5 ≤ 32*(∫ x in positionCube b h, inverseFifthTail R (y-x)) := by
  have hd : 0 < ‖y-b‖ := lt_of_lt_of_le (by positivity) hfar
  have hi := translatedInverseFifth_integrable y hR
  have he := setIntegral_mono_on
    (integrableOn_const (C := 1/‖y-b‖^5)
      ((positionCube_isCompact b hh.le).measure_lt_top (μ := volume)).ne)
    (hi.const_mul 32).integrableOn (positionCube_isClosed b h).measurableSet (fun x hx => ?_)
  · have hv : (volume.restrict (positionCube b h)).real Set.univ = h^3 := by
      simpa only [Measure.real,Measure.restrict_apply_univ] using positionCube_volume b hh.le
    simpa only [integral_const,smul_eq_mul,hv,integral_const_mul,
      div_eq_mul_inv,mul_one,one_mul] using he
  · have hn := positionCube_norm_sub_le hh.le hx
    have ha := norm_sub_le_norm_sub_add_norm_sub y x b
    have hu := (norm_sub_le_norm_sub_add_norm_sub y b x)
    rw [norm_sub_rev b x] at hu
    have hdx : R < ‖y-x‖ := by linarith
    have hupper : ‖y-x‖ ≤ 2*‖y-b‖ := by linarith
    rw [inverseFifthTail_eq_inv_pow _ hdx,mul_one_div]
    apply (div_le_div_iff₀ (pow_pos hd 5) (pow_pos (hR.trans hdx) 5)).mpr
    have hp := pow_le_pow_left₀ (norm_nonneg (y-x)) hupper 5
    nlinarith [show (2*‖y-b‖)^5 = 32*‖y-b‖^5 by ring]

theorem inverseFifth_cutoff_grid_sum {ι : Type*} [Fintype ι]
    (index : ι → Fin 3 → ℤ) (hindex : Function.Injective index)
    {h R : ℝ} (hh : 0 < h) (hR : 0 < R) (hhR : h ≤ R) (y : Position)
    (hfar : ∀ i, 4*R ≤ ‖y-gaussCellCenter h (index i)‖) :
    (∑ i, h^3/‖y-gaussCellCenter h (index i)‖^5) ≤ 64*Real.pi/R^2 := by
  calc
    _ ≤ ∑ i, 32*(∫ x in positionCube (gaussCellCenter h (index i)) h,
        inverseFifthTail R (y-x)) :=
      Finset.sum_le_sum (fun i _ => inverseFifth_cutoff_cube_bound hh hR hhR y _ (hfar i))
    _ = 32*(∑ i, ∫ x in positionCube (gaussCellCenter h (index i)) h,
        inverseFifthTail R (y-x)) := (Finset.mul_sum _ _ _).symm
    _ ≤ 32*(∫ x, inverseFifthTail R (y-x)) :=
      mul_le_mul_of_nonneg_left (grid_cell_integral_sum_le index hindex hh _
        (translatedInverseFifth_integrable y hR) (fun x => inverseFifthTail_nonneg R (y-x)))
        (by norm_num)
    _ = _ := by rw [translatedInverseFifth_integral y hR]; ring

end ContinuumCoulomb

end

end OAI
