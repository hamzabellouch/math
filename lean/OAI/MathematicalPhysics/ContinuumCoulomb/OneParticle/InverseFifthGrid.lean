import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.CubeGeometry
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.CoulombInverseFifth
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.CoulombFarCell

namespace OAI

/-! Inverse-fifth far-cell sums are bounded independently of box volume.
The proof compares each actual cube to the integrable radial tail. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

theorem far_cube_distances {h : ℝ} (hh : 0 < h) {y b x : Position}
    (hfar : 4*h ≤ ‖y-b‖) (hx : x ∈ positionCube b h) :
    h < ‖y-x‖ ∧ ‖y-b‖/2 ≤ ‖y-x‖ ∧ ‖y-x‖ ≤ 2*‖y-b‖ := by
  have hn := positionCube_norm_sub_le hh.le hx
  have ha := norm_sub_le_norm_sub_add_norm_sub y x b
  have hb := norm_sub_le_norm_sub_add_norm_sub y b x
  rw [norm_sub_rev b x] at hb
  constructor
  · linarith
  constructor <;> linarith

theorem inverseFifth_far_cube_bound {h : ℝ} (hh : 0 < h) (y b : Position)
    (hfar : 4*h ≤ ‖y-b‖) :
    h^3/‖y-b‖^5 ≤ 32*(∫ x in positionCube b h, inverseFifthTail h (y-x)) := by
  have hd : 0 < ‖y-b‖ := lt_of_lt_of_le (by positivity) hfar
  have hi := translatedInverseFifth_integrable y hh
  have hm := (positionCube_isClosed b h).measurableSet
  have hc := ((positionCube_isCompact b hh.le).measure_lt_top (μ := volume)).ne
  have he := setIntegral_mono_on
    (integrableOn_const (C := 1/‖y-b‖^5) hc)
    (hi.const_mul 32).integrableOn hm (fun x hx => ?_)
  · have hv : (volume.restrict (positionCube b h)).real Set.univ = h^3 := by
      simpa only [Measure.real,Measure.restrict_apply_univ] using positionCube_volume b hh.le
    simpa only [integral_const,smul_eq_mul,hv,integral_const_mul,
      div_eq_mul_inv,mul_one,one_mul] using he
  · obtain ⟨hgt,_hl,hu⟩ := far_cube_distances hh hfar hx
    rw [inverseFifthTail_eq_inv_pow _ hgt]
    have hdx : 0 < ‖y-x‖ := hh.trans hgt
    rw [mul_one_div]
    apply (div_le_div_iff₀ (pow_pos hd 5) (pow_pos hdx 5)).mpr
    have hp := pow_le_pow_left₀ (norm_nonneg (y-x)) hu 5
    nlinarith [show (2*‖y-b‖)^5 = 32*‖y-b‖^5 by ring]

theorem inverseFifth_grid_sum_bound {ι : Type*} [Fintype ι]
    (index : ι → Fin 3 → ℤ) (hindex : Function.Injective index)
    {h : ℝ} (hh : 0 < h) (y : Position)
    (hfar : ∀ i, 4*h ≤ ‖y-gaussCellCenter h (index i)‖) :
    (∑ i, h^3/‖y-gaussCellCenter h (index i)‖^5) ≤ 64*Real.pi/h^2 := by
  calc
    _ ≤ ∑ i, 32*(∫ x in positionCube (gaussCellCenter h (index i)) h,
        inverseFifthTail h (y-x)) :=
      Finset.sum_le_sum (fun i _ => inverseFifth_far_cube_bound hh y _ (hfar i))
    _ = 32*(∑ i, ∫ x in positionCube (gaussCellCenter h (index i)) h,
        inverseFifthTail h (y-x)) := (Finset.mul_sum _ _ _).symm
    _ ≤ 32*(∫ x, inverseFifthTail h (y-x)) :=
      mul_le_mul_of_nonneg_left (grid_cell_integral_sum_le index hindex hh _
        (translatedInverseFifth_integrable y hh) (fun x => inverseFifthTail_nonneg h (y-x)))
        (by norm_num)
    _ = _ := by rw [translatedInverseFifth_integral y hh]; ring

theorem coulomb_far_grid_error :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ {ι : Type} [Fintype ι]
      (index : ι → Fin 3 → ℤ), Function.Injective index →
      ∀ (h : ℝ), 0 < h → ∀ (y : Position),
      (∀ i, 4*h ≤ ‖y-gaussCellCenter h (index i)‖) →
      |(∑ i, positionCellGauss (gaussCellCenter h (index i)) h
        (fun x => Coulomb.coulombKernel (y-x)))-
        (∑ i, positionCellIntegral (gaussCellCenter h (index i)) h
          (fun x => Coulomb.coulombKernel (y-x)))| ≤ C*h^2 := by
  obtain ⟨C,hC,hbound⟩ := coulomb_far_cell_error
  refine ⟨2048*Real.pi*C,?_,?_⟩
  · have hp := Real.pi_gt_three
    nlinarith
  · intro ι _ index hindex h hh y hfar
    have he (i : ι) :
        |positionCellGauss (gaussCellCenter h (index i)) h (fun x => Coulomb.coulombKernel (y-x))-
          positionCellIntegral (gaussCellCenter h (index i)) h (fun x => Coulomb.coulombKernel (y-x))| ≤
          (32*C*h^4)*(h^3/‖y-gaussCellCenter h (index i)‖^5) := by
      have hd : 0 < ‖y-gaussCellCenter h (index i)‖ := lt_of_lt_of_le (by positivity) (hfar i)
      have hi := hbound y (gaussCellCenter h (index i)) h
        (‖y-gaussCellCenter h (index i)‖/2) hh.le (by positivity)
        (fun x hx v hv z hz => (far_cube_distances hh (hfar i)
          (cubePoint_mem_positionCube _ hh.le hx hv hz)).2.1)
      apply hi.trans_eq
      field_simp
      ring
    calc
      _ ≤ ∑ i, |positionCellGauss (gaussCellCenter h (index i)) h
          (fun x => Coulomb.coulombKernel (y-x))-
          positionCellIntegral (gaussCellCenter h (index i)) h
            (fun x => Coulomb.coulombKernel (y-x))| := by
        rw [← Finset.sum_sub_distrib]
        exact Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, (32*C*h^4)*(h^3/‖y-gaussCellCenter h (index i)‖^5) :=
        Finset.sum_le_sum (fun i _ => he i)
      _ = (32*C*h^4)*(∑ i, h^3/‖y-gaussCellCenter h (index i)‖^5) :=
        (Finset.mul_sum _ _ _).symm
      _ ≤ (32*C*h^4)*(64*Real.pi/h^2) :=
        mul_le_mul_of_nonneg_left (inverseFifth_grid_sum_bound index hindex hh y hfar)
          (by positivity)
      _ = _ := by field_simp [hh.ne']; ring

end ContinuumCoulomb

end

end OAI
