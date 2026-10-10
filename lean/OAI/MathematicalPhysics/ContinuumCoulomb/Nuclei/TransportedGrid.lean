import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.CubeGeometry
import OAI.MathematicalPhysics.ContinuumCoulomb.Nuclei.MoserIntegralBound

namespace OAI

/-! The far-cell inverse-fifth sum after the actual density transport.
Its constant does not depend on the slab's horizontal extent. -/

noncomputable section
open MeasureTheory
open scoped BigOperators NNReal
namespace ContinuumCoulomb

theorem transported_far_cube_distances {h : ℝ} (hh : 0 < h)
    (G : Position → Position) {L : ℝ≥0} (hL : 0 < L) (hG : LipschitzWith L G)
    {y b x : Position} (hfar : 4*(L:ℝ)*h ≤ ‖y-G b‖) (hx : x ∈ positionCube b h) :
    (L:ℝ)*h < ‖y-G x‖ ∧ ‖y-G b‖/2 ≤ ‖y-G x‖ ∧ ‖y-G x‖ ≤ 2*‖y-G b‖ := by
  have hhL : 0 < (L:ℝ)*h := mul_pos (by exact_mod_cast hL) hh
  have hn : ‖G x-G b‖ ≤ (L:ℝ)*h :=
    (hG.norm_sub_le x b).trans (mul_le_mul_of_nonneg_left
      (positionCube_norm_sub_le hh.le hx) L.coe_nonneg)
  have ha := norm_sub_le_norm_sub_add_norm_sub y (G x) (G b)
  have hb := norm_sub_le_norm_sub_add_norm_sub y (G b) (G x)
  rw [norm_sub_rev (G b) (G x)] at hb
  constructor
  · nlinarith
  constructor <;> nlinarith

theorem transported_inverseFifth_far_cube_bound {h : ℝ} (hh : 0 < h)
    (G : Position → Position) {L : ℝ≥0} (hL : 0 < L) (hG : LipschitzWith L G)
    (y b : Position) (hfar : 4*(L:ℝ)*h ≤ ‖y-G b‖) :
    h^3/‖y-G b‖^5 ≤
      32*(∫ x in positionCube b h, inverseFifthTail ((L:ℝ)*h) (y-G x)) := by
  have hr : 0 < (L:ℝ)*h := mul_pos (by exact_mod_cast hL) hh
  have hd : 0 < ‖y-G b‖ := lt_of_lt_of_le (by positivity) hfar
  have hi : IntegrableOn (fun x => inverseFifthTail ((L:ℝ)*h) (y-G x)) (positionCube b h) := by
    apply IntegrableOn.of_bound (positionCube_isCompact b hh.le).measure_lt_top
      (((inverseFifthTail_measurable _).comp (continuous_const.sub hG.continuous).measurable).aestronglyMeasurable.restrict)
      (1/((L:ℝ)*h)^5)
    exact Filter.Eventually.of_forall (fun x => by
      change ‖inverseFifthTail ((L:ℝ)*h) (y-G x)‖ ≤ 1/((L:ℝ)*h)^5
      rw [Real.norm_of_nonneg (inverseFifthTail_nonneg _ _)]
      exact inverseFifthTail_le hr _)
  have hp (x : Position) (hx : x ∈ positionCube b h) :
      1/‖y-G b‖^5 ≤ 32*inverseFifthTail ((L:ℝ)*h) (y-G x) := by
    obtain ⟨hxgt,_hxl,hxu⟩ := transported_far_cube_distances hh G hL hG hfar hx
    have hdx := hr.trans hxgt
    rw [inverseFifthTail_eq_inv_pow _ hxgt,mul_one_div]
    apply (div_le_div_iff₀ (pow_pos hd 5) (pow_pos hdx 5)).mpr
    have hb := pow_le_pow_left₀ (norm_nonneg (y-G x)) hxu 5
    nlinarith [show (2*‖y-G b‖)^5 = 32*‖y-G b‖^5 by ring]
  have he := setIntegral_mono_on
    (integrableOn_const (C := 1/‖y-G b‖^5)
      ((positionCube_isCompact b hh.le).measure_lt_top (μ := volume)).ne)
    (hi.const_mul 32) (positionCube_isClosed b h).measurableSet hp
  have hv : (volume.restrict (positionCube b h)).real Set.univ = h^3 := by
    simpa only [Measure.real,Measure.restrict_apply_univ] using positionCube_volume b hh.le
  simpa only [integral_const,smul_eq_mul,hv,integral_const_mul,div_eq_mul_inv,mul_one,one_mul] using he

theorem moser_inverseFifth_grid_sum_bound (hpublished : PublishedC4FlowInput)
    {rho H S : ℝ} (hrho : 0 < rho) (hH : 0 ≤ H) (hS : 0 ≤ S)
    (V : Position → ℝ) (hV : ContDiff ℝ 6 V)
    (hbound : ∀ x, |manufacturedCharge V x| ≤ rho/2)
    (hsupport : tsupport V ⊆ slabDomain H S)
    (G : Position → ℝ → Position) (hG : IsUnitTimeFlow (moserVelocity rho V) G)
    (hbij : Function.Bijective (fun x => G x 1))
    (hfix : ∀ x, x ∉ tsupport V → G x 1 = x)
    {L : ℝ≥0} (hL : 0 < L) (hLip : LipschitzWith L (fun x => G x 1))
    {ι : Type*} [Fintype ι] (index : ι → Fin 3 → ℤ) (hindex : Function.Injective index)
    {h : ℝ} (hh : 0 < h)
    (hsub : ∀ i, positionCube (gaussCellCenter h (index i)) h ⊆ slabDomain H S)
    (y : Position) (hfar : ∀ i, 4*(L:ℝ)*h ≤ ‖y-G (gaussCellCenter h (index i)) 1‖) :
    (∑ i, h^3/‖y-G (gaussCellCenter h (index i)) 1‖^5) ≤ 96*Real.pi/((L:ℝ)*h)^2 := by
  have hr : 0 < (L:ℝ)*h := mul_pos (by exact_mod_cast hL) hh
  calc
    _ ≤ ∑ i, 32*(∫ x in positionCube (gaussCellCenter h (index i)) h,
        inverseFifthTail ((L:ℝ)*h) (y-G x 1)) :=
      Finset.sum_le_sum (fun i _ => transported_inverseFifth_far_cube_bound hh
        (fun x => G x 1) hL hLip y _ (hfar i))
    _ = 32*(∑ i, ∫ x in positionCube (gaussCellCenter h (index i)) h,
        inverseFifthTail ((L:ℝ)*h) (y-G x 1)) := (Finset.mul_sum _ _ _).symm
    _ ≤ 32*(∫ x in slabDomain H S, inverseFifthTail ((L:ℝ)*h) (y-G x 1)) :=
      mul_le_mul_of_nonneg_left (grid_cell_integral_sum_le_on index hindex hh hsub _
        (transportedInverseFifth_integrableOn hH hS hr _ hLip.continuous y)
        (fun x => inverseFifthTail_nonneg _ _)) (by norm_num)
    _ ≤ 32*(3*Real.pi/((L:ℝ)*h)^2) := mul_le_mul_of_nonneg_left
      (moser_inverseFifth_tail_bound hpublished hrho V hV hbound hsupport G hG hbij hfix y hr)
      (by norm_num)
    _ = _ := by ring

end ContinuumCoulomb

end

end OAI
