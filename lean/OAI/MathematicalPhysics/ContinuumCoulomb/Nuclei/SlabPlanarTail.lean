import OAI.MathematicalPhysics.ContinuumCoulomb.Nuclei.SlabPlanarIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

namespace OAI

/-! The inverse-cube tail in two horizontal dimensions. Its exact mass is
`2π/H`, giving the finite-slab truncation error without divergent integrals. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

def slabRadialTail (H r : ℝ) : ℝ :=
  (Set.Ioi H).indicator (fun t : ℝ => t ^ (-3 : ℝ)) r

def slabPlanarTail (H : ℝ) (p : PlanarPosition) : ℝ := slabRadialTail H ‖p‖

private theorem slabRadialTail_weight {H : ℝ} (hH : 0 < H) (r : ℝ) :
    r * slabRadialTail H r = (Set.Ioi H).indicator (fun t : ℝ => t ^ (-2 : ℝ)) r := by
  by_cases hr : H < r
  · simp only [slabRadialTail, Set.indicator_of_mem (Set.mem_Ioi.mpr hr)]
    have hp : 0 < r := hH.trans hr
    rw [show (-2 : ℝ) = -3+1 by norm_num, Real.rpow_add hp, Real.rpow_one]
    ring
  · simp [slabRadialTail, hr]

private theorem slabRadialTail_weight_integrable {H : ℝ} (hH : 0 < H) :
    IntegrableOn (fun r : ℝ => r * slabRadialTail H r) (Set.Ioi 0) := by
  have hi := integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hH
  have h := (integrable_indicator_iff measurableSet_Ioi).mpr hi
  simpa only [slabRadialTail_weight hH] using h.integrableOn

private theorem slabRadialTail_weight_integral {H : ℝ} (hH : 0 < H) :
    (∫ r in Set.Ioi (0:ℝ), r * slabRadialTail H r) = H⁻¹ := by
  simp_rw [slabRadialTail_weight hH]
  rw [integral_indicator measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi]
  rw [Set.Ioi_inter_Ioi, max_eq_left hH.le]
  have h := integral_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hH
  convert h using 1
  norm_num
  rw [Real.rpow_neg_one]

theorem slabPlanarTail_integrable {H : ℝ} (hH : 0 < H) :
    Integrable (slabPlanarTail H) := by
  apply (integrable_fun_norm_addHaar (E := PlanarPosition) volume
    (f := slabRadialTail H)).mpr
  simp only [finrank_euclideanSpace_fin, Nat.reduceSub, pow_one, smul_eq_mul]
  exact slabRadialTail_weight_integrable hH

theorem slabPlanarTail_nonnegative (H : ℝ) (p : PlanarPosition) :
    0 ≤ slabPlanarTail H p := by
  unfold slabPlanarTail slabRadialTail
  by_cases h : H < ‖p‖
  · rw [Set.indicator_of_mem (Set.mem_Ioi.mpr h)]
    exact Real.rpow_nonneg (norm_nonneg p) _
  · simp [h]

/-- The exact horizontal inverse-cube tail mass. -/
theorem slabPlanarTail_integral {H : ℝ} (hH : 0 < H) :
    (∫ p, slabPlanarTail H p) = 2*Real.pi/H := by
  have h := integral_fun_norm_addHaar (E := PlanarPosition) volume (slabRadialTail H)
  simp only [finrank_euclideanSpace_fin, Nat.reduceSub, pow_one, smul_eq_mul,
    nsmul_eq_mul] at h
  have hm : volume.real (Metric.ball (0 : PlanarPosition) 1) = Real.pi := by
    simp [Measure.real, EuclideanSpace.volume_ball_fin_two, ENNReal.toReal_ofReal Real.pi_pos.le]
  rw [hm, slabRadialTail_weight_integral hH] at h
  change (∫ p, slabRadialTail H ‖p‖) = _
  convert h using 1
  norm_num
  ring

def slabPlanarBox (H : ℝ) : Set PlanarPosition :=
  {p | |p 0| ≤ H ∧ |p 1| ≤ H}

theorem slabPlanarBox_measurable (H : ℝ) : MeasurableSet (slabPlanarBox H) := by
  have h0 : IsClosed {p : PlanarPosition | |p 0| ≤ H} :=
    isClosed_le (by fun_prop) continuous_const
  have h1 : IsClosed {p : PlanarPosition | |p 1| ≤ H} :=
    isClosed_le (by fun_prop) continuous_const
  exact (h0.inter h1).measurableSet

theorem slabPlanarBox_compl_norm {H : ℝ} {p : PlanarPosition}
    (hp : p ∉ slabPlanarBox H) : H < ‖p‖ := by
  by_contra h
  have hn : ‖p‖ ≤ H := le_of_not_gt h
  apply hp
  have h0 : |p 0| ≤ ‖p‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le p 0
  have h1 : |p 1| ≤ ‖p‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le p 1
  exact ⟨h0.trans hn, h1.trans hn⟩

theorem slab_regularized_line_difference_uniform {R S epsilon z w : ℝ}
    (hR : 0 < R) (hz : |z| ≤ S) (hw : |w| ≤ S) :
    |coulombLineKernel (epsilon^2+(z-w)^2) R -
      coulombLineKernel (epsilon^2+w^2) R| ≤ 3*S^2/(2*R^3) := by
  have h := reciprocal_sqrt_difference_bound hR
    (show R^2 ≤ (epsilon^2+(z-w)^2)+R^2 by nlinarith [sq_nonneg epsilon, sq_nonneg (z-w)])
    (show R^2 ≤ (epsilon^2+w^2)+R^2 by nlinarith [sq_nonneg epsilon, sq_nonneg w])
  have hS : 0 ≤ S := (abs_nonneg z).trans hz
  have hz2 : z^2 ≤ S^2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg z) hS).mpr hz
  have hzw : |z*w| ≤ S^2 := by
    rw [abs_mul, pow_two]
    exact mul_le_mul hz hw (abs_nonneg w) hS
  have ha : |(epsilon^2+(z-w)^2+R^2)-(epsilon^2+w^2+R^2)| ≤ 3*S^2 := by
    rw [show (epsilon^2+(z-w)^2+R^2)-(epsilon^2+w^2+R^2) = z^2-2*(z*w) by ring]
    apply (abs_sub _ _).trans
    rw [abs_of_nonneg (sq_nonneg z), abs_mul, abs_of_pos (by norm_num : (0:ℝ)<2)]
    linarith
  exact h.trans (div_le_div_of_nonneg_right ha (by positivity))

/-- The finite square loses at most the integrable radial tail. -/
theorem slabPlanarDifference_tail_bound {H S epsilon z w : ℝ} (hH : 0 < H)
    (hepsilon : epsilon ≠ 0) (hz : |z| ≤ S) (hw : |w| ≤ S) :
    |∫ p in (slabPlanarBox H)ᶜ,
      (coulombLineKernel (epsilon^2+(z-w)^2) ‖p‖-
       coulombLineKernel (epsilon^2+w^2) ‖p‖)| ≤ 3*Real.pi*S^2/H := by
  let f := fun p : PlanarPosition =>
    coulombLineKernel (epsilon^2+(z-w)^2) ‖p‖-
      coulombLineKernel (epsilon^2+w^2) ‖p‖
  have hA : 0 < epsilon^2+(z-w)^2 := add_pos_of_pos_of_nonneg
    (sq_pos_of_ne_zero hepsilon) (sq_nonneg _)
  have hB : 0 < epsilon^2+w^2 := add_pos_of_pos_of_nonneg
    (sq_pos_of_ne_zero hepsilon) (sq_nonneg _)
  have hi : Integrable f := slabPlanarDifference_integrable hA hB
  have ht : Integrable (fun p => (3*S^2/2)*slabPlanarTail H p) :=
    (slabPlanarTail_integrable hH).const_mul _
  have hpt (p : PlanarPosition) (hp : p ∈ (slabPlanarBox H)ᶜ) :
      ‖f p‖ ≤ (3*S^2/2)*slabPlanarTail H p := by
    have hn := slabPlanarBox_compl_norm hp
    have hn0 : 0 < ‖p‖ := hH.trans hn
    have hbound := slab_regularized_line_difference_uniform (epsilon := epsilon) hn0 hz hw
    rw [Real.norm_eq_abs]
    change |coulombLineKernel (epsilon^2+(z-w)^2) ‖p‖-
      coulombLineKernel (epsilon^2+w^2) ‖p‖| ≤ _
    unfold slabPlanarTail slabRadialTail
    rw [Set.indicator_of_mem (Set.mem_Ioi.mpr hn), Real.rpow_neg (norm_nonneg p), Real.rpow_ofNat]
    convert hbound using 1
    ring
  have hm : (∫ p in (slabPlanarBox H)ᶜ, ‖f p‖) ≤
      ∫ p in (slabPlanarBox H)ᶜ, (3*S^2/2)*slabPlanarTail H p :=
    setIntegral_mono_on hi.norm.integrableOn ht.integrableOn
      (slabPlanarBox_measurable H).compl hpt
  have hall : (∫ p in (slabPlanarBox H)ᶜ, (3*S^2/2)*slabPlanarTail H p) ≤
      ∫ p, (3*S^2/2)*slabPlanarTail H p :=
    setIntegral_le_integral ht (Filter.Eventually.of_forall
      (fun p => mul_nonneg (by positivity) (slabPlanarTail_nonnegative H p)))
  calc
    _ = ‖∫ p in (slabPlanarBox H)ᶜ, f p‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∫ p in (slabPlanarBox H)ᶜ, ‖f p‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ p, (3*S^2/2)*slabPlanarTail H p := hm.trans hall
    _ = _ := by rw [integral_const_mul, slabPlanarTail_integral hH]; ring

/-- The finite horizontal square differs from the infinite-plane formula by
at most the inverse-cube tail. -/
theorem slabPlanarDifference_estimate {H S epsilon z w : ℝ} (hH : 0 < H)
    (hepsilon : epsilon ≠ 0) (hz : |z| ≤ S) (hw : |w| ≤ S) :
    |(∫ p in slabPlanarBox H,
       (coulombLineKernel (epsilon^2+(z-w)^2) ‖p‖-
        coulombLineKernel (epsilon^2+w^2) ‖p‖)) -
      2*Real.pi*(Real.sqrt (epsilon^2+w^2)-Real.sqrt (epsilon^2+(z-w)^2))| ≤
        3*Real.pi*S^2/H := by
  have hA : 0 < epsilon^2+(z-w)^2 := add_pos_of_pos_of_nonneg
    (sq_pos_of_ne_zero hepsilon) (sq_nonneg _)
  have hB : 0 < epsilon^2+w^2 := add_pos_of_pos_of_nonneg
    (sq_pos_of_ne_zero hepsilon) (sq_nonneg _)
  have hs := integral_add_compl (slabPlanarBox_measurable H)
    (slabPlanarDifference_integrable hA hB)
  rw [slabPlanarDifference_integral hA hB] at hs
  have he : (∫ p in slabPlanarBox H,
       (coulombLineKernel (epsilon^2+(z-w)^2) ‖p‖-
        coulombLineKernel (epsilon^2+w^2) ‖p‖)) -
      2*Real.pi*(Real.sqrt (epsilon^2+w^2)-Real.sqrt (epsilon^2+(z-w)^2)) =
      -(∫ p in (slabPlanarBox H)ᶜ,
       (coulombLineKernel (epsilon^2+(z-w)^2) ‖p‖-
        coulombLineKernel (epsilon^2+w^2) ‖p‖)) := by linarith
  rw [he, abs_neg]
  exact slabPlanarDifference_tail_bound hH hepsilon hz hw

end ContinuumCoulomb

end

end OAI
