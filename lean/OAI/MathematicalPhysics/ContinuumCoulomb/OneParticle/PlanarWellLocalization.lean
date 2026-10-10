import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.PlanarIMSBounds

namespace OAI

/-! Exact localization of the actual sum of manufactured wells. Site
pieces see exactly their own well; the exterior piece sees zero potential. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

def planarWellSum {ι : Type*} [Fintype ι] (u : ι → PlanarPosition) (x : PlanarPosition) : ℝ :=
  ∑ i, manufacturedPlanarWell (x-u i)

theorem planarWellSum_continuous {ι : Type*} [Fintype ι] (u : ι → PlanarPosition) :
    Continuous (planarWellSum u) :=
  continuous_finsetSum _ (fun i _ => manufacturedPlanarWell_C7.continuous.comp
    (continuous_id.sub (continuous_const : Continuous (fun _ : PlanarPosition => u i))))

theorem manufacturedPlanarWell_zero_of_norm_ge_one {x : PlanarPosition} (hx : 1 ≤ ‖x‖) :
    manufacturedPlanarWell x = 0 := by
  simp only [manufacturedPlanarWell, planarForcing_zero_of_norm_ge_one hx, neg_zero, zero_div]

theorem planarSitePartition_exterior_inner {ι : Type*} [Fintype ι] {D : ℝ} (hD : 0 < D)
    (u : ι → PlanarPosition) (hsep : ∀ i j, i ≠ j → D ≤ ‖u i-u j‖)
    (i : ι) (x : PlanarPosition) (hx : ‖x-u i‖ ≤ D/8) :
    planarSitePartition D u none x = 0 := by
  have ha := planarSiteAngle_inner hD (u i) x hx
  have hs : x ∈ tsupport (planarSiteAngle D (u i)) := by
    apply subset_tsupport
    change planarSiteAngle D (u i) x ≠ 0
    rw [ha]
    exact div_ne_zero Real.pi_ne_zero (by norm_num)
  change planarTrigPartition (fun j => planarSiteAngle D (u j)) none x = 0
  rw [planarTrigPartition_exterior_at _ (planarSiteAngle_disjoint hD u hsep) hs,
    ha, Real.cos_pi_div_two]

theorem planarWellSum_site_product {ι : Type*} [Fintype ι] {D : ℝ} (hD : 8 ≤ D)
    (u : ι → PlanarPosition) (hsep : ∀ i j, i ≠ j → D ≤ ‖u i-u j‖)
    (i : ι) (x : PlanarPosition) :
    planarWellSum u x * planarSitePartition D u (some i) x =
      manufacturedPlanarWell (x-u i) * planarSitePartition D u (some i) x := by
  classical
  by_cases hz : planarSitePartition D u (some i) x = 0
  · rw [hz, mul_zero, mul_zero]
  have hangle : planarSiteAngle D (u i) x ≠ 0 := by
    intro ha
    exact hz (by simp only [planarSitePartition, planarTrigPartition, ha, Real.sin_zero])
  have hi := planarSiteAngle_support (by linarith : 0 < D) (u i) (subset_tsupport _ hangle)
  simp only [Metric.mem_closedBall, dist_eq_norm] at hi
  unfold planarWellSum
  rw [Finset.sum_mul, Finset.sum_eq_single i]
  · intro j _ hji
    have ht : ‖u i-u j‖ ≤ ‖x-u i‖ + ‖x-u j‖ := by
      simpa only [dist_eq_norm, norm_sub_rev (u i) x] using dist_triangle (u i) x (u j)
    have hs := hsep i j hji.symm
    rw [manufacturedPlanarWell_zero_of_norm_ge_one (by linarith : 1 ≤ ‖x-u j‖), zero_mul]
  · simp

theorem planarWellSum_exterior_product {ι : Type*} [Fintype ι] {D : ℝ} (hD : 8 ≤ D)
    (u : ι → PlanarPosition) (hsep : ∀ i j, i ≠ j → D ≤ ‖u i-u j‖)
    (x : PlanarPosition) : planarWellSum u x * planarSitePartition D u none x = 0 := by
  unfold planarWellSum
  rw [Finset.sum_mul]
  apply Finset.sum_eq_zero
  intro i _
  by_cases hi : 1 ≤ ‖x-u i‖
  · rw [manufacturedPlanarWell_zero_of_norm_ge_one hi, zero_mul]
  · have hx : ‖x-u i‖ ≤ D/8 := by push Not at hi; linarith
    rw [planarSitePartition_exterior_inner (by linarith : 0 < D) u hsep i x hx, mul_zero]

theorem planarTestForm_potential_product_congr (W V f : PlanarPosition → ℝ)
    (h : ∀ x, W x * f x = V x * f x) : planarTestForm W f = planarTestForm V f := by
  unfold planarTestForm
  congr 1
  apply integral_congr_ae
  filter_upwards [] with x
  simpa only [pow_two, ← mul_assoc] using congrArg (fun t : ℝ => t * f x) (h x)

theorem planarWellSum_localized_forms {ι : Type*} [Fintype ι] {D : ℝ} (hD : 8 ≤ D)
    (u : ι → PlanarPosition) (hsep : ∀ i j, i ≠ j → D ≤ ‖u i-u j‖)
    (f : PlanarPosition → ℝ) :
    (∑ i, planarTestForm (planarWellSum u) (fun x => planarSitePartition D u i x * f x)) =
      planarTestForm (fun _ => 0) (fun x => planarSitePartition D u none x * f x) +
        ∑ i, planarTestForm (fun x => manufacturedPlanarWell (x-u i))
          (fun x => planarSitePartition D u (some i) x * f x) := by
  rw [Fintype.sum_option]
  apply congrArg₂ (· + ·)
  · apply planarTestForm_potential_product_congr
    intro x
    rw [← mul_assoc, planarWellSum_exterior_product hD u hsep, zero_mul, zero_mul]
  · apply Finset.sum_congr rfl
    intro i _
    apply planarTestForm_potential_product_congr
    intro x
    rw [← mul_assoc, ← mul_assoc, planarWellSum_site_product hD u hsep]

theorem planarWellSum_localization_lower {ι : Type*} [Fintype ι] {D : ℝ} (hD : 8 ≤ D)
    (u : ι → PlanarPosition) (hsep : ∀ i j, i ≠ j → D ≤ ‖u i-u j‖)
    (f : PlanarPosition → ℝ) (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) :
    planarTestForm (fun _ => 0) (fun x => planarSitePartition D u none x * f x) +
        (∑ i, planarTestForm (fun x => manufacturedPlanarWell (x-u i))
          (fun x => planarSitePartition D u (some i) x * f x)) -
        planarSiteDerivativeBound D ^ 2 * (∫ x, f x ^ 2) ≤ planarTestForm (planarWellSum u) f := by
  have h := planarSitePartition_IMS_lower (by linarith : 0 < D) u hsep
    (planarWellSum u) f (planarWellSum_continuous u) hf hc
  rwa [planarWellSum_localized_forms hD u hsep f] at h

end ContinuumCoulomb

end

end OAI
