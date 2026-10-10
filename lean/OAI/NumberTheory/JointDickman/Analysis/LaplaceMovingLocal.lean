import OAI.NumberTheory.JointDickman.Analysis.LaplaceMovingCutoff
import OAI.NumberTheory.JointDickman.Analysis.LaplaceIntegrability

namespace OAI

/-! # Replacing a fixed local Hankel cutoff by the moving contour width -/
namespace JointDickman
open MeasureTheory Set Filter Asymptotics
open scoped Topology

theorem laplace_cutoff_difference_bound {z L C r δ : ℝ}
    (hz1 : z < 1) (hL : 0 < L) (hC : 0 ≤ C) (hδ : 0 ≤ δ) (hδr : δ ≤ r)
    (f : ℝ → ℂ) (hf : AEStronglyMeasurable f (volume.restrict (Ioc 0 r)))
    (hbound : ∀ t ∈ Ioc 0 r, ‖f t‖ ≤ C) :
    ‖(∫ t : ℝ in Ioc 0 r, (t^(-z)*Real.exp (-(L*t))) • f t) -
      (∫ t : ℝ in Ioc 0 δ, (t^(-z)*Real.exp (-(L*t))) • f t)‖ ≤
      C*(∫ t : ℝ in Ioi δ, t^(-z)*Real.exp (-(L*t))) := by
  let W : ℝ → ℂ := fun t => (t^(-z)*Real.exp (-(L*t))) • f t
  have h0r := laplace_weighted_integrable hz1 hL 0 f hf
    (by simpa only [pow_zero,mul_one] using hbound)
  have h0δ : IntegrableOn W (Ioc 0 δ) :=
    h0r.mono_set (Ioc_subset_Ioc_right hδr)
  have hδr' : IntegrableOn W (Ioc δ r) :=
    h0r.mono_set (Ioc_subset_Ioc_left hδ)
  have heq : (∫ t : ℝ in Ioc 0 r, W t) - (∫ t : ℝ in Ioc 0 δ, W t) =
      ∫ t : ℝ in Ioc δ r, W t := by
    have hs := intervalIntegral.integral_add_adjacent_intervals
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le hδ).mpr h0δ)
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le hδr).mpr hδr')
    simp only [intervalIntegral.integral_of_le hδ,intervalIntegral.integral_of_le hδr,
      intervalIntegral.integral_of_le (hδ.trans hδr)] at hs
    exact sub_eq_of_eq_add' hs.symm
  change ‖(∫ t : ℝ in Ioc 0 r, W t) - (∫ t : ℝ in Ioc 0 δ, W t)‖ ≤ _
  rw [heq]
  have hmajor : IntegrableOn (fun t : ℝ => C*(t^(-z)*Real.exp (-(L*t)))) (Ioi δ) := by
    have hmajor0 : IntegrableOn (fun t : ℝ => C*(t^(-z)*Real.exp (-(L*t)))) (Ioi 0) := by
      simpa only [IntegrableOn,Nat.cast_zero,zero_sub] using
        (fractional_laplace_integrable hz1 hL 0).const_mul C
    exact hmajor0.mono_set (Ioi_subset_Ioi hδ)
  calc
    _ ≤ ∫ t : ℝ in Ioc δ r, C*(t^(-z)*Real.exp (-(L*t))) := by
      apply norm_integral_le_of_norm_le (hmajor.mono_set Ioc_subset_Ioi_self)
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      have ht0 : 0 < t := hδ.trans_lt ht.1
      have hweight : 0 ≤ t^(-z)*Real.exp (-(L*t)) :=
        mul_nonneg (Real.rpow_nonneg ht0.le _) (Real.exp_pos _).le
      dsimp only [W]
      rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hweight]
      calc
        _ ≤ (t^(-z)*Real.exp (-(L*t)))*C :=
          mul_le_mul_of_nonneg_left (hbound t ⟨hδ.trans_lt ht.1,ht.2⟩) hweight
        _ = _ := mul_comm _ _
    _ ≤ ∫ t : ℝ in Ioi δ, C*(t^(-z)*Real.exp (-(L*t))) := by
      apply setIntegral_mono_set hmajor
      · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        have ht0 : 0 < t := hδ.trans_lt ht
        exact mul_nonneg hC (mul_nonneg (Real.rpow_nonneg ht0.le _) (Real.exp_pos _).le)
      · exact Eventually.of_forall (fun t ht => ht.1)
    _ = _ := integral_const_mul C _

theorem laplace_moving_local_isLittleO {z C r a α : ℝ} (hz1 : z < 1)
    (hC : 0 ≤ C) (ha : 0 < a) (hα : 0 < α)
    (f : ℝ → ℂ) (hf : AEStronglyMeasurable f (volume.restrict (Ioc 0 r)))
    (hbound : ∀ t ∈ Ioc 0 r, ‖f t‖ ≤ C) {η : ℝ → ℝ}
    (hη : ∀ᶠ L in atTop, 0 ≤ η L ∧ η L ≤ r)
    (hgrowth : ∀ᶠ L in atTop, a*L^α ≤ L*η L/2) (b : ℝ) :
    (fun L : ℝ => (∫ t : ℝ in Ioc 0 r, (t^(-z)*Real.exp (-(L*t))) • f t) -
      (∫ t : ℝ in Ioc 0 (η L), (t^(-z)*Real.exp (-(L*t))) • f t))
      =o[atTop] (fun L => L^b) := by
  apply IsBigO.trans_isLittleO (g := fun L : ℝ =>
    ∫ t : ℝ in Ioi (η L), t^(-z)*Real.exp (-(L*t))) _
    (by simpa only [Nat.cast_zero,zero_sub] using
      fractional_laplace_moving_tail_isLittleO hz1 ha hα (hη.mono fun _ h => h.1) hgrowth 0 b)
  apply isBigO_iff.mpr ⟨C,?_⟩
  filter_upwards [eventually_gt_atTop (0:ℝ),hη] with L hL hηL
  exact (laplace_cutoff_difference_bound hz1 hL hC hηL.1 hηL.2 f hf hbound).trans
    (mul_le_mul_of_nonneg_left (le_abs_self _) hC)

end JointDickman

end OAI
