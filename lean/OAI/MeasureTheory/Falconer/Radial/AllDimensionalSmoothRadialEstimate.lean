import OAI.MeasureTheory.Falconer.Radial.HyperplaneTrace
import OAI.MeasureTheory.Falconer.Radial.HyperplaneMixedEnergy
import OAI.MeasureTheory.Falconer.Radial.EuclideanRadialDensity

namespace OAI

/-! The all-dimensional smooth radial moment estimate. -/

namespace Falconer
open Set MeasureTheory PlanarFalconer
open scoped ENNReal

theorem smooth_euclidean_radial_moment_bound (n : ℕ) {s t p q D : ℝ}
    (hs0 : 0 < s) (hs : (n : ℝ) < s) (hsn : s < n+1) (hs2 : s < 2*n)
    (ht : 0 < t) (hpq : p.HolderConjugate q) (hp2 : p < 2)
    (hupt : (2*n-s)*p < t) (htr : t/(2-p) < n) (hD : 0 < D) :
    ∃ C : ℝ≥0∞, C < ∞ ∧ ∀ (a : Space (n+1) → ℝ)
      (_hc : HasCompactSupport a) (_ha : ContDiff ℝ (⊤ : ℕ∞) a) (_hn : ∀ x, 0 ≤ a x)
      (β : Measure (Space (n+1))) [IsFiniteMeasure β],
      (∀ᵐ z : Space (n+1) × Space (n+1) ∂β.prod β, dist z.1 z.2 ≤ D) →
      (∀ᵐ x ∂β, ∀ y, a y ≠ 0 → dist y x ≤ D) →
      (∫⁻ x, ∫⁻ w : Sphere (n+1),
        (euclideanRadialDensity (fun y => ENNReal.ofReal (a y)) x w)^p
          ∂sphereMeasure (n+1) ∂β) ≤
        C * (rieszEnergyOn β t)^(1/2 : ℝ) * (rieszEnergyOn (euclideanDensityMeasure a) s)^(p/2) := by
  have hp1 : 1 < p := (Real.holderConjugate_iff.mp hpq).1
  obtain ⟨M,hM,hmix⟩ := hyperplane_mixed_energy_bound n hs0 hs hsn ht hp1 hp2 htr
  let c : ℝ≥0∞ := (ENNReal.ofReal (sourceEnergyConstant n (2*n-s)))^(p/2)
  let A : ℝ≥0∞ := (ENNReal.ofReal (D^n))^p *
    (ENNReal.ofReal (D^(t-(2*n-s)*p)))^(1/2 : ℝ)
  have hc0 : c ≠ 0 := (ENNReal.rpow_pos (ENNReal.ofReal_pos.mpr
    (sourceEnergyConstant_pos (by linarith) (by linarith))) ENNReal.ofReal_ne_top).ne'
  have hct : c ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg (by linarith [hpq.pos]) ENNReal.ofReal_ne_top
  have hAt : A < ∞ := ENNReal.mul_lt_top
    (ENNReal.rpow_lt_top_of_nonneg hpq.nonneg ENNReal.ofReal_ne_top)
    (ENNReal.rpow_lt_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top)
  refine ⟨c⁻¹*A*M, ENNReal.mul_lt_top (ENNReal.mul_lt_top
    (ENNReal.inv_lt_top.mpr (bot_lt_iff_ne_bot.mpr hc0)) hAt) hM, ?_⟩
  intro a hc ha hn β hβ hdiam hbound
  let α := euclideanDensityMeasure a
  let : IsFiniteMeasure α := euclideanDensityMeasure_finite a hc ha.continuous hn
  let R := fun (x : Space (n+1)) (w : Sphere (n+1)) =>
    euclideanRadialDensity (fun y => ENNReal.ofReal (a y)) x w
  let F := fun w : Sphere (n+1) =>
    ∫⁻ y : Space n, (hyperplaneFiberDensity (fun x => ENNReal.ofReal (a x)) w y)^p
      ∂hyperplaneCoordinateMeasure β w
  let T := fun w : Sphere (n+1) =>
    (rieszEnergyOn (hyperplaneProjectedMeasure β w) t)^(1/2 : ℝ) *
      (hyperplaneEnergyMajorant α s w)^(p/2)
  have hR : Measurable (Function.uncurry R) :=
    euclideanRadialDensity_joint_measurable _ ha.continuous.measurable.ennreal_ofReal
  have hfiber (w : Sphere (n+1)) : (∫⁻ x, (R x w)^p ∂β) ≤
      (ENNReal.ofReal (D^n))^p * F w := by
    calc
      _ ≤ ∫⁻ x, (ENNReal.ofReal (D^n))^p *
          (hyperplaneFiberDensity (fun y => ENNReal.ofReal (a y)) w
            (hyperplaneProjection w x))^p ∂β := by
        apply lintegral_mono_ae
        filter_upwards [hbound] with x hx
        have h := euclideanRadialDensity_le_fiber (fun y => ENNReal.ofReal (a y)) x
          (fun y hy => hx y (by intro hz; exact hy (by simp [hz]))) w
        simpa only [ENNReal.mul_rpow_of_nonneg _ _ hpq.nonneg] using
          ENNReal.rpow_le_rpow h hpq.nonneg
      _ = (ENNReal.ofReal (D^n))^p * F w := by
        rw [lintegral_const_mul' _ _
          (ENNReal.rpow_ne_top_of_nonneg hpq.nonneg ENNReal.ofReal_ne_top)]
        congr 1
        exact (lintegral_map
          ((hyperplaneFiberDensity_measurable _ ha.continuous.measurable.ennreal_ofReal w).pow_const p)
          (contDiff_hyperplaneProjection w).continuous.measurable).symm
  have htrace (w : Sphere (n+1)) : c * F w ≤
      (ENNReal.ofReal (D^(t-(2*n-s)*p)))^(1/2 : ℝ) * T w := by
    apply (hyperplane_smooth_fiber_bound a hc ha hn β hpq hs hs2 hD hupt hdiam w).trans
    exact (mul_le_mul_right (ENNReal.rpow_le_rpow
      (hyperplaneFourierEnergy_le_majorant α hs w) (by linarith [hpq.pos])) _).trans_eq
        (by dsimp [T]; ac_rfl)
  have hpoint (w : Sphere (n+1)) : c * (∫⁻ x, (R x w)^p ∂β) ≤ A * T w := by
    calc
      _ ≤ c * ((ENNReal.ofReal (D^n))^p * F w) := mul_le_mul_right (hfiber w) c
      _ = (ENNReal.ofReal (D^n))^p * (c * F w) := by ac_rfl
      _ ≤ (ENNReal.ofReal (D^n))^p *
          ((ENNReal.ofReal (D^(t-(2*n-s)*p)))^(1/2 : ℝ) * T w) :=
        mul_le_mul_right (htrace w) _
      _ = _ := by dsimp [A]; ac_rfl
  have htot : c * (∫⁻ x, ∫⁻ w : Sphere (n+1), (R x w)^p ∂sphereMeasure (n+1) ∂β) ≤
      A * M * (rieszEnergyOn β t)^(1/2 : ℝ) * (rieszEnergyOn α s)^(p/2) := by
    rw [lintegral_lintegral_swap (hR.pow_const p).aemeasurable,
      ← lintegral_const_mul' _ _ hct]
    apply (lintegral_mono hpoint).trans
    rw [lintegral_const_mul' _ _ hAt.ne]
    exact (mul_le_mul_right (hmix α β) A).trans_eq (by ac_rfl)
  have h := mul_le_mul_right htot c⁻¹
  rw [← mul_assoc, ENNReal.inv_mul_cancel hc0 hct, one_mul] at h
  exact h.trans_eq (by ac_rfl)

end Falconer

end OAI
