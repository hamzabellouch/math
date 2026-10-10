import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.PlanarLaplaceIBP
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.PlanarModeDerivatives

namespace OAI

/-! The differential eigen-equation of the constructed resolvent mode is
obtained from its heat representation and the fundamental theorem of calculus,
not supplied as an assumption. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators
namespace ContinuumCoulomb

theorem planarResolvent_joint_integrable {g : PlanarPosition → ℝ}
    (hg : Continuous g) (hc : HasCompactSupport g) (r : PlanarPosition) :
    Integrable (fun p : ℝ × PlanarPosition => planarResolventIntegrand p * g (r - p.2))
      ((volume.restrict (Set.Ioi (0 : ℝ))).prod (volume : Measure PlanarPosition)) := by
  obtain ⟨B, hB⟩ := hg.bounded_above_of_compact_support hc
  apply planarResolventIntegrand_integrable.mul_bdd
    ((hg.comp (continuous_const.sub continuous_snd)).aestronglyMeasurable)
  exact Eventually.of_forall (fun p => by
    change ‖g (r - p.2)‖ ≤ B
    exact hB _)

theorem planarResolventOf_heat_representation {g : PlanarPosition → ℝ}
    (hg : Continuous g) (hc : HasCompactSupport g) (r : PlanarPosition) :
    planarResolventOf g r = ∫ t in Set.Ioi (0 : ℝ),
      Real.exp (-t) * ∫ b, planarHeatKernel t b * g (r - b) := by
  unfold planarResolventOf planarResolventKernel
  simp_rw [← integral_mul_const]
  rw [← integral_integral_swap (planarResolvent_joint_integrable hg hc r)]
  simp_rw [planarResolventIntegrand, mul_assoc, integral_const_mul]

theorem planarResolventOf_heat_integrable {g : PlanarPosition → ℝ}
    (hg : Continuous g) (hc : HasCompactSupport g) (r : PlanarPosition) :
    IntegrableOn (fun t => Real.exp (-t) * ∫ b, planarHeatKernel t b * g (r - b))
      (Set.Ioi (0 : ℝ)) := by
  have h := (planarResolvent_joint_integrable hg hc r).integral_prod_left
  change Integrable _ _
  simpa only [planarResolventIntegrand, mul_assoc, integral_const_mul] using h

theorem planarResolventMode_laplacian_integral (r : PlanarPosition) :
    planarLaplacian planarResolventMode r = planarResolventOf (planarLaplacian planarForcing) r := by
  have hi (a : Fin 2) : Integrable (fun b => planarResolventKernel b *
      planarPartial (planarPartial planarForcing (planarAxis a)) (planarAxis a) (r - b)) :=
    ((planarForcing_hasCompactSupport.fderiv_apply ℝ (planarAxis a)).fderiv_apply ℝ
      (planarAxis a)).convolutionExists_right (ContinuousLinearMap.mul ℝ ℝ)
      planarResolventKernel_integrable.locallyIntegrable
      (planarPartial_continuous (planarPartial_C1 (planarForcing_C7.of_le (by norm_num)) _) _) r
  unfold planarLaplacian
  simp_rw [planarResolventMode_partial_partial]
  change (∑ a : Fin 2, ∫ b, planarResolventKernel b *
      planarPartial (planarPartial planarForcing (planarAxis a)) (planarAxis a) (r - b)) =
    ∫ b, planarResolventKernel b * ∑ a : Fin 2,
      planarPartial (planarPartial planarForcing (planarAxis a)) (planarAxis a) (r - b)
  rw [← integral_finsetSum _ (fun a _ => hi a)]
  simp only [Finset.mul_sum]

def planarHeatResolventPrimitive (r : PlanarPosition) (t : ℝ) : ℝ :=
  if t = 0 then planarForcing r else Real.exp (-t) * planarHeatAverage t r

def planarHeatResolventDerivative (r : PlanarPosition) (t : ℝ) : ℝ :=
  Real.exp (-t) * (∫ b, planarHeatKernel t b * planarLaplacian planarForcing (r - b)) -
    Real.exp (-t) * planarHeatAverage t r

@[simp] theorem planarHeatResolventPrimitive_zero (r : PlanarPosition) :
    planarHeatResolventPrimitive r 0 = planarForcing r := by
  simp [planarHeatResolventPrimitive]

theorem planarHeatResolventPrimitive_hasDerivAt (r : PlanarPosition) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (planarHeatResolventPrimitive r) (planarHeatResolventDerivative r t) t := by
  have he : HasDerivAt (fun s : ℝ => Real.exp (-s)) (-Real.exp (-t)) t := by
    simpa only [Pi.neg_apply, id_eq, mul_neg, mul_one] using (hasDerivAt_id t).neg.exp
  have hd := he.mul (planarHeatAverage_hasDerivAt_laplacian ht r)
  have hd' : HasDerivAt (fun s => Real.exp (-s) * planarHeatAverage s r)
      (planarHeatResolventDerivative r t) t := by
    convert hd using 1
    dsimp [planarHeatResolventDerivative]
    ring
  apply hd'.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds ht] with s hs
  simp only [planarHeatResolventPrimitive, ite_eq_right (show s ≠ 0 from (show 0 < s from hs).ne')]

theorem planarHeatResolventPrimitive_continuousWithinAt (r : PlanarPosition) :
    ContinuousWithinAt (planarHeatResolventPrimitive r) (Set.Ici (0 : ℝ)) 0 := by
  have he : Tendsto (fun t : ℝ => Real.exp (-t)) (𝓝[>] 0) (𝓝 1) := by
    have he0 : Tendsto (fun t : ℝ => Real.exp (-t)) (𝓝 (0 : ℝ)) (𝓝 (Real.exp (-0))) :=
      (Real.continuous_exp.comp continuous_neg).continuousAt.tendsto
    simpa only [neg_zero, Real.exp_zero] using
      he0.mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
  have hlim := he.mul (planarHeatAverage_tendsto_zero r)
  apply continuousWithinAt_Ioi_iff_Ici.mp
  change Tendsto _ _ (𝓝 (planarHeatResolventPrimitive r 0))
  rw [planarHeatResolventPrimitive_zero]
  have hlim' : Tendsto (fun t => Real.exp (-t) * planarHeatAverage t r)
      (𝓝[>] (0 : ℝ)) (𝓝 (planarForcing r)) := by simpa only [one_mul] using hlim
  apply hlim'.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  simp only [planarHeatResolventPrimitive, ite_eq_right (show t ≠ 0 from (show 0 < t from ht).ne')]

theorem planarHeatResolventDerivative_integrable (r : PlanarPosition) :
    IntegrableOn (planarHeatResolventDerivative r) (Set.Ioi (0 : ℝ)) :=
  (planarResolventOf_heat_integrable
    (planarLaplacian_continuous (planarForcing_C7.of_le (by norm_num)))
    (planarLaplacian_hasCompactSupport planarForcing_hasCompactSupport) r).sub
    (planarResolventMode_heat_integrable r)

theorem planarHeatResolventPrimitive_integrable (r : PlanarPosition) :
    IntegrableOn (planarHeatResolventPrimitive r) (Set.Ioi (0 : ℝ)) := by
  apply (planarResolventMode_heat_integrable r).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  simp only [planarHeatResolventPrimitive, ite_eq_right (show t ≠ 0 from (show 0 < t from ht).ne')]

theorem planarResolventMode_equation (r : PlanarPosition) :
    planarLaplacian planarResolventMode r = planarResolventMode r - planarForcing r := by
  have hd := fun t (ht : t ∈ Set.Ioi (0 : ℝ)) => planarHeatResolventPrimitive_hasDerivAt r ht
  have hzero := tendsto_zero_of_hasDerivAt_of_integrableOn_Ioi hd
    (planarHeatResolventDerivative_integrable r) (planarHeatResolventPrimitive_integrable r)
  have hFTC := integral_Ioi_of_hasDerivAt_of_tendsto
    (planarHeatResolventPrimitive_continuousWithinAt r) hd
    (planarHeatResolventDerivative_integrable r) hzero
  have hL := planarResolventOf_heat_representation
    (planarLaplacian_continuous (planarForcing_C7.of_le (by norm_num)))
    (planarLaplacian_hasCompactSupport planarForcing_hasCompactSupport) r
  have hLi := planarResolventOf_heat_integrable
    (planarLaplacian_continuous (planarForcing_C7.of_le (by norm_num)))
    (planarLaplacian_hasCompactSupport planarForcing_hasCompactSupport) r
  simp only [planarHeatResolventDerivative, planarHeatResolventPrimitive_zero, zero_sub,
    integral_sub hLi (planarResolventMode_heat_integrable r), ← hL,
    ← planarResolventMode_heat_representation, ← planarResolventMode_laplacian_integral] at hFTC
  linarith

theorem manufacturedPlanarWell_eigen_equation (r : PlanarPosition) :
    planarLaplacian planarResolventMode r =
      (2 * manufacturedPlanarWell r + 1) * planarResolventMode r := by
  rw [planarResolventMode_equation]
  unfold manufacturedPlanarWell
  field_simp [(planarResolventMode_positive r).ne']
  ring

theorem manufacturedPlanarWell_test_lower (u : PlanarPosition → ℝ)
    (hu : ContDiff ℝ 1 u) (hc : HasCompactSupport u) :
    -(1 / 2 : ℝ) * (∫ x, u x ^ 2) ≤ planarTestForm manufacturedPlanarWell u :=
  planar_positive_mode_form_lower planarResolventMode manufacturedPlanarWell u
    (planarResolventMode_C7.of_le (by norm_num)) planarResolventMode_positive
    manufacturedPlanarWell_C7.continuous manufacturedPlanarWell_eigen_equation hu hc

end ContinuumCoulomb

end

end OAI
