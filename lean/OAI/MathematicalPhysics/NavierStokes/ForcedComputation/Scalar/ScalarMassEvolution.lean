import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.ScalarMassCalculus
import OAI.MathematicalPhysics.NavierStokes.ShearFlows.EnergyCalculus

namespace OAI

/-! The scalar's total mass changes only by the prescribed source. -/

noncomputable section
namespace ForcedComputation.VelocityDetector
open ShearFlows Set MeasureTheory Filter
open scoped ContDiff Topology

def scalarMass (w : ℝ → Plane → ℝ) (t : ℝ) : ℝ :=
  ∫ x in Icc (0 : Plane) (fun _ => 1), w t x

theorem scalarMass_continuous {w : ℝ → Plane → ℝ}
    (hw : Continuous (Function.uncurry w)) : Continuous (scalarMass w) := by
  exact continuous_parametric_integral_of_continuous hw isCompact_Icc

theorem scalarMass_hasDerivAt {w d : ℝ → Plane → ℝ}
    (hw : Continuous (Function.uncurry w)) (hd : Continuous (Function.uncurry d))
    (hderiv : ∀ s x, HasDerivAt (fun r => w r x) (d s x) s) (t : ℝ) :
    HasDerivAt (scalarMass w) (scalarMass d t) t := by
  let K : Set Plane := Icc 0 (fun _ => 1)
  obtain ⟨B, hB⟩ := (isCompact_Icc.prod (isCompact_Icc (a := (0 : Plane))
    (b := fun _ => 1))).bddAbove_image
      (hd.norm.continuousOn (s := Icc (t - 1) (t + 1) ×ˢ K))
  have hbound : ∀ᵐ x ∂(volume.restrict K),
      ∀ s ∈ Ioo (t - 1) (t + 1), ‖d s x‖ ≤ B := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    intro s hs
    exact hB (mem_image_of_mem (fun y : ℝ × Plane => ‖d y.1 y.2‖)
      (show (s, x) ∈ Icc (t - 1) (t + 1) ×ˢ K from ⟨Ioo_subset_Icc_self hs, hx⟩))
  have hmeas : ∀ᶠ s in 𝓝 t,
      AEStronglyMeasurable (w s) (volume.restrict K) := by
    exact Eventually.of_forall (fun s =>
      (hw.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable)
  have hint : IntegrableOn (w t) K :=
    (hw.comp (continuous_const.prodMk continuous_id)).integrableOn_Icc
  have hdmeas : AEStronglyMeasurable (d t) (volume.restrict K) :=
    (hd.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Ioo_mem_nhds (by linarith) (by linarith)) hmeas hint hdmeas hbound
    (by exact integrableOn_const (s := K) (hs := isCompact_Icc.measure_lt_top.ne))
    (Eventually.of_forall (fun x s _ => hderiv s x))).2

theorem scalarMass_source_derivative {ν : ℝ}
    {a : ℝ → Plane → Plane} {h w d : ℝ → Plane → ℝ}
    (hw : ContDiff ℝ ∞ (Function.uncurry w))
    (hd : Continuous (Function.uncurry d))
    (ha : ∀ t, ContDiff ℝ ∞ (a t))
    (hpa : ∀ t, PlanePeriodic (a t)) (hpw : ∀ t, PlanePeriodic (w t))
    (hdiv : ∀ t x, PlanarHamiltonian.divergence (a t) x = 0)
    (hderiv : ∀ t x, HasDerivAt (fun s => w s x) (d t x) t)
    (he : ∀ t x, d t x = scalarGenerator ν (a t) (w t) x + h t x)
    (hh : ∀ t, Continuous (h t)) (t : ℝ) :
    HasDerivAt (scalarMass w) (scalarMass h t) t := by
  have hws : ContDiff ℝ ∞ (w t) :=
    hw.comp (contDiff_const.prodMk contDiff_id)
  have hG : Continuous (fun x => scalarGenerator ν (a t) (w t) x) := by
    apply Continuous.sub
    · apply Continuous.const_mul
      apply continuous_finsetSum
      intro j _
      exact (PlanarHamiltonian.spatialD_smooth j
        (PlanarHamiltonian.spatialD_smooth j hws)).continuous
    · exact ((hws.fderiv_right (m := ∞) (by simp)).clm_apply (ha t)).continuous
  have hi : scalarMass d t = scalarMass h t := by
    unfold scalarMass
    simp_rw [he t]
    rw [integral_add hG.integrableOn_Icc (hh t).integrableOn_Icc,
      scalarGenerator_integral_zero (ha t) hws (hpa t) (hpw t) (hdiv t) ν,
      zero_add]
  exact hi ▸ scalarMass_hasDerivAt hw.continuous hd hderiv t

end ForcedComputation.VelocityDetector

end

end OAI
