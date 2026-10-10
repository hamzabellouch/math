import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.VerticalResidual
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.PlanarCutoffTail

namespace OAI

/-! Planar orbital coefficients on product L2, with exact contraction
and subtraction identities. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

def planarCoefficient (u : PlanarPosition) (f : SplitPosition → ℝ) (z : ℝ) : ℝ :=
  ∫ r, f (r,z)*normalizedPlanarMode (r-u)

theorem split_memLp_planar_slices (f : SplitPosition → ℝ) (hf : MemLp f 2) :
    ∀ᵐ z : ℝ, MemLp (fun r : PlanarPosition => f (r,z)) 2 := by
  have hp : MemLp f 2 ((volume : Measure PlanarPosition).prod (volume : Measure ℝ)) := by
    simpa only [Measure.volume_eq_prod] using hf
  filter_upwards [hp.aestronglyMeasurable.prodMk_right,hp.integrable_sq.prod_left_ae] with z hz hi
  exact (memLp_two_iff_integrable_sq hz).mpr hi

theorem planarCoefficient_contraction (u : PlanarPosition)
    (f : SplitPosition → ℝ) (hf : MemLp f 2) :
    MemLp (planarCoefficient u f) 2 ∧
      (∫ z, (planarCoefficient u f z)^2) ≤ ∫ p, f p^2 := by
  have hp : MemLp f 2 ((volume : Measure PlanarPosition).prod (volume : Measure ℝ)) := by
    simpa only [Measure.volume_eq_prod] using hf
  have hphi : MemLp (fun r => normalizedPlanarMode (r-u)) 2 :=
    normalizedPlanarMode_memLp.comp_measurePreserving (measurePreserving_sub_right volume u)
  have hm : AEStronglyMeasurable (planarCoefficient u f) volume :=
    (hp.aestronglyMeasurable.mul hphi.aestronglyMeasurable.comp_fst).prod_swap.integral_prod_right'
  have hdom : ∀ᵐ z : ℝ, (planarCoefficient u f z)^2 ≤ ∫ r : PlanarPosition, f (r,z)^2 := by
    filter_upwards [split_memLp_planar_slices f hf] with z hz
    have h := planar_l2_pair_sq_le (fun r => f (r,z))
      (fun r => normalizedPlanarMode (r-u)) hz hphi
    rw [integral_sub_right_eq_self (fun r => normalizedPlanarMode r^2) u,
      normalizedPlanarMode_normalized,mul_one] at h
    exact h
  have hi : Integrable (fun z : ℝ => ∫ r : PlanarPosition, f (r,z)^2) :=
    hp.integrable_sq.integral_prod_right
  have ha : Integrable (fun z => (planarCoefficient u f z)^2) :=
    hi.mono' (hm.pow 2) (hdom.mono (fun z hz => by
      simpa only [Real.norm_eq_abs,
        abs_of_nonneg (sq_nonneg (planarCoefficient u f z))] using hz))
  refine ⟨(memLp_two_iff_integrable_sq hm).mpr ha,?_⟩
  have h := integral_mono_ae ha hi hdom
  rw [← integral_prod_symm _ hp.integrable_sq] at h
  simpa only [Measure.volume_eq_prod] using h

theorem planarCoefficient_sub_ae (u : PlanarPosition)
    (f g : SplitPosition → ℝ) (hf : MemLp f 2) (hg : MemLp g 2) :
    planarCoefficient u (fun p => f p-g p) =ᵐ[volume]
      fun z => planarCoefficient u f z-planarCoefficient u g z := by
  have hphi : MemLp (fun r => normalizedPlanarMode (r-u)) 2 :=
    normalizedPlanarMode_memLp.comp_measurePreserving (measurePreserving_sub_right volume u)
  filter_upwards [split_memLp_planar_slices f hf,split_memLp_planar_slices g hg] with z hz hz'
  unfold planarCoefficient
  rw [show (fun r => (f (r,z)-g (r,z))*normalizedPlanarMode (r-u)) =
    (fun r => f (r,z)*normalizedPlanarMode (r-u)-g (r,z)*normalizedPlanarMode (r-u)) from
      funext (fun r => sub_mul _ _ _)]
  simpa only [Pi.mul_apply] using integral_sub (hz.integrable_mul hphi) (hz'.integrable_mul hphi)

theorem planarCoefficient_lift (u : PlanarPosition) (freq : ℝ)
    (a : PlanarPosition → ℝ) (z : ℝ) :
    planarCoefficient u (verticalLift freq a) z =
      (∫ r, a r*normalizedPlanarMode (r-u))*verticalMode freq z := by
  unfold planarCoefficient verticalLift
  rw [show (fun r => a r*verticalMode freq z*normalizedPlanarMode (r-u)) =
    (fun r => (a r*normalizedPlanarMode (r-u))*verticalMode freq z) from
      funext (fun r => by ring),integral_mul_const]

end ContinuumCoulomb

end

end OAI
