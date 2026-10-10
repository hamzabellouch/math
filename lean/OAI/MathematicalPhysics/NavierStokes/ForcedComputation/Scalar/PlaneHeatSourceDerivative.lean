import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.PlaneHeatTimeLipschitz
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.VolterraDifferentiation

namespace OAI

/-! Differentiation of the actual inhomogeneous Gaussian heat integral. -/

noncomputable section
namespace ForcedComputation.PlaneHeat
open ShearFlows Set Filter MeasureTheory
open scoped Topology NNReal ContDiff Interval BigOperators

variable (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

theorem hasDerivAt_heat_source {ν t : ℝ} (hν : 0 < ν) (ht : 0 < t)
    (g : ℝ → Plane → F) (hg : ∀ s, ContDiff ℝ ∞ (g s))
    (L : ℝ≥0) (hL : ∀ s, LipschitzWith L (g s)) (C D E : ℝ)
    (hC : ∀ s x, ‖g s x‖ ≤ C)
    (hD : ∀ s j x, ‖spatialPartial F j (g s) x‖ ≤ D)
    (hE : ∀ s j x, ‖spatialPartial F j (spatialPartial F j (g s)) x‖ ≤ E)
    (x : Plane)
    (hc : Continuous (fun p : ℝ × ℝ => evolution F (g p.2) (ν*(p.1-p.2)) x))
    (hdc : Continuous (fun s => ν • ∑ j : Fin 2,
      evolution F (spatialPartial F j (spatialPartial F j (g s))) (ν*(t-s)) x)) :
    HasDerivAt (fun u => ∫ s in 0..u, evolution F (g s) (ν*(u-s)) x)
      ((∫ s in 0..t, ν • ∑ j : Fin 2,
        evolution F (spatialPartial F j (spatialPartial F j (g s))) (ν*(t-s)) x) + g t x) t := by
  have hE0 : 0 ≤ E := (norm_nonneg _).trans (hE 0 0 0)
  have htime (s : ℝ) : LipschitzWith (Real.nnabs (2*E*ν))
      (fun r => evolution F (g s) (ν*(r-s)) x) := by
    apply LipschitzWith.of_dist_le_mul
    intro r u
    have hh := (evolution_time_lipschitz F (hg s) (hL s) C D E
      (hC s) (hD s) (hE s) x).dist_le_mul (ν*(r-s)) (ν*(u-s))
    convert! hh using 1
    simp only [Real.coe_nnabs, Real.dist_eq, ← mul_sub, sub_sub_sub_cancel_right,
      abs_mul, abs_of_pos hν, abs_of_nonneg (by positivity : 0 ≤ 2*E)]
    ring
  have hd : HasDerivAt (fun u => ∫ s in 0..t, evolution F (g s) (ν*(u-s)) x)
      (∫ s in 0..t, ν • ∑ j : Fin 2,
        evolution F (spatialPartial F j (spatialPartial F j (g s))) (ν*(t-s)) x) t := by
    refine (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_lip
      (μ := volume) (s := univ) (bound := fun _ => 2*E*ν)
      (F' := fun s => ν • ∑ j : Fin 2,
        evolution F (spatialPartial F j (spatialPartial F j (g s))) (ν*(t-s)) x)
      univ_mem ?_ ?_ hdc.aestronglyMeasurable.restrict ?_ ?_ ?_).2
    · exact Eventually.of_forall fun u =>
        (hc.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable.restrict
    · exact (hc.comp (continuous_const.prodMk continuous_id)).intervalIntegrable 0 t
    · exact ae_of_all _ fun s _ => (htime s).lipschitzOnWith
    · exact intervalIntegrable_const
    · filter_upwards [volume.ae_ne t] with s hs hst
      rw [uIoc_of_le ht.le] at hst
      have hst' : s < t := lt_of_le_of_ne hst.2 hs
      have hh := (evolution_time_hasDerivAt_pos F (hg s) C D E
        (hC s) (hD s) (hE s) (mul_pos hν (sub_pos.mpr hst')) x).scomp t
          (((hasDerivAt_id t).sub_const s).const_mul ν)
      convert! hh using 1
      simp only [mul_one]
      apply congrArg (fun z : F => ν • z)
      apply Finset.sum_congr rfl
      intro j _
      rw [evolution, ite_eq_right (not_le.mpr (mul_pos hν (sub_pos.mpr hst')))]
  convert! hasDerivAt_volterra_of_fixed F
    (fun u s => evolution F (g s) (ν*(u-s)) x) hc 0 t _ hd using 1
  simp only [sub_self, mul_zero, evolution, le_refl, ite_true]

end ForcedComputation.PlaneHeat

end

end OAI
