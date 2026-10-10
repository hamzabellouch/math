import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.PlaneHeatDataEquation
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.PlaneHeatInitialContinuity

namespace OAI

/-! Uniform time Lipschitz bounds for bounded smooth Gaussian evolutions. -/

noncomputable section
namespace ForcedComputation.PlaneHeat
open Real MeasureTheory Set Filter ShearFlows
open scoped Topology ContDiff BigOperators NNReal

variable (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

omit [CompleteSpace F] in
theorem norm_heatConvolution_le {t : ℝ} (ht : 0 < t) {f : Plane → F}
    (hf : Continuous f) (C : ℝ) (hC : ∀ x, ‖f x‖ ≤ C) (x : Plane) :
    ‖heatConvolution F t f x‖ ≤ C := by
  rw [heatConvolution_eq]
  have h := BoundedKernel.norm_convolve_le Plane F volume (kernel t) f
    (kernel_integrable ht) hf C hC x
  simpa only [abs_of_nonneg (kernel_nonneg t _), kernel_integral ht, mul_one] using h

omit [CompleteSpace F] in
theorem evolution_time_hasDerivAt_pos {f : Plane → F} (hf : ContDiff ℝ ∞ f)
    (C D E : ℝ) (hC : ∀ x, ‖f x‖ ≤ C)
    (hD : ∀ j x, ‖spatialPartial F j f x‖ ≤ D)
    (hE : ∀ j x, ‖spatialPartial F j (spatialPartial F j f) x‖ ≤ E)
    {t : ℝ} (ht : 0 < t) (x : Plane) :
    HasDerivAt (fun s => evolution F f s x)
      (∑ j : Fin 2, heatConvolution F t (spatialPartial F j (spatialPartial F j f)) x) t := by
  apply (hasDerivAt_heatConvolution_data F ht hf C D E hC hD hE x).congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds ht] with s hs
  exact ite_eq_right (not_le.mpr hs)

theorem evolution_time_continuous {f : Plane → F}
    {L : ℝ≥0} (hL : LipschitzWith L f) (C : ℝ) (hC : ∀ x, ‖f x‖ ≤ C) (x : Plane) :
    Continuous (fun t => evolution F f t x) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  rcases lt_trichotomy t 0 with ht | rfl | ht
  · apply (show ContinuousAt (fun _ : ℝ => f x) t from continuousAt_const).congr
    filter_upwards [Iio_mem_nhds ht] with s hs
    change s < 0 at hs
    exact (ite_eq_left hs.le).symm
  · apply continuousAt_iff_continuous_left'_right'.mpr
    constructor
    · apply continuousWithinAt_const.congr
      · intro s hs
        change s < 0 at hs
        exact ite_eq_left hs.le
      · exact ite_eq_left le_rfl
    · change Tendsto (fun t => evolution F f t x) (𝓝[>] 0) (𝓝 (evolution F f 0 x))
      simpa only [evolution, ite_eq_left le_rfl] using
        (evolution_tendsto_uniformly F hL C hC).tendsto_at x
  · apply (hasDerivAt_heatConvolution F ht f hL.continuous C hC x).continuousAt.congr
    filter_upwards [Ioi_mem_nhds ht] with s hs
    change 0 < s at hs
    exact (ite_eq_right (not_le.mpr hs)).symm

theorem evolution_time_lipschitz {f : Plane → F} (hf : ContDiff ℝ ∞ f)
    {L : ℝ≥0} (hL : LipschitzWith L f) (C D E : ℝ) (hC : ∀ x, ‖f x‖ ≤ C)
    (hD : ∀ j x, ‖spatialPartial F j f x‖ ≤ D)
    (hE : ∀ j x, ‖spatialPartial F j (spatialPartial F j f) x‖ ≤ E) (x : Plane) :
    LipschitzWith (Real.nnabs (2*E)) (fun t => evolution F f t x) := by
  have hE0 : 0 ≤ E := (norm_nonneg _).trans (hE 0 0)
  have hpos : LipschitzOnWith (Real.nnabs (2*E)) (fun t => evolution F f t x) (Ioi 0) := by
    apply (convex_Ioi (0:ℝ)).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
      (fun t ht => (evolution_time_hasDerivAt_pos F hf C D E hC hD hE ht x).hasDerivWithinAt)
    intro t ht
    rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_nnabs, abs_of_nonneg (by positivity : 0 ≤ 2*E)]
    calc
      _ ≤ ∑ j : Fin 2, ‖heatConvolution F t (spatialPartial F j (spatialPartial F j f)) x‖ :=
        norm_sum_le _ _
      _ ≤ ∑ _j : Fin 2, E := Finset.sum_le_sum fun j _ =>
        norm_heatConvolution_le F ht (partial_smooth F (partial_smooth F hf j) j).continuous E (hE j) x
      _ = 2*E := by simp
  have hclosed : LipschitzOnWith (Real.nnabs (2*E)) (fun t => evolution F f t x) (Ici 0) := by
    have h := LipschitzOnWith.closure
      (show ContinuousOn (fun t => evolution F f t x) (closure (Ioi (0:ℝ))) from
        (evolution_time_continuous F hL C hC x).continuousOn) hpos
    simpa only [closure_Ioi] using h
  have he (t : ℝ) : evolution F f (max t 0) x = evolution F f t x := by
    by_cases ht : 0 ≤ t
    · rw [max_eq_left ht]
    · rw [max_eq_right (le_of_not_ge ht)]
      simp only [evolution, ite_eq_left le_rfl, ite_eq_left (le_of_not_ge ht)]
  apply LipschitzWith.of_dist_le_mul
  intro s t
  rw [← he s, ← he t]
  exact (hclosed.dist_le_mul (max s 0) (show max s 0 ∈ Ici (0:ℝ) from le_max_right s 0)
    (max t 0) (show max t 0 ∈ Ici (0:ℝ) from le_max_right t 0)).trans
    (mul_le_mul_of_nonneg_left (by simpa only [Real.dist_eq] using abs_max_sub_max_le_abs s t 0)
      (NNReal.coe_nonneg _))

end ForcedComputation.PlaneHeat

end

end OAI
