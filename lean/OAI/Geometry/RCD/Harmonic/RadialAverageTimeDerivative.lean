import OAI.Geometry.RCD.Harmonic.RadialContinuousL2Time
import OAI.Geometry.RCD.Coordinates.TimeAverageLinearMap

namespace OAI

/-! # The L2 derivative of the actual averaged Sobolev family

The countable exceptional times disappear under integration. The
derivative is represented by the exact endpoint difference of values.
-/

open Set Filter MeasureTheory Metric
open scoped Topology NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) [IsFiniteMeasureOnCompacts μ] (Q : QuadraticCheegerEnergy μ)

theorem radial_average_L2_derivative
    {a b : ℝ} (v : Ioo a b → SobolevSpace μ Q)
    (hv : AEStronglyMeasurable v (volume.comap Subtype.val))
    {C : ℝ} (hb : ∀ q, ‖v q‖ ≤ C)
    (z : X) {r : ℝ} (hr : 0 < r) (H : ℝ → X → ℝ) {L : ℝ≥0}
    (hH : LipschitzOnWith L (Function.uncurry H) (Ioo a b ×ˢ closedBall z (2*r)))
    (N : Set ℝ) (hN : N.Countable)
    (hrep : ∀ q : Ioo a b, (q:ℝ) ∉ N → SobolevSpace.toLp μ Q (v q) =ᵐ[μ]
      fun x => radialCutoff z r x*H q x)
    {h t : ℝ} (hh : 0 < h) (ha : a < t-h) (hb' : t+h < b) :
    ∃ D : Lp ℝ 2 μ,
      HasDerivAt (fun s => SobolevSpace.toLp μ Q
        (timeIntervalAverage (intervalVectorExtension v) h s)) D t ∧
      D =ᵐ[μ] fun x => radialCutoff z r x*((H (t+h) x-H (t-h) x)/(2*h)) := by
  obtain ⟨g,-,hg,hgc⟩ := radial_continuous_L2_time_family μ Q z hr H hH
  let T := SobolevSpace.toLpCLM μ Q
  let u := intervalVectorExtension v
  let G := intervalVectorExtension g
  have he : (fun s => T (u s)) =ᵐ[volume] G := by
    filter_upwards [hN.ae_notMem volume] with s hs
    by_cases hmem : s ∈ Ioo a b
    · change T (intervalVectorExtension v s) = intervalVectorExtension g s
      simp only [intervalVectorExtension,dite_eq_left hmem]
      exact Lp.ext ((hrep ⟨s,hmem⟩ hs).trans (hg ⟨s,hmem⟩).symm)
    · simp only [u,G,intervalVectorExtension,dite_eq_right hmem,map_zero]
  have hp : t+h ∈ Ioo a b := ⟨by linarith,hb'⟩
  have hm : t-h ∈ Ioo a b := ⟨ha,by linarith⟩
  let D := (2*h)⁻¹ • (G (t+h)-G (t-h))
  refine ⟨D,timeIntervalAverage_map_hasDerivAt T u
    (intervalVectorExtension_integrable v hv hb) G he h t
    (hgc.continuousAt (isOpen_Ioo.mem_nhds hp))
    (hgc.continuousAt (isOpen_Ioo.mem_nhds hm)),?_⟩
  have hGp : G (t+h) = g ⟨t+h,hp⟩ := intervalVectorExtension_eq g ⟨t+h,hp⟩
  have hGm : G (t-h) = g ⟨t-h,hm⟩ := intervalVectorExtension_eq g ⟨t-h,hm⟩
  dsimp only [D]
  rw [hGp,hGm]
  filter_upwards [Lp.coeFn_smul ((2*h)⁻¹) (g ⟨t+h,hp⟩-g ⟨t-h,hm⟩),
    Lp.coeFn_sub (g ⟨t+h,hp⟩) (g ⟨t-h,hm⟩),hg ⟨t+h,hp⟩,hg ⟨t-h,hm⟩]
    with x hx hsub hplus hminus
  rw [hx,Pi.smul_apply,hsub,Pi.sub_apply,hplus,hminus]
  simp only [smul_eq_mul,div_eq_mul_inv]
  ring

end RegularPointCoordinates

end

end OAI
