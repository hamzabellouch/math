import OAI.Geometry.RCD.Coordinates.TimeIntervalAverage

namespace OAI

/-! # Compatibility of time averages with the actual Sobolev inclusion -/

open Set Filter MeasureTheory
open scoped Topology
noncomputable section
namespace RegularPointCoordinates
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

theorem timeIntervalAverage_map (T : E →L[ℝ] F) (u : ℝ → E) (hu : Integrable u)
    (h t : ℝ) :
    T (timeIntervalAverage u h t) = timeIntervalAverage (fun s => T (u s)) h t := by
  rw [timeIntervalAverage,timeIntervalAverage,map_smul,
    T.intervalIntegral_comp_comm hu.intervalIntegrable]

omit [CompleteSpace E] in
theorem timeIntervalAverage_congr_ae (u v : ℝ → E) (he : u =ᵐ[volume] v) (h : ℝ) :
    timeIntervalAverage u h = timeIntervalAverage v h := by
  funext t
  rw [timeIntervalAverage,timeIntervalAverage]
  congr 1
  exact intervalIntegral.integral_congr_ae (he.mono fun _ hx _ => hx)

theorem timeIntervalAverage_map_hasDerivAt (T : E →L[ℝ] F)
    (u : ℝ → E) (hu : Integrable u) (v : ℝ → F)
    (hv : (fun s => T (u s)) =ᵐ[volume] v) (h t : ℝ)
    (hp : ContinuousAt v (t+h)) (hm : ContinuousAt v (t-h)) :
    HasDerivAt (fun s => T (timeIntervalAverage u h s))
      ((2*h)⁻¹ • (v (t+h)-v (t-h))) t := by
  have hi : Integrable v := (T.integrable_comp hu).congr hv
  have he : (fun s => T (timeIntervalAverage u h s)) = timeIntervalAverage v h := by
    funext s
    rw [timeIntervalAverage_map T u hu,
      timeIntervalAverage_congr_ae (fun s => T (u s)) v hv]
  rw [he]
  exact timeIntervalAverage_hasDerivAt v hi h t hp hm

end RegularPointCoordinates

end

end OAI
