import OAI.Analysis.CircleDomains.Rigidity.MatchedInnerCircleFlux
import Mathlib.Analysis.Complex.MeanValue

namespace OAI

/-! Reassembling the four geometric quarter circles into the usual
circle average. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem quadrantPoint_true_true (r θ : ℝ) :
    quadrantPoint 0 r true true θ = circleMap 0 r θ := by
  apply Complex.ext <;> simp [quadrantPoint,quadrantNormal,quadrantSign,circleMap_zero_re,circleMap_zero_im]

 theorem quadrantPoint_false_true (r θ : ℝ) :
    quadrantPoint 0 r false true θ = circleMap 0 r (Real.pi-θ) := by
  apply Complex.ext <;> simp [quadrantPoint,quadrantNormal,quadrantSign,circleMap_zero_re,circleMap_zero_im]

 theorem quadrantPoint_false_false (r θ : ℝ) :
    quadrantPoint 0 r false false θ = circleMap 0 r (Real.pi+θ) := by
  apply Complex.ext <;> simp [quadrantPoint,quadrantNormal,quadrantSign,circleMap_zero_re,circleMap_zero_im,
    Real.cos_add,Real.sin_add]

 theorem quadrantPoint_true_false (r θ : ℝ) :
    quadrantPoint 0 r true false θ = circleMap 0 r (2*Real.pi-θ) := by
  apply Complex.ext <;> simp [quadrantPoint,quadrantNormal,quadrantSign,circleMap_zero_re,circleMap_zero_im,
    Real.cos_two_pi_sub,Real.sin_two_pi_sub]

 theorem integral_four_quadrants {H : ℂ → ℂ} {r : ℝ} (hr : 0 ≤ r)
    (hH : ContinuousOn H (closedBall 0 r)) :
    (∫ θ in (0 : ℝ)..(Real.pi/2), ∑ s : Bool, ∑ t : Bool, H (quadrantPoint 0 r s t θ)) =
      ∫ θ in (0 : ℝ)..(2*Real.pi), H (circleMap 0 r θ) := by
  let f := fun θ => H (circleMap 0 r θ)
  have hf : Continuous f := hH.comp_continuous (continuous_circleMap 0 r) (by
    intro θ
    simp only [mem_closedBall,dist_zero_right,norm_circleMap_zero,abs_of_nonneg hr,le_refl])
  have e (θ : ℝ) : (∑ s : Bool, ∑ t : Bool, H (quadrantPoint 0 r s t θ)) =
      f θ+f (Real.pi-θ)+f (Real.pi+θ)+f (2*Real.pi-θ) := by
    simp only [Fintype.sum_bool,quadrantPoint_false_false,quadrantPoint_false_true,
      quadrantPoint_true_false,quadrantPoint_true_true]
    dsimp only [f]
    abel
  have h1 : IntervalIntegrable f volume 0 (Real.pi/2) := hf.intervalIntegrable (0 : ℝ) (Real.pi/2)
  have h2 : IntervalIntegrable (fun θ => f (Real.pi-θ)) volume 0 (Real.pi/2) := (hf.comp (continuous_const.sub continuous_id)).intervalIntegrable (0 : ℝ) (Real.pi/2)
  have h3 : IntervalIntegrable (fun θ => f (Real.pi+θ)) volume 0 (Real.pi/2) := (hf.comp (continuous_const.add continuous_id)).intervalIntegrable (0 : ℝ) (Real.pi/2)
  have h4 : IntervalIntegrable (fun θ => f (2*Real.pi-θ)) volume 0 (Real.pi/2) := (hf.comp (continuous_const.sub continuous_id)).intervalIntegrable (0 : ℝ) (Real.pi/2)
  have e2 : (∫ θ in (0 : ℝ)..(Real.pi/2), f (Real.pi-θ)) =
      ∫ θ in (Real.pi/2)..Real.pi, f θ := by
    rw [intervalIntegral.integral_comp_sub_left]
    congr 1 <;> ring
  have e3 : (∫ θ in (0 : ℝ)..(Real.pi/2), f (Real.pi+θ)) =
      ∫ θ in Real.pi..(3*Real.pi/2), f θ := by
    rw [intervalIntegral.integral_comp_add_left]
    congr 1 <;> ring
  have e4 : (∫ θ in (0 : ℝ)..(Real.pi/2), f (2*Real.pi-θ)) =
      ∫ θ in (3*Real.pi/2)..(2*Real.pi), f θ := by
    rw [intervalIntegral.integral_comp_sub_left]
    congr 1 <;> ring
  simp_rw [e]
  rw [intervalIntegral.integral_add ((h1.add h2).add h3) h4,
    intervalIntegral.integral_add (h1.add h2) h3,intervalIntegral.integral_add h1 h2,e2,e3,e4,
    intervalIntegral.integral_add_adjacent_intervals (hf.intervalIntegrable _ _) (hf.intervalIntegrable _ _),
    intervalIntegral.integral_add_adjacent_intervals (hf.intervalIntegrable _ _) (hf.intervalIntegrable _ _),
    intervalIntegral.integral_add_adjacent_intervals (hf.intervalIntegrable _ _) (hf.intervalIntegrable _ _)]

end CircleDomainRigidity

end

end OAI
