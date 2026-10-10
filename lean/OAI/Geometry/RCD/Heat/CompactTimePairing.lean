import Mathlib.Analysis.Calculus.ParametricIntegral

namespace OAI

/-! # Differentiating compact spatial pairings

Joint continuity on compact interior cylinders supplies the domination
needed for differentiation against any integrable spatial test.
-/

open Set Filter MeasureTheory
open scoped Topology
noncomputable section
namespace RegularPointCoordinates
variable {Y : Type*} [MetricSpace Y] [CompactSpace Y]
  [MeasurableSpace Y] [BorelSpace Y] (μ : Measure Y)

theorem compact_weighted_integrable (φ : Y → ℝ) (hφ : Integrable φ μ)
    (h : Y → ℝ) (hh : Continuous h) : Integrable (fun y => φ y * h y) μ := by
  obtain ⟨C,hC⟩ := isCompact_univ.exists_bound_of_continuousOn hh.continuousOn
  exact hφ.mul_bdd hh.aestronglyMeasurable (Eventually.of_forall fun y => hC y (mem_univ y))

theorem compact_time_pairing_continuousOn (H : ℝ → Y → ℝ) {a b : ℝ}
    (hH : ContinuousOn (Function.uncurry H) (Icc a b ×ˢ univ))
    (φ : Y → ℝ) (hφ : Integrable φ μ) :
    ContinuousOn (fun t => ∫ y, φ y * H t y ∂μ) (Icc a b) := by
  obtain ⟨C,hC⟩ := (isCompact_Icc.prod isCompact_univ).exists_bound_of_continuousOn hH
  refine continuousOn_of_dominated (μ := μ) (F := fun t y => φ y * H t y)
    (bound := fun y => |φ y| * C) ?_ ?_ (hφ.abs.mul_const C) ?_
  · intro t ht
    have hc : Continuous (H t) := continuousOn_univ.mp
      (hH.comp (continuous_const.prodMk continuous_id).continuousOn
        (fun y _ => ⟨ht,mem_univ y⟩))
    exact hφ.aestronglyMeasurable.mul hc.aestronglyMeasurable
  · intro t ht
    exact Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs,abs_mul]
      exact mul_le_mul_of_nonneg_left (hC (t,y) ⟨ht,mem_univ y⟩) (abs_nonneg _)
  · exact Eventually.of_forall fun y => continuousOn_const.mul
      (hH.comp (continuous_id.prodMk continuous_const).continuousOn
        (fun t ht => ⟨ht,mem_univ y⟩))

theorem compact_time_pairing_hasDerivAt (H D : ℝ → Y → ℝ)
    (hH : ContinuousOn (Function.uncurry H) (Ioi 0 ×ˢ univ))
    (hD : ContinuousOn (Function.uncurry D) (Ioi 0 ×ˢ univ))
    (hd : ∀ t, 0 < t → ∀ y, HasDerivAt (fun s => H s y) (D t y) t)
    (φ : Y → ℝ) (hφ : Integrable φ μ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s => ∫ y, φ y * H s y ∂μ) (∫ y, φ y * D t y ∂μ) t := by
  let I := Icc (t/2) (t+1)
  have hI : I ∈ 𝓝 t := Icc_mem_nhds (by linarith) (by linarith)
  have hpos : ∀ s ∈ I, 0 < s := fun s hs => (half_pos ht).trans_le hs.1
  have hcH (s : ℝ) (hs : 0 < s) : Continuous (H s) := continuousOn_univ.mp
    (hH.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun y _ => ⟨hs,mem_univ y⟩))
  have hcD : Continuous (D t) := continuousOn_univ.mp
    (hD.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun y _ => ⟨ht,mem_univ y⟩))
  obtain ⟨C,hC⟩ := (isCompact_Icc.prod isCompact_univ).exists_bound_of_continuousOn
    (hD.mono (show I ×ˢ univ ⊆ Ioi 0 ×ˢ univ from fun q hq => ⟨hpos q.1 hq.1,hq.2⟩))
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ)
    (F := fun s y => φ y*H s y) (F' := fun s y => φ y*D s y)
    (bound := fun y => |φ y| * C) hI ?_
    (compact_weighted_integrable μ φ hφ (H t) (hcH t ht))
    (hφ.aestronglyMeasurable.mul hcD.aestronglyMeasurable) ?_
    (hφ.abs.mul_const C) ?_).2
  · filter_upwards [Ioi_mem_nhds ht] with s hs
    exact hφ.aestronglyMeasurable.mul (hcH s hs).aestronglyMeasurable
  · exact Eventually.of_forall fun y s hs => by
      rw [Real.norm_eq_abs,abs_mul]
      exact mul_le_mul_of_nonneg_left (hC (s,y) ⟨hs,mem_univ y⟩) (abs_nonneg _)
  · exact Eventually.of_forall fun y s hs => (hd s (hpos s hs) y).const_mul (φ y)

end RegularPointCoordinates

end

end OAI
