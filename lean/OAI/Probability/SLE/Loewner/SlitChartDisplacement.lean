import OAI.Probability.SLE.Loewner.SlitChartBoundaryBasics
import OAI.Probability.SLE.Loewner.HalfPlaneDisplacementBound

namespace OAI

/-! Quantitative comparison of the actual normalized inverse slit charts. -/
noncomputable section
open Set Filter Function
open scoped Topology

namespace SLEExactGauge

lemma SimpleSlitChart.inverse_displacement {p : C(unitInterval,ℂ)} (P : SimpleSlitChart p)
    {z : ℂ} (hz : z∈upperHalfPlane) : ‖P.inverse z-z‖≤P.capacity/z.im := by
  apply nonnegative_im_hydrodynamic_bound (P.inverse_differentiable.sub differentiableOn_id)
    (fun w hw => by
      change 0 ≤ (P.inverse w-w).im
      simpa only [Complex.sub_im] using sub_nonneg.mpr (P.inverse_im_ge hw))
    P.capacity_pos.le
    (inverse_hydrodynamic_coefficient P.coefficient P.inverse_normalized P.right_inverse) hz

lemma SimpleSlitChart.forward_displacement {p : C(unitInterval,ℂ)} (P : SimpleSlitChart p)
    {z : ℂ} (hz : z∈upperHalfPlane \ range p) :
    ‖P.forward z-z‖≤P.capacity/(P.forward z).im := by
  have hh := P.inverse_displacement (P.bijOn.mapsTo hz)
  simpa only [P.left_inverse z hz,norm_sub_rev] using hh

lemma SimpleSlitChart.inverse_comparison {p q : C(unitInterval,ℂ)}
    (P : SimpleSlitChart p) (Q : SimpleSlitChart q) (hpq : range p ⊆ range q)
    {z : ℂ} (hz : z∈upperHalfPlane) :
    ‖P.forward (Q.inverse z)-z‖≤(Q.capacity-P.capacity)/z.im := by
  have hdom : upperHalfPlane \ range q ⊆ upperHalfPlane \ range p :=
    fun _ hw => ⟨hw.1,fun hp => hw.2 (hpq hp)⟩
  have hm := Q.inverse_mapsTo.mono_right hdom
  have hd := P.forward_differentiable.comp Q.inverse_differentiable hm
  have hn := hydrodynamic_composition_ratio P.coefficient Q.inverse_normalized
  apply nonnegative_im_hydrodynamic_bound (hd.sub differentiableOn_id)
    (fun w hw => by
      change 0 ≤ (P.forward (Q.inverse w)-w).im
      simpa only [Function.comp_apply,Complex.sub_im] using sub_nonneg.mpr
        (normalized_halfPlane_height hd (P.bijOn.mapsTo.comp hm) hn hw))
    (sub_nonneg.mpr (P.capacity_le_of_range_subset Q hpq))
  · have hh := hydrodynamic_composition_coefficient P.coefficient Q.coefficient
      Q.inverse_normalized Q.right_inverse
    have he : -((Q.capacity-P.capacity:ℝ):ℂ) = (P.capacity:ℂ)-Q.capacity := by
      push_cast
      ring
    change Tendsto (fun w : ℂ => w*(P.forward (Q.inverse w)-w))
      (cocompact ℂ ⊓ 𝓟 upperHalfPlane) (𝓝 (-((Q.capacity-P.capacity:ℝ):ℂ)))
    rw [he]
    exact hh
  · exact hz

end SLEExactGauge

end

end OAI
