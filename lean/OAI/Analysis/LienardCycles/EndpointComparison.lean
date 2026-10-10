import OAI.Analysis.LienardCycles.RiccatiComparison

namespace OAI

open Set Filter Metric
open scoped Topology NNReal ContDiff Manifold
open Filter Set
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff
open Set Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace QuinticLienard.ModelEndpoint
open Set Filter
open scoped Topology ContDiff
open PartialCalculus QuadraticCoordinates RiccatiJets

theorem LowerChart.formulas {d k r : ℝ} (hr : 0 < r) (c : LowerChart d k r) :
    schwarzian c.upper (m ((d,k),r)) =
      k*(m ((d,k),r)+n ((d,k),r)*(ell ((d,k),r))^2)+
      (d^2/2)*((ell ((d,k),r))^2-1)-
      d*(1/m ((d,k),r)+(ell ((d,k),r))^2/n ((d,k),r))+
      (3/2)*((ell ((d,k),r))^2/(n ((d,k),r))^2-1/(m ((d,k),r))^2) ∧
    deriv (deriv c.upper) (m ((d,k),r))/ell ((d,k),r) =
      1/m ((d,k),r)-ell ((d,k),r)/n ((d,k),r)+d*(1+ell ((d,k),r))+
      k*m ((d,k),r)*(∫ y in (-m ((d,k),r))..(n ((d,k),r)),
        1/(Riccati.multiplier (fun s => c.solution (m ((d,k),r),s)) (k/2) d
          (-m ((d,k),r)) y)^2) := by
  have hn : 0 < c.upper (m ((d,k),r)) := by rw [c.upper_base]; exact n_pos hr
  have hl : 0 < deriv c.upper (m ((d,k),r)) := by
    rw [c.upper_derivative.deriv]; exact ell_pos hr
  have hu : ∀ y ∈ Icc (-m ((d,k),r)) (c.upper (m ((d,k),r))),
      ContDiffAt ℝ ω c.solution (m ((d,k),r),y) := by
    rw [c.upper_base]; exact c.solution_analytic
  have he : ∀ y ∈ Icc (-m ((d,k),r)) (c.upper (m ((d,k),r))),
      ∀ᶠ q in 𝓝 (m ((d,k),r),y), HasDerivAt (fun s => c.solution (q.1,s))
        (d*c.solution q+(k/2)*(c.solution q)^2-q.2) q.2 := by
    rw [c.upper_base]; exact c.equation
  have hh := RiccatiJets.endpoint_formulas (m_pos hr) hn hl
    (c.solution_continuous _) hu he c.upper_analytic c.lower_zero c.upper_zero
  rw [c.upper_base,c.upper_derivative.deriv] at hh
  constructor
  · convert hh.1 using 1; ring
  · convert hh.2.1 using 1; ring

theorem LowerChart.variation_bound {d k r ν : ℝ} (hr : 0 < r)
    (hk : 0 < k) (hd : d < 0) (hν : 0 ≤ ν)
    (hνsq : ν^2=d^2/4-(k/2)*m ((d,k),r)) (c : LowerChart d k r) :
    deriv (deriv c.upper) (m ((d,k),r))/ell ((d,k),r) ≤
      1/m ((d,k),r)-ell ((d,k),r)/n ((d,k),r)+d*ell ((d,k),r)-2*ν := by
  have he : ∀ y ∈ Icc (-m ((d,k),r)) (n ((d,k),r)),
      HasDerivAt (fun s => c.solution (m ((d,k),r),s))
        (d*c.solution (m ((d,k),r),y)+(k/2)*(c.solution (m ((d,k),r),y))^2-y) y :=
    fun y hy => (c.equation y hy).self_of_nhds
  have hz : c.solution (m ((d,k),r),-m ((d,k),r))=0 := c.lower_zero.self_of_nhds
  have hf := (c.formulas hr).2
  have hv := Riccati.endpoint_variation_bound (c.solution_continuous _)
    (show 0 < k/2 by linarith) (m_pos hr) (n_pos hr) hd hν hνsq hz he
    (show deriv (deriv c.upper) (m ((d,k),r))/ell ((d,k),r) =
      1/m ((d,k),r)-ell ((d,k),r)/n ((d,k),r)+d*(1+ell ((d,k),r))+
      2*(k/2)*m ((d,k),r)*(∫ y in (-m ((d,k),r))..(n ((d,k),r)),
        1/(Riccati.multiplier (fun s => c.solution (m ((d,k),r),s)) (k/2) d
          (-m ((d,k),r)) y)^2) by convert hf using 1; ring)
  exact hv

end QuinticLienard.ModelEndpoint

end OAI
