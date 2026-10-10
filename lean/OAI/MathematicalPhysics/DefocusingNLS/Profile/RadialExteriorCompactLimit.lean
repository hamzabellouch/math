import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialExteriorCompactExistence
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialFreeParameterContinuity

namespace OAI

/-! The canonical exterior boundary jet converges uniformly on compact shooting sets. -/

open Set Filter
namespace DefocusingNLS

theorem radialExterior_compact_boundary_limit {K : Type*} [MetricSpace K] [CompactSpace K]
    (q m : K → ℂ) (hqcont : Continuous q) (hmcont : Continuous m) (l : ℝ)
    (hq : ∀ x, -1 < (q x).re)
    (hannulus : ∀ x, ∃ δ ρ : ℝ, 0 < δ ∧ δ < ‖m x‖ ∧ ‖m x‖+2*δ < 1 ∧ ρ < 1 ∧
      (∀ t, l ≤ t → ‖(radialFreeSlowJet (q x) (m x) t).1‖+2*δ ≤ ρ) ∧
      ∀ t, l ≤ t → δ < ‖(radialFreeSlowJet (q x) (m x) t).1‖) :
    TendstoUniformly
      (fun (n : ℕ) x => radialExteriorCanonical (-2*q x-1/(n : ℂ)) n (m x) l l)
      (fun x => radialFreeSlowJet (q x) (m x) l) atTop := by
  classical
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  by_contra h
  obtain ⟨s,hs,x,x₀,hx,hbad⟩ := radial_compact_bad_subsequence
    (fun n x => dist (radialFreeSlowJet (q x) (m x) l)
      (radialExteriorCanonical (-2*q x-1/(n : ℂ)) n (m x) l l) < ε) h
  have hqlim := hqcont.continuousAt.tendsto.comp hx
  have hmlim := hmcont.continuousAt.tendsto.comp hx
  have hν : Tendsto (fun i => -2*q (x i)-1/(s i : ℂ)) atTop (nhds (-2*q x₀)) := by
    simpa only [Function.comp_def,sub_zero] using!
      (hqlim.const_mul (-2)).sub
        ((tendsto_one_div_atTop_nhds_zero_nat :
          Tendsto (fun n : ℕ => 1/(n : ℂ)) atTop (nhds 0)).comp hs.tendsto_atTop)
  obtain ⟨δ,ρ,hδ,hδm,hsmall,hρ,hupper,hlower⟩ := hannulus x₀
  have hconv := (radialExteriorCanonical_H_limit_subsequence s hs
    (fun i => -2*q (x i)-1/(s i : ℂ)) (fun i => m (x i))
    (q x₀) (m x₀) (hq x₀) hν hmlim δ ρ l hδ hδm hsmall hρ hupper hlower).2
  have hc := hconv.tendsto_at (Set.mem_Ici.mpr le_rfl)
  have hf := (continuousAt_radialFreeSlowJet_parameter (q x₀) (m x₀) (hq x₀) l).tendsto.comp
    (hqlim.prodMk_nhds hmlim)
  have hdist : Tendsto (fun i => dist
      (radialExteriorCanonical (-2*q (x i)-1/(s i : ℂ)) (s i) (m (x i)) l l)
      (radialFreeSlowJet (q (x i)) (m (x i)) l)) atTop (nhds 0) := by
    simpa only [dist_self] using! hc.dist hf
  obtain ⟨i,hi⟩ := (hdist.eventually (gt_mem_nhds hε)).exists
  exact hbad i (by simpa only [dist_comm] using hi)

end DefocusingNLS

end OAI
