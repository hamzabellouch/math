import Mathlib
import OAI.Probability.CriticalPercolation.Criticality.BandScale
import OAI.Probability.CriticalPercolation.Criticality.PositiveCritical
import OAI.Probability.CriticalPercolation.Criticality.SubexponentialVolumes
import OAI.Probability.CriticalPercolation.GraphGeometry.InfiniteEventSubsetHit
import OAI.Probability.CriticalPercolation.Growth.SuperpolynomialContradiction
import OAI.Probability.CriticalPercolation.Growth.SuperpolynomialRadius
import OAI.Probability.CriticalPercolation.Model

namespace OAI

section
section
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Classical Topology

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

theorem no_percolation_at_criticality_superpolynomial
    (hconnected : G.fullGraph.Connected) (hlocal : G.LocallyFinite)
    (hquasi : G.QuasiTransitive) (hpc : G.criticalProbability<1)
    (hsub : G.SubexponentialGrowth) (hsuper : G.SuperpolynomialGrowth) :
    G.law G.criticalProbability G.percolates = 0 := by
  let := G.countable_vertices hconnected hlocal
  let := G.countable_bonds hconnected hlocal
  let := hconnected.nonempty
  by_contra hbad
  obtain ⟨θ,hθ,hroot⟩ := G.uniform_rooted_probability hconnected hlocal hquasi
    G.criticalProbability (pos_iff_ne_zero.mpr hbad)
  have hθ1 : θ≤1 := (hroot (Classical.arbitrary V)).trans measureReal_le_one
  have hpcpos := G.criticalProbability_pos hconnected hlocal hquasi
  let ε : ℝ := min ((G.criticalProbability:ℝ)/2) (1-(G.criticalProbability:ℝ))
  have hε : 0<ε := lt_min (by positivity) (by exact sub_pos.mpr hpc)
  have hforbid := G.eventually_no_superpolynomial_band hconnected hlocal hquasi hsub hsuper θ hθ hθ1 ε hε
  obtain ⟨N,hN⟩ := eventually_atTop.mp hforbid
  have hl : Tendsto (fun n : ℕ => Real.log (n:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlarge : ∀ᶠ L : ℕ in atTop, 4/(3*(Real.log L)^2)<θ/4 := by
    have hh := (tendsto_const_nhds (x := (4:ℝ))).div_atTop
      (((tendsto_pow_atTop (α := ℝ) (n := 2) (by norm_num)).comp hl).const_mul_atTop (by norm_num : (0:ℝ)<3))
    exact hh.eventually (gt_mem_nhds (by positivity : (0:ℝ)<θ/4))
  obtain ⟨L,hLN,hL,hlarge⟩ := ((eventually_ge_atTop N).and ((eventually_ge_atTop 2).and hlarge)).exists
  obtain ⟨p,hphalf,hppc,z,s,hs,hband,htail⟩ := G.exists_subcritical_clusterBand
    hconnected hlocal hquasi hpcpos θ hθ hroot L hL hlarge
  apply hN s (hLN.trans hs) p z
  · exact (min_le_left _ _).trans hphalf
  · exact (min_le_right _ _).trans (by exact sub_le_sub_left (show (p:ℝ)≤G.criticalProbability from hppc.le) 1)
  · exact hband
  · exact htail

end CriticalPercolation.BondGraph
end
end
end

end OAI
