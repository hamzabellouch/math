import OAI.Geometry.CylinderCovering.Beams.NeighborhoodCoversDefinitions
import OAI.Geometry.CylinderCovering.Beams.NeighborhoodIntrinsic
import OAI.Geometry.CylinderCovering.Beams.Core

namespace OAI

noncomputable section
open Set Filter
open scoped Topology
namespace ShortenedBeam
open CylinderCovering

theorem neighborhoodMixedStatement : NeighborhoodMixedStatement := by
  intro a ha ha1 ε hε
  obtain ⟨E,hE,Cm,Cp,h⟩ := neighborhoodAlternativeStatement a ha ha1
  have hs : 0 < Real.sqrt (2:ℝ)/4 := by positivity
  have hlimit : Tendsto (fun N : ℕ => (Real.sqrt 2/4)*E/(N:ℝ)) atTop (𝓝 0) := by
    have hi : Tendsto (fun N : ℕ => (N:ℝ)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
    simpa only [div_eq_mul_inv, mul_zero] using
      (tendsto_const_nhds.mul hi : Tendsto
        (fun N : ℕ => ((Real.sqrt 2/4)*E)*(N:ℝ)⁻¹) atTop
        (𝓝 (((Real.sqrt 2/4)*E)*0)))
  have hevent : ∀ᶠ N : ℕ in atTop, (Real.sqrt 2/4)*E/(N:ℝ) < ε/2 :=
    hlimit.eventually (gt_mem_nhds (by linarith : (0:ℝ) < ε/2))
  obtain ⟨N, hN, hsmall⟩ := (eventually_gt_atTop (0:ℕ)).and hevent |>.exists
  obtain ⟨hb,hcm,hcp,hcost⟩ := h N hN
  obtain ⟨n,D,hD,hstrip,hDcost⟩ := finiteStripStatement a (ε/2) (by linarith)
  refine ⟨N,hN,Cm N,Cp N,n,D,⟨hb,hcm,hcp⟩,hD,hstrip,?_,?_⟩
  · exact (tetrahedron_covered ha.le ha1.le).trans
      (union_subset_union (union_subset_union hcm hcp) hstrip)
  · have hbeam := (div_le_iff₀ hs).mp hcost
    have heq : (BeamCost.beamCost a+E/(N:ℝ))*(Real.sqrt 2/4) =
        (Real.sqrt 2/4)*BeamCost.beamCost a+(Real.sqrt 2/4)*E/(N:ℝ) := by ring
    rw [heq] at hbeam
    linarith

theorem neighborhoodStrictStatement : NeighborhoodStrictStatement := by
  obtain ⟨a,ha,ha1,hgain⟩ := BeamCost.exists_strict_gain
  let A := (Real.sqrt 2/4)*(BeamCost.beamCost a+BeamCost.stripCost a)
  have hA : A < Real.sqrt 2 := by
    dsimp [A]
    have hs : 0 < Real.sqrt (2:ℝ)/4 := by positivity
    nlinarith [mul_lt_mul_of_pos_left hgain hs]
  let ε := (Real.sqrt 2-A)/2
  have hε : 0 < ε := by dsimp [ε]; linarith
  obtain ⟨N,hN,Cm,Cp,n,D,hfamilies,hD,hstrip,hcover,hcost⟩ :=
    neighborhoodMixedStatement a ha ha1 ε hε
  refine ⟨a,ha,ha1,N,hN,Cm,Cp,n,D,hfamilies,hD,hstrip,hcover,?_⟩
  rw [tetrahedron_minimum_shadow]
  dsimp [A,ε] at *
  linarith

end ShortenedBeam

end

end OAI
