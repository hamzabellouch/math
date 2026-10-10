import OAI.Analysis.CircleDomains.Rigidity.RealBeltramiL2Reduction
import OAI.Analysis.CircleDomains.Sobolev.PrincipalSmoothLimit
import OAI.Analysis.CircleDomains.Rigidity.PrincipalPhysicalWitness
import OAI.Analysis.CircleDomains.Sobolev.ExteriorCoefficientAreaProof
import OAI.Analysis.CircleDomains.Topology.PlanarSchoenfliesProof
import OAI.Analysis.CircleDomains.Topology.FiniteCircleGreenProof

namespace OAI

/-! The exact compactly supported real-coefficient principal Beltrami input,
constructed from the L2 conductivity contraction and smooth principal maps.
No generalized Beltrami existence theorem is assumed. -/
open MeasureTheory Set Filter
open scoped Topology NNReal
noncomputable section
namespace CircleDomainRigidity

lemma principalRealBeltrami : PrincipalRealBeltrami := by
  intro q hq hcompact k hk hb
  obtain ⟨K, hK, hKzero⟩ := hcompact
  obtain ⟨g, μ, hm, hbound, hzero, hreal, he⟩ :=
    exists_complex_real_beltrami_l2_reduction q hq hK hKzero k hk hb
  obtain ⟨R, hR⟩ := (hK.image complexPlaneCoordinates.continuous).isBounded.subset_ball 0
  have hs : ∀ z, R ≤ ‖z‖ → μ z=0 := by
    intro z hz
    apply hzero
    intro hmem
    have hh := hR hmem
    simp only [Metric.mem_ball, dist_zero_right] at hh
    linarith
  have hk0 : 0 ≤ (k : ℝ) := k.2
  have hk1 : (k : ℝ) < 1 := by exact_mod_cast hk
  obtain ⟨S⟩ := exists_principal_smooth_approximation μ hm.aestronglyMeasurable
    hk0 hk1 hbound hs g he
  let T := max (R+2) 1
  have hT : 0 < T := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  obtain ⟨H, hprincipal, hw⟩ := S.exists_principal_homeomorph_limit
    (exteriorCoefficientAreaTheorem planarSchoenflies unorientedFiniteCircleGreenFormula)
    hk0 hk1 hT (le_max_left _ _)
  exact ⟨H, principalPhysicalWitness H g hw, hprincipal,
    principalPhysicalWitness_equation H g hw q hreal⟩

end CircleDomainRigidity

end

end OAI
