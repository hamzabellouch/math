import OAI.NumberTheory.JointDickman.Arithmetic.BinGeneratingDickman

namespace OAI

/-! # Unconditional finite-bin distribution with its Dickman marginal -/
namespace JointDickman
open Finset

 theorem finiteBinDistributionInput : PublishedInputs.FiniteBinDistributionInput := by
  intro J hJ
  obtain ⟨ν,hν0,hν1,hνlim⟩ := finiteBinStateDistribution J hJ
  refine ⟨ν,hν0,hν1,hνlim,?_⟩
  intro k hk hkJ
  rw [highBinMarginal_eq_generating hJ ν (hνlim 1 zero_lt_one) k,
    highBinGenerating_eq_dickman hJ hk hkJ]
  have hc : 0 < (k : ℝ)/J := div_pos (by exact_mod_cast hk)
    (by exact_mod_cast (show 0 < J by omega))
  simp only [dickmanCDF, not_le.mpr hc, ite_false]

end JointDickman

end OAI
