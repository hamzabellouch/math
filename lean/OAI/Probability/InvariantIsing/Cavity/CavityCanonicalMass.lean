import OAI.Probability.InvariantIsing.Cavity.CavityResidueConvergence
import OAI.Probability.InvariantIsing.Cavity.CavityAffineWindows

namespace OAI

/-! The all-dimension canonical rational labels have the prescribed
positive limiting proportions. -/

noncomputable section
open Filter
open scoped Topology BigOperators

namespace InvariantIsing

lemma cavity_canonical_mass_tendsto {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (s : Fin m → ℕ) (hsum : ∑ a, s a=n) :
    Tendsto (fun N a => ((cavitySpectralGroup (cavityResidueLabel hm s hsum N) a).card : ℝ)/N)
      atTop (𝓝 (fun a => (s a : ℝ)/n)) := by
  apply tendsto_pi_nhds.mpr
  intro a
  apply cavity_residue_tendsto hn 1
  intro t
  have hh := cavityAffineCount_ratio s (cavityResidueOffset hm t) hn (q := 1) zero_lt_one a
  apply hh.congr
  intro r
  rw [← cavityResidueSize hm n 1 (t : ℕ) r]
  rw [cavityResidueLabel_progression hm s hsum 1 (t : ℕ) r t.isLt,
    cavityAffineLabel_progression hm s (cavityResidueOffset hm t) hsum hn,
    cavityOrderedGroup_card]

end InvariantIsing

end

end OAI
