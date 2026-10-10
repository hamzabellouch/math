import Mathlib
import OAI.Geometry.HyperbolicGroups.SeparatorDecomposition

namespace OAI

section
section


noncomputable section
universe vertexUniverse
namespace HyperbolicObstruction.PlanarRecursion

lemma exists_separator_cutoff (c d eta : ℝ) (hc : 0 ≤ c) (hd : 0 ≤ d) (heta : 0 < eta) :
    ∃ K : ℕ, 0 < K ∧ 144*c^2 ≤ (K : ℝ) ∧ d*(16*c/Real.sqrt K) ≤ eta := by
  let r := 16*c*d/eta
  obtain ⟨K,hK⟩ := exists_nat_gt (max (144*c^2) (max 1 (r^2)))
  have hcap : 144*c^2 ≤ (K : ℝ) := le_trans (le_max_left _ _) hK.le
  have hpos : (1 : ℝ) < K := lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_right _ _)) hK
  have hk : 0 < K := by exact_mod_cast (lt_trans (by norm_num : (0 : ℝ) < 1) hpos)
  have hsq : r^2 ≤ (K : ℝ) := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hK.le
  have hroot : r ≤ Real.sqrt K := by
    exact (Real.le_sqrt (by dsimp [r]; positivity) (by positivity)).mpr hsq
  have hh := mul_le_mul_of_nonneg_right hroot heta.le
  have hid : r*eta = 16*c*d := by dsimp only [r]; field_simp
  rw [hid] at hh
  refine ⟨K,hk,hcap,?_⟩
  calc
    d*(16*c/Real.sqrt K) = (16*c*d)/Real.sqrt K := by ring
    _ ≤ eta := (div_le_iff₀ (Real.sqrt_pos.2 (by exact_mod_cast hk))).mpr (by nlinarith)

/-- Uniform recursive partition theorem from balanced separators. The cutoff is
chosen before the finite vertex type, graph, and all recursive subproblems. -/
theorem uniform_bounded_partition (c d eta : ℝ) (hc : 0 ≤ c) (hd : 0 ≤ d) (heta : 0 < eta) :
    ∃ K : ℕ, 0 < K ∧ ∀ (V : Type vertexUniverse) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      HasBalancedSeparators G c → ∀ U : Finset V,
      ∃ P : CutPartition G U K, d*(P.removed.card : ℝ) ≤ eta*U.card := by
  obtain ⟨K,hK,hcap,hcoef⟩ := exists_separator_cutoff c d eta hc hd heta
  refine ⟨K,hK,?_⟩
  intro V _ _ G hsep U
  obtain ⟨P,hP⟩ := partition_of_balanced_separators hc hsep K hK hcap U
  refine ⟨P,?_⟩
  calc
    d*(P.removed.card : ℝ) ≤ d*(16*c*U.card/Real.sqrt K) := mul_le_mul_of_nonneg_left hP hd
    _ = (d*(16*c/Real.sqrt K))*U.card := by ring
    _ ≤ eta*U.card := mul_le_mul_of_nonneg_right hcoef (by positivity)

end HyperbolicObstruction.PlanarRecursion
end
end

section

end
end

end OAI
