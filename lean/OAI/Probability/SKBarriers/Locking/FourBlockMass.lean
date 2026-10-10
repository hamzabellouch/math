import Mathlib
import OAI.Probability.SKBarriers.Hierarchy.WeightedAugment
import OAI.Probability.SKBarriers.Locking.FourBlockTent

namespace OAI

section

noncomputable section
open scoped BigOperators
open Set
namespace SK.Analytic

theorem fourBlockTent_underlying (κ : ℝ) (b l j k : List (ℝ × ℝ)) :
    weightedUnderlying (fourBlockTent κ b l j k)=(b++l)++(j++k) := by
  simp [fourBlockTent]

theorem fourBlockTent_mass (κ : ℝ) (b l j k : List (ℝ × ℝ))
    (hm : ∀ p∈(b++l)++(j++k),p.1∈Icc (0:ℝ) 1) :
    ∀ p∈fourBlockTent κ b l j k,p.1∈Icc (0:ℝ) 1 := by
  apply (weighted_mass_iff _ (P:=fun x => x∈Icc (0:ℝ) 1)).mpr
  rw [fourBlockTent_underlying]; exact hm

theorem fourBlockTent_sorted (κ : ℝ) (b l j k : List (ℝ × ℝ))
    (hs : ((b++l)++(j++k)).Pairwise (fun p q => p.1≤q.1)) :
    (fourBlockTent κ b l j k).Pairwise (fun p q => p.1≤q.1) := by
  apply (weighted_sorted_iff _).mpr
  rw [fourBlockTent_underlying]; exact hs

def narrowTentError (μ B R ω : ℝ) : ℝ := 6*R^2+2*μ*B*ω+(B*ω)^2+B^2*ω

theorem narrowTentError_mono {μ B R A ω : ℝ} (hμ : 0≤μ) (hB : 0≤B) (hA : 0≤A) (hAω : A≤ω) :
    narrowTentError μ B R A≤narrowTentError μ B R ω := by
  have HA := mul_le_mul_of_nonneg_left hAω hB
  have HS := sq_le_sq₀ (mul_nonneg hB hA) (mul_nonneg hB (hA.trans hAω))
  have H1 := mul_le_mul_of_nonneg_left hAω (show 0≤2*μ*B by positivity)
  have H2 := mul_le_mul_of_nonneg_left hAω (sq_nonneg B)
  dsimp [narrowTentError]
  nlinarith [(HS.mpr HA)]

end SK.Analytic

end
end

end OAI
