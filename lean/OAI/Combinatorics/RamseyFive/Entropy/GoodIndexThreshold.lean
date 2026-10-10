import Mathlib
import OAI.Combinatorics.RamseyFive.Entropy.CollisionSampling

namespace OAI

namespace SharpRamseyFive.FiniteEntropy
open scoped Classical
noncomputable section
lemma badIndexIndicator_mono {δ δ' g d e : ℝ} (hδ : δ≤δ') :
    badIndexIndicator δ g d e≤badIndexIndicator δ' g d e := by
  unfold badIndexIndicator
  split_ifs with h h' h'
  · exact le_rfl
  · exact False.elim (h' (h.imp (fun h=>lt_of_lt_of_le h hδ) id))
  · norm_num
  · exact le_rfl

variable {B A T β : Type} [Fintype B] [Fintype A] [Fintype T]
    [Fintype β]
local instance goodThresholdDE : DecidableEq ((B×A)⊕T) := Classical.decEq _

lemma indexBad_cap_mono {J J' d e : ℝ} (hJ : J≤J')
    (p : Law (((B×A)⊕T)→β)) (c : ((B×A)⊕T)→((B×A)⊕T)→ℝ)
    (s : B→A) (i : ((B×A)⊕T)) :
    indexBad J d e p c s i ≤ indexBad J' d e p c s i :=
  badIndexIndicator_mono (sub_le_sub_right hJ _)

lemma indexBad_of_larger_cap {J J' d e : ℝ} (hJ : J≤J')
    (p : Law (((B×A)⊕T)→β)) (c : ((B×A)⊕T)→((B×A)⊕T)→ℝ)
    (s : B→A) (i : ((B×A)⊕T)) (hi : indexBad J' d e p c s i=0) :
    indexBad J d e p c s i=0 := by
  apply le_antisymm
  · exact (indexBad_cap_mono hJ p c s i).trans hi.le
  · exact badIndexIndicator_nonneg _ _ _ _
end
end SharpRamseyFive.FiniteEntropy

end OAI
