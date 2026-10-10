import OAI.Analysis.PlanarEndpoint.Information.ChainRule
import OAI.Analysis.PlanarEndpoint.Information.Entropy
import OAI.Analysis.PlanarEndpoint.Information.FiniteTables
import OAI.Analysis.PlanarEndpoint.Information.Sampling

namespace OAI

/-! Finite information laws, entropy and convergence of probability measures. -/


noncomputable section
open MeasureTheory Filter Set
open scoped Topology BigOperators ENNReal Classical
namespace PlanarEndpoint.TransverseInformation

variable {S V V' Y Y' W : Type*} [Fintype S] [Fintype V] [Fintype V']
  [Fintype Y] [Fintype Y'] [Fintype W]

omit [Fintype V] [Fintype V'] in
lemma sampledInformation_congr_fibers (L : ℝ) (a : S → ℝ)
    (v : S → V) (v' : S → V') (y : S → Y) (y' : S → Y')
    (hv : ∀ r s, v r = v s ↔ v' r = v' s)
    (hy : ∀ r s, y r = y s ↔ y' r = y' s) (s : S) :
    sampledInformation L a v y s = sampledInformation L a v' y' s := by
  unfold sampledInformation conditionalMass
  rw [sampledTable_row, sampledTable_row]
  have hnum : sampledTable a v y (v s) (y s) = sampledTable a v' y' (v' s) (y' s) := by
    unfold sampledTable
    apply Finset.sum_congr rfl
    intro r _
    rw [hv r s, hy r s]
  have hden : (∑ r, if v r = v s then a r else 0) =
      ∑ r, if v' r = v' s then a r else 0 := by
    apply Finset.sum_congr rfl
    intro r _
    rw [hv r s]
  rw [hnum, hden]

omit [Fintype V] [Fintype V'] in
lemma sampledEntropy_congr_fibers (L : ℝ) (a : S → ℝ)
    (v : S → V) (v' : S → V') (y : S → Y) (y' : S → Y')
    (hv : ∀ r s, v r = v s ↔ v' r = v' s)
    (hy : ∀ r s, y r = y s ↔ y' r = y' s) :
    sampledEntropy L a v y = sampledEntropy L a v' y' := by
  apply Finset.sum_congr rfl
  intro s _
  rw [sampledInformation_congr_fibers L a v v' y y' hv hy s]

omit [Fintype V] in
lemma sampledEntropy_mutual_information (a : S → ℝ) (ha : ∀ s, 0 ≤ a s)
    (v : S → V) (u : S → W) (y : S → Y) (L : ℝ) :
    sampledEntropy L a v y - sampledEntropy L a (fun s => (v s,u s)) y =
      sampledEntropy L a v u - sampledEntropy L a (fun s => (v s,y s)) u := by
  have h1 := sampledEntropy_chain a ha v u y L
  have h2 := sampledEntropy_chain a ha v y u L
  have hswap : sampledEntropy L a v (fun s => (u s,y s)) =
      sampledEntropy L a v (fun s => (y s,u s)) := by
    apply sampledEntropy_congr_fibers
    · intro r s
      rfl
    · intro r s
      simp only [Prod.mk.injEq, and_comm]
  rw [hswap] at h1
  linarith

lemma sampledEntropy_le_log_card (a : S → ℝ) (ha : ∀ s, 0 ≤ a s)
    (ha1 : ∑ s, a s = 1) (v : S → V) (y : S → Y) {L : ℝ} (hL : 1 < L) :
    sampledEntropy L a v y ≤ Real.log (Fintype.card Y) / Real.log L := by
  rw [sampledEntropy_eq]
  apply (entropy_conditioning_le (sampledTable a v y) (sampledTable_nonneg a ha v y)
    (by rw [sampledTable_total, ha1]) hL).trans
  apply entropy_le_log_card
  · exact colMass_nonneg _ (sampledTable_nonneg a ha v y)
  · change (∑ z, ∑ b, sampledTable a v y b z) = 1
    rw [Finset.sum_comm, sampledTable_total, ha1]
  · exact hL

end PlanarEndpoint.TransverseInformation
end

end OAI
