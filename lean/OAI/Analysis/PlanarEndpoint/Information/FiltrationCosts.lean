import OAI.Analysis.PlanarEndpoint.Information.Entropy
import OAI.Analysis.PlanarEndpoint.Information.EntropyLaws

namespace OAI

/-! Finite information laws, entropy and convergence of probability measures. -/


noncomputable section
open MeasureTheory Filter Set
open scoped Topology BigOperators ENNReal Classical
namespace PlanarEndpoint.TransverseInformation

variable {S C D : Type*} [Fintype S] [Fintype C] [Fintype D]
  {X : ℕ → Type*} [∀ j, Fintype (X j)]

def directionFiltrationCost (L : ℝ) (a : S → ℝ) (c : S → C) (d : S → D)
    (x : (j : ℕ) → S → X j) (j : ℕ) : ℝ :=
  sampledEntropy L a (fun s => (c s,x j s)) (x (j+1)) -
    sampledEntropy L a (fun s => ((c s,x j s),d s)) (x (j+1))

lemma directionFiltrationCost_nonneg (a : S → ℝ) (ha : ∀ s, 0 ≤ a s)
    (c : S → C) (d : S → D) (x : (j : ℕ) → S → X j)
    {L : ℝ} (hL : 1 < L) (j : ℕ) : 0 ≤ directionFiltrationCost L a c d x j :=
  sub_nonneg.mpr (sampledEntropy_conditioning_le a ha _ d _ hL)

omit [Fintype C] in
lemma directionFiltrationCost_eq (a : S → ℝ) (ha : ∀ s, 0 ≤ a s)
    (c : S → C) (d : S → D) (x : (j : ℕ) → S → X j)
    (parent : (j : ℕ) → X (j+1) → X j)
    (hnest : ∀ j s, x j s = parent j (x (j+1) s)) (L : ℝ) (j : ℕ) :
    directionFiltrationCost L a c d x j =
      sampledEntropy L a (fun s => (c s,x j s)) d -
        sampledEntropy L a (fun s => (c s,x (j+1) s)) d := by
  unfold directionFiltrationCost
  rw [sampledEntropy_mutual_information a ha _ d _ L]
  congr 1
  apply sampledEntropy_congr_fibers
  · intro r s
    simp only [Prod.mk.injEq]
    constructor
    · intro h
      exact ⟨h.1.1,h.2⟩
    · rintro ⟨hc,hx⟩
      exact ⟨⟨hc,by rw [hnest j r, hnest j s, hx]⟩,hx⟩
  · intro r s
    rfl

omit [Fintype C] in
lemma directionFiltrationCost_sum_eq (a : S → ℝ) (ha : ∀ s, 0 ≤ a s)
    (c : S → C) (d : S → D) (x : (j : ℕ) → S → X j)
    (parent : (j : ℕ) → X (j+1) → X j)
    (hnest : ∀ j s, x j s = parent j (x (j+1) s)) (L : ℝ) (n : ℕ) :
    (∑ j ∈ Finset.range n, directionFiltrationCost L a c d x j) =
      sampledEntropy L a (fun s => (c s,x 0 s)) d -
        sampledEntropy L a (fun s => (c s,x n s)) d := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, directionFiltrationCost_eq a ha c d x parent hnest]
    ring

theorem directionFiltrationCost_sum_le (a : S → ℝ) (ha : ∀ s, 0 ≤ a s)
    (ha1 : ∑ s, a s = 1) (c : S → C) (d : S → D) (x : (j : ℕ) → S → X j)
    (parent : (j : ℕ) → X (j+1) → X j)
    (hnest : ∀ j s, x j s = parent j (x (j+1) s)) {L : ℝ} (hL : 1 < L)
    (n : ℕ) (J : Finset ℕ) (hJ : J ⊆ Finset.range n) :
    0 ≤ ∑ j ∈ J, directionFiltrationCost L a c d x j ∧
    (∑ j ∈ J, directionFiltrationCost L a c d x j) ≤
      Real.log (Fintype.card D) / Real.log L := by
  constructor
  · exact Finset.sum_nonneg (fun j _ => directionFiltrationCost_nonneg a ha c d x hL j)
  · calc
      _ ≤ ∑ j ∈ Finset.range n, directionFiltrationCost L a c d x j :=
        Finset.sum_le_sum_of_subset_of_nonneg hJ
          (fun j _ _ => directionFiltrationCost_nonneg a ha c d x hL j)
      _ = _ := directionFiltrationCost_sum_eq a ha c d x parent hnest L n
      _ ≤ sampledEntropy L a (fun s => (c s,x 0 s)) d :=
        sub_le_self _ (sampledEntropy_nonneg a ha _ d hL)
      _ ≤ _ := sampledEntropy_le_log_card a ha ha1 _ d hL

end PlanarEndpoint.TransverseInformation
end

end OAI
