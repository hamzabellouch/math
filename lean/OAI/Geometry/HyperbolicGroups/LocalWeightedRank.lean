import Mathlib
import OAI.Geometry.HyperbolicGroups.WeightedRank

namespace OAI

section
section


noncomputable section
open scoped BigOperators
namespace HyperbolicObstruction.IncidenceTemplate.Occurrences.Shape.Weights
attribute [local instance] Classical.propDecidable
variable {s u q v : ℕ} {T : Shape s u q} (W : T.Weights (v := v))
local instance : DecidableEq (T.Pos v) := Classical.typeDecidableEq _

/-- Only the occurrence collections retained at each positive weight level
need be small; the complete alphabet's array is not bounded by the fragment.
This is the literal layer application of source diagram:weighted-rank. -/
theorem rank_level_bound_local {M n : ℕ} {α β δ : ℝ} {w : Entry (SymmetricAlphabet n) → Bool}
    (h : GoodUpTo M α β δ w) (j : ℕ)
    (hs : Fintype.card (W.TopAt j) ≤ M) (hu : Fintype.card (W.FanAt j) ≤ M)
    (hq : Fintype.card (W.SquareAt j) ≤ M) (hv : Fintype.card (W.SixAt j) ≤ M)
    (σ : T.Pos v → SymmetricAlphabet n) (hi : Function.Injective (T.row σ))
    (hp : BernoulliCandidates.Present T.row w σ) :
    (Coincidence.rankOn (fun p => (σ p).1) (Finset.univ.filter (fun p => j < W.position p)) : ℝ) ≤
      ((3-β)-7*(2-α)) * Fintype.card (W.TopAt j) + (2-α) * Fintype.card (W.FanAt j) +
        (2-δ) * Fintype.card (W.SquareAt j) + (3-δ) * Fintype.card (W.SixAt j) := by
  rw [← W.rank_embed j σ]
  apply h.rank_bound (v := Fintype.card (W.SixAt j)) (W.atLevel j) hs hu hq hv
  · intro a b hab
    simp only [W.row_embed] at hab
    exact W.embedTrial_injective j (hi hab)
  · intro r
    rw [W.row_embed]
    exact hp _

theorem weighted_rank_bound_local {M n K : ℕ} {α β δ : ℝ} {w : Entry (SymmetricAlphabet n) → Bool}
    (h : GoodUpTo M α β δ w)
    (hs : ∀ j, Fintype.card (W.TopAt j) ≤ M) (hu : ∀ j, Fintype.card (W.FanAt j) ≤ M)
    (hq : ∀ j, Fintype.card (W.SquareAt j) ≤ M) (hv : ∀ j, Fintype.card (W.SixAt j) ≤ M)
    (σ : T.Pos v → SymmetricAlphabet n) (hi : Function.Injective (T.row σ))
    (hp : BernoulliCandidates.Present T.row w σ)
    (htK : ∀ a, W.top a ≤ K) (hfK : ∀ b, W.fan b ≤ K)
    (hqK : ∀ e, W.square e ≤ K) (hdK : ∀ e, W.six e ≤ K) :
    ((∑ j ∈ Finset.range K, Coincidence.rankOn (fun p => (σ p).1)
      (Finset.univ.filter (fun p => j < W.position p)) : ℕ) : ℝ) ≤
      ((3-β)-7*(2-α)) * (∑ a, (W.top a : ℝ)) + (2-α) * (∑ b, (W.fan b : ℝ)) +
        (2-δ) * (∑ e, (W.square e : ℝ)) + (3-δ) * (∑ e, (W.six e : ℝ)) := by
  push_cast
  have hh := Finset.sum_le_sum (s := Finset.range K)
    (fun j _ => W.rank_level_bound_local h j (hs j) (hu j) (hq j) (hv j) σ hi hp)
  simp only [Finset.sum_add_distrib,← Finset.mul_sum] at hh
  simpa only [TopAt,FanAt,SquareAt,SixAt,layer_card W.top K htK,layer_card W.fan K hfK,
    layer_card W.square K hqK,layer_card W.six K hdK] using hh

theorem contact_bound_local {M n K : ℕ} {α β δ : ℝ} {w : Entry (SymmetricAlphabet n) → Bool}
    (h : GoodUpTo M α β δ w)
    (hs : ∀ j, Fintype.card (W.TopAt j) ≤ M) (hu : ∀ j, Fintype.card (W.FanAt j) ≤ M)
    (hq : ∀ j, Fintype.card (W.SquareAt j) ≤ M) (hv : ∀ j, Fintype.card (W.SixAt j) ≤ M)
    (σ : T.Pos v → SymmetricAlphabet n) (hi : Function.Injective (T.row σ))
    (hp : BernoulliCandidates.Present T.row w σ)
    (htK : ∀ a, W.top a ≤ K) (hfK : ∀ b, W.fan b ≤ K)
    (hqK : ∀ e, W.square e ≤ K) (hdK : ∀ e, W.six e ≤ K)
    {E : Type*} [Fintype E] [DecidableEq E] (l r : E → T.Pos v)
    (hne : ∀ e, l e ≠ r e) (hc : ∀ e, (σ (l e)).1 = (σ (r e)).1)
    (hcap : ∀ p, (Finset.univ.filter (fun e => l e = p ∨ r e = p)).card ≤ W.position p) :
    (Fintype.card E : ℝ) ≤ ((3-β)-7*(2-α)) * (∑ a, (W.top a : ℝ)) +
      (2-α) * (∑ b, (W.fan b : ℝ)) + (2-δ) * (∑ e, (W.square e : ℝ)) +
      (3-δ) * (∑ e, (W.six e : ℝ)) := by
  have hh := Coincidence.contacts_le_weighted_rank (fun p => (σ p).1) W.position l r hne hc hcap K
    (W.positions_le htK hfK hqK hdK)
  exact (Nat.cast_le.mpr hh).trans (W.weighted_rank_bound_local h hs hu hq hv σ hi hp htK hfK hqK hdK)
end HyperbolicObstruction.IncidenceTemplate.Occurrences.Shape.Weights
end
end

section

end
end

end OAI
