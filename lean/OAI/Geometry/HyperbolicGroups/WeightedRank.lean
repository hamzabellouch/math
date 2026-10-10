import Mathlib
import OAI.Geometry.HyperbolicGroups.RestrictOccurrence

namespace OAI

section
section


noncomputable section
open scoped BigOperators
namespace HyperbolicObstruction
namespace IncidenceTemplate.Occurrences.Shape.Weights

variable {s u q v : ℕ} {T : Shape s u q} (W : T.Weights (v := v))
local instance : DecidableEq (T.Pos v) := Classical.typeDecidableEq _

lemma positions_le {K : ℕ} (ht : ∀ a, W.top a ≤ K) (hf : ∀ b, W.fan b ≤ K)
    (hq : ∀ e, W.square e ≤ K) (hd : ∀ e, W.six e ≤ K) (p : T.Pos v) : W.position p ≤ K := by
  rcases p with a | (⟨b,f⟩ | (⟨e,f⟩ | ⟨e,i⟩))
  · exact ht a
  · exact hf b
  · exact hq e
  · exact hd e

lemma layer_card {I : Type*} [Fintype I] (r : I → ℕ) (K : ℕ) (h : ∀ i, r i ≤ K) :
    (∑ j ∈ Finset.range K, (Fintype.card {i : I // j < r i} : ℝ)) = ∑ i, (r i : ℝ) := by
  classical
  have hh := Coincidence.layer_cake Finset.univ r K (fun i _ => h i)
  exact_mod_cast (by simpa only [Fintype.card_subtype] using hh :
    (∑ j ∈ Finset.range K, Fintype.card {i : I // j < r i}) = ∑ i, r i)

/-- Source weighted-coincidence for literal field positions and the SAME good
arrays that were selected with all conditional tests. -/
theorem weighted_rank_bound {M n K : ℕ} {α β δ : ℝ} {w : Entry (SymmetricAlphabet n) → Bool}
    (h : GoodUpTo M α β δ w) (hs : s ≤ M) (hu : u ≤ M) (hq : q ≤ M) (hv : v ≤ M)
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
    (fun j _ => W.rank_level_bound h hs hu hq hv σ hi hp j)
  simp only [Finset.sum_add_distrib,← Finset.mul_sum] at hh
  simpa only [TopAt,FanAt,SquareAt,SixAt,layer_card W.top K htK,layer_card W.fan K hfK,
    layer_card W.square K hqK,layer_card W.six K hdK] using hh

/-- Literal internal-letter-contact estimate. The hypotheses on contacts are
exactly the indexed-side normality and side multiplicity conditions supplied
by source normal form; arbitrary cycles of contacts are allowed. -/
theorem contact_bound {M n K : ℕ} {α β δ : ℝ} {w : Entry (SymmetricAlphabet n) → Bool}
    (h : GoodUpTo M α β δ w) (hs : s ≤ M) (hu : u ≤ M) (hq : q ≤ M) (hv : v ≤ M)
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
  exact (Nat.cast_le.mpr hh).trans (W.weighted_rank_bound h hs hu hq hv σ hi hp htK hfK hqK hdK)

end IncidenceTemplate.Occurrences.Shape.Weights
end HyperbolicObstruction
end
end

section

end
end

end OAI
