import Mathlib
import OAI.Geometry.HyperbolicGroups.Shape

namespace OAI

section
section


noncomputable section
open scoped BigOperators
open Filter Topology
namespace HyperbolicObstruction
namespace IncidenceTemplate.Occurrences

instance shapeFintype (s u q : ℕ) : Fintype (Shape s u q) := by
  classical
  unfold Shape
  letI (t : Fin u → Fin 7) : Fintype ((Fin s → (i : Fin 7) → {b : Fin u // t b = i}) ×
      (Fin q → TwoPath)) := inferInstance
  infer_instance

/-- Each count is bounded separately. Thus every collection of at most M
occurrences is included, with all its retained fan slots. This harmless stronger
finite family needs no union over diagram copies or equality guesses. -/
abbrev BoundedShape (M : ℕ) := Σ s : Fin (M+1), Σ u : Fin (M+1),
  Σ q : Fin (M+1), Σ _ : Fin (M+1), Shape s u q

instance (M : ℕ) : Fintype (BoundedShape M) := by
  classical
  unfold BoundedShape
  infer_instance

namespace BoundedShape
variable {M : ℕ} (b : BoundedShape M)
abbrev tops := b.1.val
abbrev fans := b.2.1.val
abbrev squares := b.2.2.1.val
abbrev sixes := b.2.2.2.1.val
abbrev shape : Shape b.tops b.fans b.squares := b.2.2.2.2

def Good {n : ℕ} (α β δ : ℝ) (w : Entry (SymmetricAlphabet n) → Bool) :=
  b.shape.Good (v := b.sixes) α β δ w
instance {n : ℕ} (α β δ : ℝ) : DecidablePred (b.Good (n := n) α β δ) :=
  fun _ => Classical.propDecidable _

def rate (α β δ N : ℝ) : ℝ :=
  Coincidence.rankRate (Fintype.card (b.shape.Pos b.sixes))
    (∑ r : Shape.Trial b.tops b.fans b.squares b.sixes, b.shape.cost α β δ r) N

lemma rate_nonneg (α β δ : ℝ) {N : ℝ} (hN : 0 ≤ N) : 0 ≤ b.rate α β δ N :=
  Coincidence.rankRate_nonneg _ _ hN

lemma rate_tendsto (α β δ : ℝ) : Tendsto (b.rate α β δ) atTop (𝓝 0) :=
  Coincidence.rankRate_tendsto _ _

lemma bad_bound {n : ℕ} {α β δ : ℝ} (ha : 0 ≤ α) (hb : 7*α ≤ β) (hd : 0 ≤ δ) :
    (FiniteLaw.bernoulliProduct (probability α β δ (SymmetricAlphabet n))
      (probability_mem ha hb hd)).prob (fun w => ¬b.Good α β δ w) ≤
      b.rate α β δ (Fintype.card (SymmetricAlphabet n)) :=
  b.shape.bad_bound ha hb hd
end BoundedShape

/-- The exact source diagram:rank conclusion at any fixed finite size. -/
def GoodUpTo (M : ℕ) {n : ℕ} (α β δ : ℝ) (w : Entry (SymmetricAlphabet n) → Bool) :=
  ∀ b : BoundedShape M, b.Good α β δ w
instance (M : ℕ) {n : ℕ} (α β δ : ℝ) : DecidablePred (GoodUpTo M (n := n) α β δ) :=
  fun _ => Classical.propDecidable _

def rankRate (M : ℕ) (α β δ N : ℝ) : ℝ := ∑ b : BoundedShape M, b.rate α β δ N

lemma rankRate_nonneg (M : ℕ) (α β δ : ℝ) {N : ℝ} (hN : 0 ≤ N) :
    0 ≤ rankRate M α β δ N := Finset.sum_nonneg fun b _ => b.rate_nonneg α β δ hN

lemma rankRate_tendsto (M : ℕ) (α β δ : ℝ) : Tendsto (rankRate M α β δ) atTop (𝓝 0) := by
  unfold rankRate
  simpa only [rankRate,Finset.sum_const_zero] using
    tendsto_finsetSum (Finset.univ : Finset (BoundedShape M)) (fun b _ => b.rate_tendsto α β δ)

/-- The bounded-rank bad-event probability tends to zero, with literal costs
and original full probability space. -/
theorem rank_bad_bound (M : ℕ) {n : ℕ} {α β δ : ℝ}
    (ha : 0 ≤ α) (hb : 7*α ≤ β) (hd : 0 ≤ δ) :
    (FiniteLaw.bernoulliProduct (probability α β δ (SymmetricAlphabet n))
      (probability_mem ha hb hd)).prob (fun w => ¬GoodUpTo M α β δ w) ≤
      rankRate M α β δ (Fintype.card (SymmetricAlphabet n)) := by
  classical
  simp only [GoodUpTo,not_forall]
  exact (FiniteLaw.prob_exists_le _ _).trans (Finset.sum_le_sum fun b _ => b.bad_bound ha hb hd)

lemma GoodUpTo.rank_bound {M n s u q v : ℕ} {α β δ : ℝ}
    {w : Entry (SymmetricAlphabet n) → Bool} (h : GoodUpTo M α β δ w)
    (T : Shape s u q) (hs : s ≤ M) (hu : u ≤ M) (hq : q ≤ M) (hv : v ≤ M) :
    T.Good (v := v) α β δ w :=
  h ⟨⟨s,Nat.lt_succ_of_le hs⟩,⟨u,Nat.lt_succ_of_le hu⟩,
    ⟨q,Nat.lt_succ_of_le hq⟩,⟨v,Nat.lt_succ_of_le hv⟩,T⟩

lemma GoodUpTo.mono {M L n : ℕ} {α β δ : ℝ} {w : Entry (SymmetricAlphabet n) → Bool}
    (h : GoodUpTo M α β δ w) (hLM : L ≤ M) : GoodUpTo L α β δ w := by
  intro b
  exact h.rank_bound b.shape ((Nat.le_of_lt_succ b.1.isLt).trans hLM)
    ((Nat.le_of_lt_succ b.2.1.isLt).trans hLM)
    ((Nat.le_of_lt_succ b.2.2.1.isLt).trans hLM)
    ((Nat.le_of_lt_succ b.2.2.2.1.isLt).trans hLM)

end IncidenceTemplate.Occurrences
end HyperbolicObstruction
end
end

section

end
end

end OAI
