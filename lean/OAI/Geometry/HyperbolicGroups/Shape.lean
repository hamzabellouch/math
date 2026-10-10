import Mathlib
import OAI.Geometry.HyperbolicGroups.Coincidence
import OAI.Geometry.HyperbolicGroups.Occurrence

namespace OAI

noncomputable section
open scoped BigOperators
open Filter Topology
namespace HyperbolicObstruction
namespace IncidenceTemplate
namespace Occurrences

namespace Shape
variable {s u q v : ℕ} (T : Shape s u q)

/-- Literal field positions in source diagram:rank. -/
abbrev Pos (v : ℕ) := Fin s ⊕ ((Σ b : Fin u, rowSupport (.inl (T.1 b))) ⊕
  ((Σ e : Fin q, squareSupport (T.2.2 e)) ⊕ (Fin v × Fin 6)))

abbrev Trial (s u q v : ℕ) := Fin s ⊕ (Fin u ⊕ (Fin q ⊕ Fin v))

def coreCoord (a : Fin s) (e : Edge) : T.Pos v :=
  if he : isLoose e then .inl a else
    .inr (.inl ⟨(T.2.1 a (pointOfRepresentative e.val.1)).val,
      ⟨.inl e, by
        simp only [rowSupport,Finset.mem_map,Function.Embedding.inl_apply,
          Sum.inl.injEq]
        refine ⟨e,?_,rfl⟩
        simp only [fan,Finset.mem_filter,Finset.mem_univ,true_and]
        exact ⟨(T.2.1 a (pointOfRepresentative e.val.1)).property.symm,he⟩⟩⟩)

def topCoord (a : Fin s) (f : rowSupport (.inr (.inl ()))) : T.Pos v :=
  match f with
  | ⟨.inl e,_⟩ => T.coreCoord a e
  | ⟨.inr _,h⟩ => False.elim (by simp [rowSupport] at h)

/-- Every position refers to the original arrays. A top is its independent
mark, not a new independent copy of its correlated fan entries. -/
def row {A : Type*} (σ : T.Pos v → A) : Trial s u q v → Entry A
  | .inl a => .inl ⟨.inr (.inl ()),fun f => σ (T.topCoord a f)⟩
  | .inr (.inl b) => .inl ⟨.inl (T.1 b),fun f => σ (.inr (.inl ⟨b,f⟩))⟩
  | .inr (.inr (.inl e)) => .inl ⟨.inr (.inr (T.2.2 e)),fun f => σ (.inr (.inr (.inl ⟨e,f⟩)))⟩
  | .inr (.inr (.inr e)) => .inr (fun i => σ (.inr (.inr (.inr (e,i)))))

def cost (α β δ : ℝ) : Trial s u q v → ℝ
  | .inl _ => -actualRowCost α β δ (.inr (.inl ()))
  | .inr (.inl b) => -actualRowCost α β δ (.inl (T.1 b))
  | .inr (.inr (.inl e)) => -actualRowCost α β δ (.inr (.inr (T.2.2 e)))
  | .inr (.inr (.inr _)) => -3-δ

lemma probability_row {A : Type*} [Fintype A] (α β δ : ℝ) (σ : T.Pos v → A)
    (r : Trial s u q v) : probability α β δ A (T.row σ r) =
      (Fintype.card A:ℝ)^(T.cost α β δ r) := by
  rcases r with a | (b | (e | e)) <;> rfl

lemma square_card (τ : TwoPath) : (squareSupport τ).card = 4 := by
  simp [squareSupport,twoPath_ne τ]

lemma cardinal_positions : Fintype.card (T.Pos v) = s + (∑ b, (fan (T.1 b)).card) + 4*q + 6*v := by
  rw [← Nat.card_eq_fintype_card]
  simp only [Pos, Nat.card_sum, Nat.card_sigma, Nat.card_prod, Nat.card_fin]
  simp only [Nat.card_eq_fintype_card, Fintype.card_coe, rowSupport, Finset.card_map,
    square_card, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  omega

/-- Cancellation of the field count with the exact negative Bernoulli costs.
This is the source rank budget, with p=3-beta and f=2-alpha. -/
lemma rank_budget (α β δ : ℝ) : (Fintype.card (T.Pos v):ℝ) + ∑ r : Trial s u q v, T.cost α β δ r =
    ((3-β)-7*(2-α))*s + (2-α)*u + (2-δ)*q + (3-δ)*v := by
  rw [cardinal_positions]
  simp only [cost,Fintype.sum_sum_type,Finset.sum_const,Finset.card_univ,
    Fintype.card_fin,nsmul_eq_mul,actualRowCost,rowCost,rowSurcharge]
  push_cast
  rw [Finset.sum_neg_distrib,Finset.sum_add_distrib,Finset.sum_sub_distrib]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  ring

/-- The source good-rank condition for this literal collection shape. -/
def Good {n : ℕ} (α β δ : ℝ) (w : Entry (SymmetricAlphabet n) → Bool) : Prop :=
  ∀ σ : T.Pos v → SymmetricAlphabet n,
    Function.Injective (T.row σ) → BernoulliCandidates.Present T.row w σ →
      (Coincidence.unsignedRank σ : ℝ) ≤
        ((3-β)-7*(2-α))*s + (2-α)*u + (2-δ)*q + (3-δ)*v

instance {n : ℕ} (α β δ : ℝ) : DecidablePred (T.Good (v := v) (n := n) α β δ) :=
  fun _ => Classical.propDecidable _

lemma not_good_iff {n : ℕ} (α β δ : ℝ) (w : Entry (SymmetricAlphabet n) → Bool) :
    ¬T.Good (v := v) α β δ w ↔ Coincidence.RankBad (T.row (v := v)) (∑ r : Trial s u q v, T.cost α β δ r) w := by
  classical
  simp only [Good,Coincidence.RankBad,T.rank_budget,not_forall,not_le]
  aesop

/-- Source diagram:rank for a fixed shape, uniformly over all literal signed
assignments and all distinct actual trials. -/
theorem bad_bound {n : ℕ} {α β δ : ℝ}
    (ha : 0 ≤ α) (hb : 7*α ≤ β) (hd : 0 ≤ δ) :
    (FiniteLaw.bernoulliProduct (probability α β δ (SymmetricAlphabet n))
      (probability_mem ha hb hd)).prob (fun w => ¬T.Good (v := v) α β δ w) ≤
      Coincidence.rankRate (Fintype.card (T.Pos v)) (∑ r : Trial s u q v, T.cost α β δ r)
        (Fintype.card (SymmetricAlphabet n)) := by
  classical
  simp_rw [T.not_good_iff]
  exact Coincidence.rank_bad_bound T.row _ _ (T.cost α β δ) (T.probability_row α β δ)

end Shape
end Occurrences
end IncidenceTemplate
end HyperbolicObstruction
end

end OAI
