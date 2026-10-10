import OAI.Combinatorics.ContingencyTables.Transport.TranslatedCompletionCounts
import OAI.Combinatorics.ContingencyTables.Transport.MetropolisChain

namespace OAI

/-! # The ideal chain draws an actual uniform completion then translates it -/

namespace ContingencyTables.CompletionTranslation

open scoped BigOperators Classical
open CommonBasesFPRAS

variable {X I J : Type*} [Fintype X] [Nonempty X] [Fintype I] [Fintype J]

noncomputable def completionMove (R : X → Option I → ℕ) (P : X → Option J → ℕ)
    (Adj : X → X → Prop) (β : ℝ) (x y : X) : ℝ :=
  if Adj x y then β*(acceptedCount R P x y:ℝ)/(blockCount R P x:ℝ) else 0

omit [Fintype X] [Nonempty X] in
lemma completionMove_nonnegative (R : X → Option I → ℕ) (P : X → Option J → ℕ)
    (Adj : X → X → Prop) (β : ℝ) (hβ : 0 ≤ β) (x y : X) :
    0 ≤ completionMove R P Adj β x y := by
  unfold completionMove
  split_ifs
  · exact div_nonneg (mul_nonneg hβ (Nat.cast_nonneg _)) (Nat.cast_nonneg _)
  · exact le_rfl

omit [Fintype X] [Nonempty X] in
lemma completionMove_le_proposal (R : X → Option I → ℕ) (P : X → Option J → ℕ)
    (htotal : ∀ x,(∑ i,R x i)=∑ j,P x j)
    (Adj : X → X → Prop) (β : ℝ) (hβ : 0 ≤ β) (x y : X) :
    completionMove R P Adj β x y ≤ if Adj x y then β else 0 := by
  unfold completionMove
  split_ifs
  · have hf : (0:ℝ) < blockCount R P x := by exact_mod_cast blockCount_pos R P htotal x
    have hc : (acceptedCount R P x y:ℝ) ≤ blockCount R P x := by exact_mod_cast acceptedCount_le R P x y
    apply (div_le_iff₀ hf).mpr
    exact mul_le_mul_of_nonneg_left hc hβ
  · exact le_rfl

omit [Nonempty X] in
lemma completionMove_row (R : X → Option I → ℕ) (P : X → Option J → ℕ)
    (htotal : ∀ x,(∑ i,R x i)=∑ j,P x j)
    (Adj : X → X → Prop) (β : ℝ) (hβ : 0 ≤ β) (D : ℕ)
    (hdegree : ∀ x,(Finset.univ.filter (Adj x)).card ≤ D)
    (hproposal : (D:ℝ)*β ≤ 1/2) (x : X) : ∑ y,completionMove R P Adj β x y ≤ 1/2 := by
  calc
    _ ≤ ∑ y,if Adj x y then β else 0 :=
      Finset.sum_le_sum (fun y _ => completionMove_le_proposal R P htotal Adj β hβ x y)
    _ = ((Finset.univ.filter (Adj x)).card:ℝ)*β := by rw [← Finset.sum_filter]; simp
    _ ≤ (D:ℝ)*β := mul_le_mul_of_nonneg_right (by exact_mod_cast hdegree x) hβ
    _ ≤ _ := hproposal

omit [Nonempty X] in
lemma completionMove_reversible (R : X → Option I → ℕ) (P : X → Option J → ℕ)
    (htotal : ∀ x,(∑ i,R x i)=∑ j,P x j)
    (Adj : X → X → Prop) (hsym : ∀ x y,Adj x y ↔ Adj y x) (β : ℝ) (x y : X) :
    ((blockCount R P x:ℝ)/MetropolisChain.normalizer (fun z => (blockCount R P z:ℝ)))*
      completionMove R P Adj β x y=
    ((blockCount R P y:ℝ)/MetropolisChain.normalizer (fun z => (blockCount R P z:ℝ)))*
      completionMove R P Adj β y x := by
  have hx : (blockCount R P x:ℝ)≠0 := ne_of_gt (by exact_mod_cast blockCount_pos R P htotal x)
  have hy : (blockCount R P y:ℝ)≠0 := ne_of_gt (by exact_mod_cast blockCount_pos R P htotal y)
  unfold completionMove
  by_cases ha : Adj x y
  · rw [ite_eq_left ha,ite_eq_left ((hsym x y).mp ha),acceptedCount_symmetric R P htotal x y]
    exact (div_mul_div_cancel₀' hx _ _).trans (div_mul_div_cancel₀' hy _ _).symm
  · rw [ite_eq_right ha,ite_eq_right ((hsym x y).not.mp ha)]
    simp only [mul_zero]

noncomputable def completionChain (R : X → Option I → ℕ) (P : X → Option J → ℕ)
    (htotal : ∀ x,(∑ i,R x i)=∑ j,P x j)
    (Adj : X → X → Prop) (hsym : ∀ x y,Adj x y ↔ Adj y x)
    (β : ℝ) (hβ : 0 ≤ β) (D : ℕ)
    (hdegree : ∀ x,(Finset.univ.filter (Adj x)).card ≤ D)
    (hproposal : (D:ℝ)*β ≤ 1/2) : FiniteChain X :=
  FiniteChain.ofMoves
    (fun x => (blockCount R P x:ℝ)/MetropolisChain.normalizer (fun z => (blockCount R P z:ℝ)))
    (completionMove R P Adj β)
    (fun x => div_pos (by exact_mod_cast blockCount_pos R P htotal x)
      (MetropolisChain.normalizer_pos _ (fun z => by exact_mod_cast blockCount_pos R P htotal z)))
    (by rw [← Finset.sum_div]; exact div_self (ne_of_gt
      (MetropolisChain.normalizer_pos _ (fun z => by exact_mod_cast blockCount_pos R P htotal z))))
    (completionMove_nonnegative R P Adj β hβ)
    (completionMove_row R P htotal Adj β hβ D hdegree hproposal)
    (completionMove_reversible R P htotal Adj hsym β)

end ContingencyTables.CompletionTranslation

end OAI
