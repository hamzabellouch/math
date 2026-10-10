import OAI.Combinatorics.ContingencyTables.Transport.TranslatedCompletionChain

namespace OAI

/-! # Exact edge flow of the completion-translation chain -/

namespace ContingencyTables.CompletionTranslation

open scoped BigOperators Classical
open CommonBasesFPRAS

variable {X I J : Type*} [Fintype X] [Nonempty X] [Fintype I] [Fintype J]

omit [Nonempty X] in
lemma completionMove_flow (R : X → Option I → ℕ) (P : X → Option J → ℕ)
    (htotal : ∀ x,(∑ i,R x i)=∑ j,P x j)
    (Adj : X → X → Prop) (β : ℝ) (x y : X) :
    ((blockCount R P x:ℝ)/MetropolisChain.normalizer (fun z => (blockCount R P z:ℝ)))*
      completionMove R P Adj β x y =
      if Adj x y then β*(acceptedCount R P x y:ℝ)/
        MetropolisChain.normalizer (fun z => (blockCount R P z:ℝ)) else 0 := by
  have hx : (blockCount R P x:ℝ)≠0 := ne_of_gt (by exact_mod_cast blockCount_pos R P htotal x)
  unfold completionMove
  split_ifs
  · exact div_mul_div_cancel₀' hx _ _
  · exact mul_zero _

/-- The flow formula includes the holding terms: those contribute zero
energy. The numerator counts literal acceptable completion translations. -/
theorem completionChain_energy (R : X → Option I → ℕ) (P : X → Option J → ℕ)
    (htotal : ∀ x,(∑ i,R x i)=∑ j,P x j)
    (Adj : X → X → Prop) (hsym : ∀ x y,Adj x y ↔ Adj y x)
    (β : ℝ) (hβ : 0 ≤ β) (D : ℕ)
    (hdegree : ∀ x,(Finset.univ.filter (Adj x)).card ≤ D)
    (hproposal : (D:ℝ)*β ≤ 1/2) (H : X → ℝ) :
    (completionChain R P htotal Adj hsym β hβ D hdegree hproposal).energy H=
      (∑ x,∑ y,if Adj x y then
        β*(acceptedCount R P x y:ℝ)*(H x-H y)^2 else 0)/
          (2*MetropolisChain.normalizer (fun z => (blockCount R P z:ℝ))) := by
  unfold completionChain
  rw [FiniteChain.ofMoves_energy]
  simp_rw [completionMove_flow R P htotal Adj β]
  have hterm (x y : X) :
      (if Adj x y then β*(acceptedCount R P x y:ℝ)/
        MetropolisChain.normalizer (fun z => (blockCount R P z:ℝ)) else 0)*(H x-H y)^2 =
      (if Adj x y then β*(acceptedCount R P x y:ℝ)*(H x-H y)^2 else 0)/
        MetropolisChain.normalizer (fun z => (blockCount R P z:ℝ)) := by
    split_ifs <;> ring
  simp_rw [hterm,← Finset.sum_div]
  ring

omit [Fintype X] [Nonempty X] in
/-- A half-acceptance estimate yields the min-weight comparison on every
actual edge, with no request for completion-count evaluation. -/
lemma completionMove_lower (R : X → Option I → ℕ) (P : X → Option J → ℕ)
    (htotal : ∀ x,(∑ i,R x i)=∑ j,P x j)
    (Adj : X → X → Prop) (β : ℝ) (hβ : 0 ≤ β) (x y : X)
    (hxy : Adj x y)
    (haccept : (blockCount R P x:ℝ)/2 ≤ acceptedCount R P x y) :
    β/2*min 1 ((blockCount R P y:ℝ)/blockCount R P x) ≤ completionMove R P Adj β x y := by
  have hx : (0:ℝ)<blockCount R P x := by exact_mod_cast blockCount_pos R P htotal x
  have hm : β/2*min 1 ((blockCount R P y:ℝ)/blockCount R P x) ≤ β/2 := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left
      (min_le_left (1:ℝ) ((blockCount R P y:ℝ)/blockCount R P x)) (by positivity : 0 ≤ β/2)
  apply hm.trans
  unfold completionMove
  rw [ite_eq_left hxy]
  apply (le_div_iff₀ hx).mpr
  nlinarith [mul_nonneg hβ (sub_nonneg.mpr haccept)]

end ContingencyTables.CompletionTranslation

end OAI
