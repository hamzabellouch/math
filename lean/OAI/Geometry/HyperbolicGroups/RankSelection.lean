import Mathlib
import OAI.Geometry.HyperbolicGroups.RankCollection

namespace OAI

noncomputable section
open scoped BigOperators
open Filter Topology
namespace HyperbolicObstruction
namespace FiniteLaw

lemma bernoulliProduct_sum_expect {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] (p : I → ℝ) (q : J → ℝ)
    (hp : ∀ i, p i ∈ Set.Icc (0:ℝ) 1) (hq : ∀ i, q i ∈ Set.Icc (0:ℝ) 1)
    (f : (I ⊕ J → Bool) → ℝ) :
    (bernoulliProduct (Sum.elim p q) (fun i => by cases i <;> simp_all)).expect f =
      ((bernoulliProduct p hp).prod (bernoulliProduct q hq)).expect
        (fun z => f (Sum.elim z.1 z.2)) := by
  unfold expect
  rw [← (Equiv.sumArrowEquivProdArrow I J Bool).symm.sum_comp
    (fun w => (bernoulliProduct (Sum.elim p q) _).mass w * f w)]
  apply Finset.sum_congr rfl
  intro z _
  simp only [bernoulliProduct,prod,Fintype.prod_sum_type,Sum.elim_inl,Sum.elim_inr]
  rfl

end FiniteLaw
namespace IncidenceTemplate
namespace Occurrences

lemma expect_join {n : ℕ} {α β δ : ℝ} (ha : 0 ≤ α) (hb : 7*α ≤ β) (hd : 0 ≤ δ)
    (f : (Entry (SymmetricAlphabet n) → Bool) → ℝ) :
    (FiniteLaw.bernoulliProduct (probability α β δ (SymmetricAlphabet n))
      (probability_mem ha hb hd)).expect f =
    ((TableModel.law rowSupport (actualProbability α β δ (SymmetricAlphabet n))
      (actualProbability_mem ha hb hd)).prod (SixTable.law (A := SymmetricAlphabet n) δ hd)).expect
        (fun z => f (Sum.elim z.1 z.2)) := by
  convert FiniteLaw.bernoulliProduct_sum_expect
    (fun e : TableModel.Entry (A := SymmetricAlphabet n) rowSupport => actualProbability α β δ (SymmetricAlphabet n) e.1)
    (fun _ : Fin 6 → SymmetricAlphabet n => SixTable.probability (A := SymmetricAlphabet n) δ)
    (fun e => actualProbability_mem ha hb hd e.1) (fun _ => SixTable.probability_mem hd) f using 1
  · congr 2
    funext e
    cases e <;> rfl
  · rfl

lemma rank_bad_join_bound (M : ℕ) {n : ℕ} {α β δ : ℝ}
    (ha : 0 ≤ α) (hb : 7*α ≤ β) (hd : 0 ≤ δ) :
    ((TableModel.law rowSupport (actualProbability α β δ (SymmetricAlphabet n))
      (actualProbability_mem ha hb hd)).prod (SixTable.law (A := SymmetricAlphabet n) δ hd)).prob
        (fun z => ¬GoodUpTo M α β δ (Sum.elim z.1 z.2)) ≤
      rankRate M α β δ (Fintype.card (SymmetricAlphabet n)) := by
  have hh := rank_bad_bound M (n := n) ha hb hd
  unfold FiniteLaw.prob at *
  rw [expect_join ha hb hd] at hh
  exact hh

/-- Simultaneous selection with the genuine bounded-rank event, not independent
new copies of the arrays used for sampling. -/
theorem exists_tables_of_estimate {J : Type*} [Fintype J]
    (T : J → ConditionalTest) (M n : ℕ) {α β δ ε τ : ℝ}
    (ha : 0 ≤ α) (hb : 7*α ≤ β) (hd : 0 ≤ δ)
    (hsmall : ∀ j, ((T j).k+1:ℝ)*(β+90*δ) ≤ 1/2)
    (hN : ∀ j, (T j).threshold ≤ Fintype.card (SymmetricAlphabet n))
    (hε0 : 0 < ε) (hε1 : ε < 1) (hτ0 : 0 < τ) (hτ2 : τ ≤ 2)
    (hest : (∑ j, (T j).rate (Fintype.card (SymmetricAlphabet n))) +
      ε*(60*(Fintype.card (SymmetricAlphabet n):ℝ)^2*
        Real.exp (-τ^2*(Fintype.card (SymmetricAlphabet n):ℝ)^(1-δ)/4) +
        rankRate M α β δ (Fintype.card (SymmetricAlphabet n))) < ε) :
    ∃ (w : TableModel.Entry (A := SymmetricAlphabet n) rowSupport → Bool)
      (d : (Fin 6 → SymmetricAlphabet n) → Bool),
      ¬SixTable.BadPairs δ τ d ∧ GoodUpTo M α β δ (Sum.elim w d) ∧
      ∀ j, (T j).Satisfies w
        (ε/(1-ε) + (1-((Fintype.card (SymmetricAlphabet n)).descFactorial ((T j).k+1):ℝ)/
          (Fintype.card (SymmetricAlphabet n):ℝ)^((T j).k+1))) := by
  classical
  let A := SymmetricAlphabet n
  let μ : FiniteLaw (TableModel.Entry (A := A) rowSupport → Bool) :=
    TableModel.law rowSupport (actualProbability α β δ A) (actualProbability_mem ha hb hd)
  let ν := SixTable.law (A := A) δ hd
  let E (j : J) (w : TableModel.Entry (A := A) rowSupport → Bool) :=
    (T j).error α β δ ha hb hd (hN j) w
  have hx (j : J) : (μ.prod ν).expect (fun z => E j z.1) ≤ (T j).rate (Fintype.card A) := by
    rw [FiniteLaw.expect_prod_fst]
    exact ConditionalTest.expectedError _ ha hb hd (hsmall j) (hN j)
  let B (z : (TableModel.Entry (A := A) rowSupport → Bool) × ((Fin 6 → A) → Bool)) :=
    SixTable.BadPairs δ τ z.2 ∨ ¬GoodUpTo M α β δ (Sum.elim z.1 z.2)
  have hb' : (μ.prod ν).prob B ≤
      60*(Fintype.card A:ℝ)^2*Real.exp (-τ^2*(Fintype.card A:ℝ)^(1-δ)/4) +
        rankRate M α β δ (Fintype.card A) := by
    apply (FiniteLaw.prob_or_le (μ.prod ν) _ _).trans
    apply add_le_add _ (rank_bad_join_bound M ha hb hd)
    unfold FiniteLaw.prob
    rw [FiniteLaw.expect_prod_snd μ ν (fun d => if SixTable.BadPairs δ τ d then 1 else 0)]
    exact SixTable.badPairs_bound hd hτ0 hτ2
  have hh : (∑ j, (μ.prod ν).expect (fun z => E j z.1)) + ε*(μ.prod ν).prob B < ε :=
    lt_of_le_of_lt (add_le_add (Finset.sum_le_sum fun j _ => hx j)
      (mul_le_mul_of_nonneg_left hb' hε0.le)) hest
  obtain ⟨⟨w,d⟩,hw,hE⟩ := FiniteLaw.exists_good_simultaneously (μ.prod ν) (fun j z => E j z.1)
    (fun j z => ConditionalTest.error_nonneg _ _ _ _ _ _ _ _ _) B hε0 hh
  refine ⟨w,d,fun h => hw (Or.inl h),not_not.mp (fun h => hw (Or.inr h)),?_⟩
  exact fun j => (T j).satisfies_of_error ha hb hd (hN j) w hε1 (hE j).le

end Occurrences
end IncidenceTemplate
end HyperbolicObstruction
end

end OAI
