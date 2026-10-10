import Mathlib
import OAI.Geometry.HyperbolicGroups.Test
import OAI.Geometry.HyperbolicGroups.SixCounts
import OAI.Geometry.HyperbolicGroups.FiniteSelection

namespace OAI

section
section


noncomputable section
open scoped BigOperators
open Filter Topology
namespace HyperbolicObstruction
namespace IncidenceTemplate
variable {J A : Type*} [Fintype J] [Fintype A] [DecidableEq A] [Nonempty A]

/-- Finite simultaneous selection from the source's independent master arrays
and six-letter array. Its hypothesis is an explicit numerical upper bound,
which tends to zero; it assumes no good table or coupling. -/
theorem exists_tables_of_estimate (T : J → ConditionalTest) {α β δ ε τ : ℝ}
    (ha : 0 ≤ α) (hb : 7*α ≤ β) (hd : 0 ≤ δ)
    (hsmall : ∀ j, ((T j).k+1:ℝ)*(β+90*δ) ≤ 1/2)
    (hN : ∀ j, (T j).threshold ≤ Fintype.card A)
    (hε0 : 0 < ε) (hε1 : ε < 1) (hτ0 : 0 < τ) (hτ2 : τ ≤ 2)
    (hest : (∑ j, (T j).rate (Fintype.card A)) +
      ε*(60*(Fintype.card A:ℝ)^2*Real.exp (-τ^2*(Fintype.card A:ℝ)^(1-δ)/4)) < ε) :
    ∃ (w : TableModel.Entry (A := A) rowSupport → Bool) (d : (Fin 6 → A) → Bool),
      ¬SixTable.BadPairs δ τ d ∧ ∀ j, (T j).Satisfies w
        (ε/(1-ε) + (1-((Fintype.card A).descFactorial ((T j).k+1):ℝ)/
          (Fintype.card A:ℝ)^((T j).k+1))) := by
  classical
  let μ : FiniteLaw (TableModel.Entry (A := A) rowSupport → Bool) :=
    TableModel.law rowSupport (actualProbability α β δ A) (actualProbability_mem ha hb hd)
  let ν := SixTable.law (A := A) δ hd
  let E (j : J) (w : TableModel.Entry (A := A) rowSupport → Bool) :=
    (T j).error α β δ ha hb hd (hN j) w
  have hx (j : J) : (μ.prod ν).expect (fun z => E j z.1) ≤ (T j).rate (Fintype.card A) := by
    rw [FiniteLaw.expect_prod_fst]
    exact ConditionalTest.expectedError _ ha hb hd (hsmall j) (hN j)
  have hb' : (μ.prod ν).prob (fun z => SixTable.BadPairs δ τ z.2) ≤
      60*(Fintype.card A:ℝ)^2*Real.exp (-τ^2*(Fintype.card A:ℝ)^(1-δ)/4) := by
    unfold FiniteLaw.prob
    rw [FiniteLaw.expect_prod_snd μ ν (fun d => if SixTable.BadPairs δ τ d then 1 else 0)]
    exact SixTable.badPairs_bound hd hτ0 hτ2
  have hh : (∑ j, (μ.prod ν).expect (fun z => E j z.1)) +
      ε*(μ.prod ν).prob (fun z => SixTable.BadPairs δ τ z.2) < ε :=
    lt_of_le_of_lt (add_le_add (Finset.sum_le_sum fun j _ => hx j)
      (mul_le_mul_of_nonneg_left hb' hε0.le)) hest
  obtain ⟨⟨w,d⟩,hw,hE⟩ := FiniteLaw.exists_good_simultaneously (μ.prod ν) (fun j z => E j z.1)
    (fun j z => ConditionalTest.error_nonneg _ _ _ _ _ _ _ _ _) (fun z => SixTable.BadPairs δ τ z.2)
    hε0 hh
  exact ⟨w,d,hw,fun j => (T j).satisfies_of_error ha hb hd (hN j) w hε1 (hE j).le⟩

/-- The alphabet of rank n+1, including each generator and its formal inverse.
This is an arbitrarily large cofinal set of the literal source alphabets. -/
abbrev SymmetricAlphabet (n : ℕ) := Fin (n+1) × Bool

lemma card_symmetricAlphabet (n : ℕ) : Fintype.card (SymmetricAlphabet n) = 2*(n+1) := by
  simp [Fintype.card_prod,Nat.mul_comm]

lemma alphabet_size_tendsto : Tendsto (fun n => Fintype.card (SymmetricAlphabet n)) atTop atTop := by
  apply tendsto_atTop_mono (f := fun n : ℕ => n) _ tendsto_id
  intro n
  rw [card_symmetricAlphabet]
  omega

/-- Every finite set of literal conditional tests is simultaneously realizable
with small errors on arbitrarily large source alphabets. Parameters are fixed
first; the actual table is chosen only after N is large. -/
theorem eventually_exists_tables (T : J → ConditionalTest) {α β δ ε τ : ℝ}
    (ha : 0 ≤ α) (hb : 7*α ≤ β) (hd : 0 ≤ δ) (hd1 : δ < 1)
    (hsmall : ∀ j, ((T j).k+1:ℝ)*(β+90*δ) ≤ 1/2)
    (hε0 : 0 < ε) (hε1 : ε < 1) (hτ0 : 0 < τ) (hτ2 : τ ≤ 2) :
    ∀ᶠ n in atTop, ∃ (w : TableModel.Entry (A := SymmetricAlphabet n) rowSupport → Bool)
      (d : (Fin 6 → SymmetricAlphabet n) → Bool),
      ¬SixTable.BadPairs δ τ d ∧ ∀ j, (T j).Satisfies w
        (ε/(1-ε) + (1-((Fintype.card (SymmetricAlphabet n)).descFactorial ((T j).k+1):ℝ)/
          (Fintype.card (SymmetricAlphabet n):ℝ)^((T j).k+1))) := by
  have hs : Tendsto (fun N => ∑ j, (T j).rate N) atTop (𝓝 0) := by
    simpa using tendsto_finsetSum Finset.univ (fun j _ => (T j).rate_tendsto)
  have hd' := (SixTable.badPairs_rate_tendsto hd1 hτ0).const_mul ε
  have hh : Tendsto (fun N : ℕ => (∑ j, (T j).rate N) +
      ε*(60*(N:ℝ)^2*Real.exp (-τ^2*(N:ℝ)^(1-δ)/4))) atTop (𝓝 0) := by
    simpa only [mul_zero,zero_add] using hs.add hd'
  have he := (hh.comp alphabet_size_tendsto).eventually (gt_mem_nhds hε0)
  let K : ℕ := Finset.univ.sup (fun j => (T j).threshold)
  have hK := alphabet_size_tendsto.eventually (eventually_ge_atTop K)
  filter_upwards [he,hK] with n hn hN
  apply exists_tables_of_estimate T ha hb hd hsmall _ hε0 hε1 hτ0 hτ2 hn
  intro j
  exact (Finset.le_sup (f := fun j => (T j).threshold) (Finset.mem_univ j)).trans hN

end IncidenceTemplate
end HyperbolicObstruction
end
end

section

end
end

end OAI
