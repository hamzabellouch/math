import OAI.NumberTheory.TotientAsymptotic.ActualBlockCount

namespace OAI

/-! The complete comparison estimate for pairs with different head primes. -/

noncomputable section
open scoped Topology
open Filter
attribute [local instance] Classical.propDecidable

namespace TotientAsymptotic

def headCollisionPairs (x : ℝ) (H : ℕ) (t : ℝ) :
    Finset (TotientTuple (R x H) × TotientTuple (R x H)) :=
  (goodCollisionPairs x H t).filter (fun q => q.1.head ≠ q.2.head)

lemma head_collision_block {x t : ℝ} {H : ℕ}
    (hPH : P H ≤ H) (hL : L x H < m x) (hR : R x H < L x H)
    (hk : collisionLastIndex x 0 < L x H) (ht : t ≤ x)
    {q : TotientTuple (R x H) × TotientTuple (R x H)} (hq : q ∈ headCollisionPairs x H t) :
    GoodCollisionBlock x t H 0 x q := by
  obtain ⟨hq,hne⟩ := Finset.mem_filter.mp hq
  obtain ⟨hpair,_,hvalue⟩ := Finset.mem_filter.mp hq
  obtain ⟨hl,hr⟩ := Finset.mem_product.mp hpair
  have hl' := (mem_goodTupleFinset hPH).mp hl
  have hr' := (mem_goodTupleFinset hPH).mp hr
  refine ⟨hl',hr',hvalue,?_,?_,hl'.1.2.1,hr'.1.2.1,?_,fun _ => rfl⟩
  · exact hne
  · intro j hj
    omega
  · rw [witnessBlockValue_zero (chosenRemainder_spec hl'.1.2.2.1).1 hL hR hk,
      chosenRemainder_tuple hl'.1]
    exact hl'.1.2.2.2.trans ht

/-- All grids, canceled index sets, canceled primes, and both residual tuple
factorizations are summed. There is no fixed-prefix cost at index zero. -/
theorem head_collision_count (hford : FordLemma51Input) (hmertens : MertensProductInput) :
    ∀ᶠ H : ℕ in atTop, ∀ᶠ x : ℝ in atTop, ∀ t ≤ x,
    ((headCollisionPairs x H t).card : ℝ) ≤
      x/Real.log x*Real.exp (-B x/(8*(m x : ℝ)^4)) := by
  obtain ⟨y₀,hy₀,hcount⟩ := actual_block_count hford hmertens
  filter_upwards [hcount,eventually_collision_indices,eventually_tail_cut_separated]
    with H hc hind hsep
  filter_upwards [hc,m_tendsto.eventually (eventually_ge_atTop H),
    B_tendsto.eventually (eventually_gt_atTop (0 : ℝ)),eventually_ge_atTop y₀]
    with x hx hm hBx hxy
  intro t ht
  have hL : L x H < m x := by unfold L; omega
  have hR : R x H < L x H := by unfold R L; omega
  have hk : collisionLastIndex x 0 < L x H := (hind x hm 0 (Nat.zero_le _)).2.2
  have hzero : fordBandScale x 0=B x := by simp [fordBandScale]
  have he := hx 0 (Nat.zero_le _) hL hR t x hxy hBx
    (by rw [hzero]; linarith) (by rw [hzero]; linarith)
    (headCollisionPairs x H t)
    (fun q hq => head_collision_block (by omega) hL hR hk ht hq)
    (fun q _ q' _ he => pairSuffix_zero_injective _ he)
  simpa only [Nat.sub_zero] using he

end TotientAsymptotic

end

end OAI
