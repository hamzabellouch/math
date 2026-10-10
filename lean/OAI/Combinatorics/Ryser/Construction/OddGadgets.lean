import OAI.Combinatorics.Ryser.Construction.GadgetExistence

namespace OAI

/-!
# Good gadgets over every sufficiently large eligible prime

The two probability thresholds are uniform before the prime is chosen.
This extraction retains the actual sample space and both proved events;
it does not use a gadget-existence assumption or prime subsequence.
-/

open Filter Topology
noncomputable section

namespace RyserCoveringCounterexample.Construction

/-- Every sufficiently large prime congruent to two modulo three supports
an actual good gadget. The threshold is chosen before the prime. -/
theorem exists_threshold_goodGadget :
    ∃ P : ℕ, ∀ p : ℕ, P ≤ p → ∀ hp : p.Prime, p % 3 = 2 →
      5 < p ∧
        (letI : Fact p.Prime := ⟨hp⟩
         ∃ a : GadgetOutcome (ZMod p), GoodGadget a) := by
  classical
  obtain ⟨Q, hQ⟩ := LineCover.uniform_linecover_probability
    3 (1 / 4) (1 / 100) (by norm_num) (by norm_num) (by norm_num)
    (1 / 4) (by norm_num)
  have hsmall : ∀ᶠ q : ℕ in atTop,
      (q : ℝ) ^ 2 * Real.exp (-(q : ℝ) / 2048) < 1 / 4 :=
    (tendsto_order.mp tendsto_originalDensity_failure_atTop).2 _ (by norm_num)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hsmall
  refine ⟨Q + N + 2048, ?_⟩
  intro p hpbound hp hpmod
  have hp5 : 5 < p := by omega
  have hpQ : Q ≤ p := by omega
  have hpN : N ≤ p := by omega
  have hp2048 : 2048 ≤ p := by omega
  refine ⟨hp5, ?_⟩
  let : Fact p.Prime := ⟨hp⟩
  have hcard : 3 < Fintype.card (ZMod p) := by simpa using (show 3 < p by omega)
  have hcop : Nat.Coprime 3 (Fintype.card (ZMod p) - 1) :=
    coprime_three_zmod_card_sub_one hpmod
  have hsub : Incidence.SmallProperSubfields (ZMod p) := by
    intro M hM
    exact (hM (primeField_subfield_eq_top p M)).elim
  have hline := hQ (ZMod p) (by simpa using hpQ) hsub
    (cubicDeletionProcess hcop hcard)
  change 1 - (1 / 4 : ℝ) ≤
    (FiniteLaw.pi (gadgetTrials (k := ZMod p))).prob
      (LineCover.GoodLineCover (1 / 4) (1 / 100)) at hline
  rw [← gadgetLaw_map_config, FiniteLaw.prob_map] at hline
  have horiginal := prob_originalLineDensity_ge (k := ZMod p)
    (by simpa using hp2048)
  change 1 - (Fintype.card (ZMod p) : ℝ) ^ 2 *
      Real.exp (-(Fintype.card (ZMod p) : ℝ) / 2048) ≤
    (gadgetLaw (ZMod p)).prob OriginalLineDensity at horiginal
  have hfailure : (Fintype.card (ZMod p) : ℝ) ^ 2 *
      Real.exp (-(Fintype.card (ZMod p) : ℝ) / 2048) < 1 / 4 := by
    simpa using hN p hpN
  have hex : ∃ a : GadgetOutcome (ZMod p), OriginalLineDensity a ∧
      LineCover.GoodLineCover (1 / 4) (1 / 100) (gadgetConfig a) := by
    by_contra hnot
    have himp : ∀ a : GadgetOutcome (ZMod p), OriginalLineDensity a →
        ¬ LineCover.GoodLineCover (1 / 4) (1 / 100) (gadgetConfig a) := by
      intro a ha hgood
      exact hnot ⟨a, ha, hgood⟩
    have hmono := (gadgetLaw (ZMod p)).prob_mono himp
    rw [FiniteLaw.prob_compl] at hmono
    linarith
  obtain ⟨a, ha, hgood⟩ := hex
  refine ⟨a, goodGadget_of_events hcop hcard ?_ a ha hgood⟩
  simpa using (show 200 < 19 * p by omega)

end RyserCoveringCounterexample.Construction

end

end OAI
