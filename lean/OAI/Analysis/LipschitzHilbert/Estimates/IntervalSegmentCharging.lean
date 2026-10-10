import OAI.Analysis.LipschitzHilbert.Trees.SegmentMassSum

namespace OAI

/-! Unary segments may charge whole disjoint drop intervals. This includes
completed segments directly, without replacing their drops by single steps. -/

noncomputable section

open scoped BigOperators

namespace LipschitzHilbert

open PhaseCombinatorics

/-- A whole completed segment, or the interruption charged by a remainder,
provides a fixed positive drop. Pairwise disjoint charge intervals give the
same shell count as single-step charges, including one final uncharged piece. -/
theorem interval_charged_segment_shell_card {ι : Type*} [Fintype ι]
    (mass : ι → ℝ) (charge : ι → Option (ℕ × ℕ)) (n : ℕ → ℝ)
    (hn : Antitone n)
    (hnone : ∀ i j, charge i = none → charge j = none → i = j)
    (hdisjoint : ∀ i j a b c d, i ≠ j → charge i = some (a,b) →
      charge j = some (c,d) → b ≤ c ∨ d ≤ a)
    {drop lo hi : ℝ} (hdrop : 0 < drop) (hlohi : lo ≤ hi)
    (hcharge : ∀ i a b, charge i = some (a,b) →
      mass i - 2 ≤ n a ∧ n a ≤ mass i ∧ drop ≤ n a - n b)
    (S : Finset ι) (hS : ∀ i ∈ S, lo ≤ mass i ∧ mass i ≤ hi) :
    (S.card : ℝ) ≤ 2 + (hi - lo + 2) / drop := by
  classical
  let T := S.filter (fun i => charge i ≠ none)
  have hsome (i : T) : charge i = some ((charge i).getD (0,0)) := by
    cases hi : charge i with
    | none => exact False.elim ((Finset.mem_filter.mp i.property).2 hi)
    | some p => simp
  have hbound (i : T) : lo - 2 ≤ n ((charge i).getD (0,0)).1 ∧
      n ((charge i).getD (0,0)).1 ≤ hi := by
    have hiS := (Finset.mem_filter.mp i.property).1
    have h := hcharge i _ _ (hsome i)
    change mass i - 2 ≤ n ((charge i).getD (0,0)).1 ∧
      n ((charge i).getD (0,0)).1 ≤ mass i ∧
      drop ≤ n ((charge i).getD (0,0)).1 - n ((charge i).getD (0,0)).2 at h
    exact ⟨by linarith [(hS i hiS).1, h.1], h.2.1.trans (hS i hiS).2⟩
  have hsep : Separated (fun i : T => n ((charge i).getD (0,0)).1) drop := by
    intro i j hij
    have hne : (i : ι) ≠ (j : ι) := fun h => hij (Subtype.ext h)
    have h := hdisjoint i j _ _ _ _ hne (hsome i) (hsome j)
    rcases h with h | h
    · have hmono := hn h
      have hd := (hcharge i _ _ (hsome i)).2.2
      change n ((charge j).getD (0,0)).1 ≤ n ((charge i).getD (0,0)).2 at hmono
      change drop ≤ n ((charge i).getD (0,0)).1 - n ((charge i).getD (0,0)).2 at hd
      have hle : drop ≤ n ((charge i).getD (0,0)).1 - n ((charge j).getD (0,0)).1 := by
        linarith
      exact hle.trans (le_abs_self _)
    · have hmono := hn h
      have hd := (hcharge j _ _ (hsome j)).2.2
      change n ((charge i).getD (0,0)).1 ≤ n ((charge j).getD (0,0)).2 at hmono
      change drop ≤ n ((charge j).getD (0,0)).1 - n ((charge j).getD (0,0)).2 at hd
      have hle : drop ≤ n ((charge j).getD (0,0)).1 - n ((charge i).getD (0,0)).1 := by
        linarith
      exact hle.trans (by rw [abs_sub_comm]; exact le_abs_self _)
  have hT : (T.card : ℝ) ≤ 1 + (hi - lo + 2) / drop := by
    have h := separated_card_le_span (fun i : T => n ((charge i).getD (0,0)).1)
      hdrop (show lo - 2 ≤ hi by linarith) hsep hbound
    have heq : hi - (lo - 2) = hi - lo + 2 := by ring
    simpa only [Fintype.card_coe, heq] using h
  have hnoneCard : (S.filter (fun i => charge i = none)).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro i hi j hj
    exact hnone i j (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hj).2
  have hcard := Finset.card_filter_add_card_filter_not (s := S) (fun i => charge i = none)
  have hcount : S.card ≤ T.card + 1 := by
    dsimp [T]
    omega
  exact (show (S.card : ℝ) ≤ (T.card : ℝ) + 1 by exact_mod_cast hcount).trans (by linarith)

theorem interval_charged_segment_weight_sum {ι : Type*} [Fintype ι]
    (mass : ι → ℝ) (charge : ι → Option (ℕ × ℕ)) (n : ℕ → ℝ)
    (hn : Antitone n)
    (hnone : ∀ i j, charge i = none → charge j = none → i = j)
    (hdisjoint : ∀ i j a b c d, i ≠ j → charge i = some (a,b) →
      charge j = some (c,d) → b ≤ c ∨ d ≤ a)
    {drop M μ : ℝ} (hdrop : 0 < drop) (hM : 1 ≤ M) (hμ : μ ≤ 1 / 12)
    (hmass : ∀ i, M ≤ mass i)
    (hcharge : ∀ i a b, charge i = some (a,b) →
      mass i - 2 ≤ n a ∧ n a ≤ mass i ∧ drop ≤ n a - n b) :
    (∑ i, mass i ^ ((-1 + μ) * (3 / 2 : ℝ))) ≤
      2 * (2 + 17 / drop) * M ^ (-(1 / 2 : ℝ) + 3 * μ / 2) := by
  have h := finite_shell_power_sum mass hM (show 0 ≤ 2 + 17 / drop by positivity)
    (show (-1 + μ) * (3 / 2 : ℝ) ≤ -(5 / 4 : ℝ) by linarith) hmass (fun t S ht hS => by
      have ht1 : 1 ≤ t := hM.trans ht
      have h := interval_charged_segment_shell_card mass charge n hn hnone hdisjoint hdrop
        (show t ≤ 16 * t by linarith) hcharge S hS
      apply h.trans
      have hpos : 0 ≤ (t - 1) / drop := div_nonneg (by linarith) hdrop.le
      have heq : (2 + 17 / drop) * t - (2 + (16 * t - t + 2) / drop) =
          2 * (t - 1) + 2 * ((t - 1) / drop) := by ring
      linarith)
  convert h using 1
  congr 2
  ring

end LipschitzHilbert

end

end OAI
