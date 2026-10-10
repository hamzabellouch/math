import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.DisjointPool
import OAI.Combinatorics.KMedianRecovery.Recovery.Map

namespace OAI

namespace MetricKMedianRecovery.PriceBisection
open PhaseCountCrossing

theorem close_sandwich (count : ℚ → ℕ) (k N : ℕ) (U : ℚ) (hU : 0 ≤ U)
    (hs : Sandwich k (count 0) (count U)) :
    (∃ s : ℚ, 0 ≤ s ∧ s ≤ U ∧ count s = k) ∨
    ∃ l u : ℚ, 0 ≤ l ∧ l ≤ u ∧ u ≤ U ∧ u-l ≤ 1/(2:ℚ)^N ∧
      Sandwich k (count l) (count u) := by
  have direct : ∀ f : ℚ → ℕ, k ≤ f 0 → f U ≤ k →
      (∃ s : ℚ, 0 ≤ s ∧ s ≤ U ∧ f s = k) ∨
      ∃ l u : ℚ, 0 ≤ l ∧ l ≤ u ∧ u ≤ U ∧ u-l ≤ 1/(2:ℚ)^N ∧
        f u < k ∧ k < f l := by
    intro f ha hb
    obtain ⟨l,u,hl,hlu,hu,hw,hcl,hcu⟩ := close_bracket f k N 0 U hU ha hb
    by_cases hckl : f l = k
    · exact Or.inl ⟨l,hl,hlu.trans hu,hckl⟩
    by_cases hcku : f u = k
    · exact Or.inl ⟨u,hl.trans hlu,hu,hcku⟩
    exact Or.inr ⟨l,u,hl,hlu,hu,hw,by omega,by omega⟩
  rcases hs with hs | hs
  · rcases direct (fun s => count (U-s)) (by simpa using hs.2.le) (by simpa using hs.1.le) with
      ⟨s,hs0,hsU,hsk⟩ | ⟨l,u,hl,hlu,hu,hw,hcu,hcl⟩
    · exact Or.inl ⟨U-s,by linarith,by linarith,hsk⟩
    · exact Or.inr ⟨U-u,U-l,by linarith,by linarith,by linarith,
        by linarith,Or.inl ⟨hcu,hcl⟩⟩
  · rcases direct count hs.2.le hs.1.le with
      ⟨s,hs0,hsU,hsk⟩ | ⟨l,u,hl,hlu,hu,hw,hcu,hcl⟩
    · exact Or.inl ⟨s,hs0,hsU,hsk⟩
    · exact Or.inr ⟨l,u,hl,hlu,hu,hw,Or.inr ⟨hcu,hcl⟩⟩

end MetricKMedianRecovery.PriceBisection

namespace MetricKMedianRecovery.PhaseLengthInterpolation
open PhaseMergeCompletion FreshCopyEndpoints PhaseCountCrossing
variable {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]

def Reach (loc : D → X) (F B Q : Finset X) (i : X) (H : List X)
    (v lam : ℝ) (q n : ℕ) (s : ℚ) (c : ℕ) : Prop := by
  classical
  letI : PseudoMetricSpace (X ⊕ ℝ) := familyMetric i
  exact Attains (fun j => incl (loc j)) (F.image incl)
    (insert (Sum.inr (s:ℝ)) (B.image incl))
    (insert (Sum.inr (s:ℝ)) ((Q ∪ H.toFinset).image incl)) v lam q n c

theorem search (loc : D → X) (F B Q : Finset X) (i : X) (H : List X)
    (v lam : ℝ) (q n k N a b : ℕ) (U : ℚ) (hU : 0 < U)
    (hQ : Q ∪ H.toFinset ⊆ F ∪ B)
    (ha : Reach loc F B Q i H v lam q n 0 a)
    (hb : Reach loc F B Q i H v lam q n U b) (hab : Sandwich k a b) :
    (∃ s : ℚ, 0 ≤ s ∧ s ≤ U ∧ Reach loc F B Q i H v lam q n s k) ∨
    ∃ l u : ℚ, 0 ≤ l ∧ l ≤ u ∧ u ≤ U ∧ u-l ≤ 1/(2:ℚ)^N ∧
      ∃ c d, Sandwich k c d ∧ Reach loc F B Q i H v lam q n l c ∧
        Reach loc F B Q i H v lam q n u d := by
  classical
  have he : ∀ s : ℚ, ∃ c, Reach loc F B Q i H v lam q n s c := by
    intro s
    exact leaf_attains loc F B Q i H v lam q n hQ s
  choose count hc using he
  let chosen : ℚ → ℕ := fun s => if s = 0 then a else if s = U then b else count s
  have hchosen : ∀ s, Reach loc F B Q i H v lam q n s (chosen s) := by
    intro s
    dsimp only [chosen]
    split_ifs with hs hs
    · subst s; exact ha
    · subst s; exact hb
    · exact hc s
  have hzero : chosen 0 = a := by simp only [chosen,ite_true]
  have hupper : chosen U = b := by simp only [chosen,ite_eq_right (ne_of_gt hU),ite_true]
  have hs : Sandwich k (chosen 0) (chosen U) := by simpa only [hzero,hupper] using hab
  rcases PriceBisection.close_sandwich chosen k N U hU.le hs with
    ⟨s,hs0,hsU,hsk⟩ | ⟨l,u,hl,hlu,hu,hw,hcs⟩
  · exact Or.inl ⟨s,hs0,hsU,hsk ▸ hchosen s⟩
  · exact Or.inr ⟨l,u,hl,hlu,hu,hw,chosen l,chosen u,hcs,hchosen l,hchosen u⟩

end MetricKMedianRecovery.PhaseLengthInterpolation

end OAI
