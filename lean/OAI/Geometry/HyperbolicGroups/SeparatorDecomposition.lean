import Mathlib
import OAI.Geometry.HyperbolicGroups.SeparatorRecursion
import OAI.Geometry.HyperbolicGroups.SeparatorBudget

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PlanarRecursion
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Balanced vertex separators of size at most the square-root bound. -/
def HasBalancedSeparators (G : SimpleGraph V) (c : ℝ) : Prop :=
  ∀ U : Finset V, ∃ t : V → Fin 3,
    ((region U t 0).card : ℝ) ≤ c * Real.sqrt U.card ∧
    3 * (region U t 1).card ≤ 2 * U.card ∧
    3 * (region U t 2).card ≤ 2 * U.card ∧
    ∀ x ∈ region U t 1, ∀ y ∈ region U t 2, ¬G.Adj x y

/-- Recursive charging for finite parts and removed vertices using balanced
separators and a finite cutoff. -/
theorem partition_of_balanced_separators {G : SimpleGraph V} {c : ℝ} (hc : 0 ≤ c)
    (hsep : HasBalancedSeparators G c) (K : ℕ) (hK : 0 < K)
    (hcap : 144*c^2 ≤ (K : ℝ)) (U : Finset V) :
    ∃ P : CutPartition G U K, (P.removed.card : ℝ) ≤ 16*c*U.card/Real.sqrt K := by
  have strong : ∀ n : ℕ, ∀ W : Finset V, W.card = n → (K : ℝ) ≤ 4*(n : ℝ) →
      ∃ P : CutPartition G W K, (P.removed.card : ℝ) ≤ budget c K n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro W hW hlow
      subst n
      by_cases hsmall : W.card ≤ K
      · refine ⟨CutPartition.trivial hsmall,?_⟩
        simpa only [CutPartition.trivial,Finset.card_empty,Nat.cast_zero] using
          (budget_nonneg hc (by exact_mod_cast hK) (by positivity) hlow)
      · have hlarge : K < W.card := Nat.lt_of_not_ge hsmall
        obtain ⟨t,hs,ha,hb,hnoedge⟩ := hsep W
        have hsum : ((region W t 0).card : ℝ) + (region W t 1).card +
            (region W t 2).card = W.card := by exact_mod_cast region_card W t
        have hnum := split_numeric hc (show 0 ≤ (W.card : ℝ) by positivity) hcap
          (show (K : ℝ) ≤ W.card by exact_mod_cast hlarge.le) hs hsum
          (show (3 : ℝ)*(region W t 1).card ≤ 2*W.card by exact_mod_cast ha)
          (show (3 : ℝ)*(region W t 2).card ≤ 2*W.card by exact_mod_cast hb)
        have ha_lt : (region W t 1).card < W.card := by omega
        have hb_lt : (region W t 2).card < W.card := by omega
        have hKr : (K : ℝ) ≤ W.card := by exact_mod_cast hlarge.le
        have ha_low : (K : ℝ) ≤ 4*((region W t 1).card : ℝ) := by linarith [hnum.2.1]
        have hb_low : (K : ℝ) ≤ 4*((region W t 2).card : ℝ) := by linarith [hnum.2.2]
        obtain ⟨P,hP⟩ := ih _ ha_lt (region W t 1) rfl ha_low
        obtain ⟨Q,hQ⟩ := ih _ hb_lt (region W t 2) rfl hb_low
        refine ⟨P.merge t Q hK hnoedge,?_⟩
        have hcount : ((P.merge t Q hK hnoedge).removed.card : ℝ) ≤
            (region W t 0).card + (P.removed.card : ℝ) + Q.removed.card := by
          exact_mod_cast CutPartition.merge_removed_card t P Q hK hnoedge
        have hstep := budget_step hc (show (0 : ℝ) < K by exact_mod_cast hK)
          (show 0 ≤ (W.card : ℝ) by positivity)
          (show 0 ≤ ((region W t 0).card : ℝ) by positivity)
          hnum.2.1 hnum.2.2 hnum.1 hs hsum
        linarith
  by_cases hsmall : U.card ≤ K
  · refine ⟨CutPartition.trivial hsmall,?_⟩
    simp only [CutPartition.trivial,Finset.card_empty,Nat.cast_zero]
    positivity
  · have hlarge : K < U.card := Nat.lt_of_not_ge hsmall
    have hlow : (K : ℝ) ≤ 4*(U.card : ℝ) := by
      have hh : (K : ℝ) ≤ U.card := by exact_mod_cast hlarge.le
      linarith [show 0 ≤ (U.card : ℝ) by positivity]
    obtain ⟨P,hP⟩ := strong U.card U rfl hlow
    refine ⟨P,hP.trans ?_⟩
    unfold budget
    exact sub_le_self _ (by positivity)

end HyperbolicObstruction.PlanarRecursion
end
end

section

end
end

end OAI
