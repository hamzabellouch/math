import OAI.Combinatorics.ContingencyTables.Rooted.RootedTerminalRegions
import OAI.Combinatorics.ContingencyTables.Counting.CompanionTerminalMass

namespace OAI

/-! # The actual selected-root terminal normalizer approximates the table count -/

namespace ContingencyTables.RootedTerminalMass

open scoped BigOperators Classical
open CompanionFactorialApplication CompanionPhysicalTables RootedPhysicalTables RootedPhysicalNormalizer
open RootedFarMass RootedNearMass RootedTerminalRegions BalancedCellFibres TreeMarginalSignature
open CompanionNearMass (cellPositions)
open CompanionTerminalMass (TreeCell Endpoints tableCount tableCount_ge_one treeCell_card_le
  feasible_sum_eq_tableCount)

variable {I J : Type*} [Fintype I] [Fintype J]

/-- Actual endpoint tables and the proved scalar signature estimates
control the entire union of narrow tree violations. -/
lemma total_near_mass_le (A : Instance I J) (R : RootedCompletion.Selection A.T) (E : Endpoints A) (alpha gamma : ℝ)
    (ha : 0 ≤ alpha) (hg : 0 < gamma) (hW : 20*A.d ≤ A.W) (B K : ℕ)
    (hB : (∏ a : I×J,(A.b a.1 a.2+1)) ≤ 2^B) (hBK : 2*B ≤ K) (hK : 0 < K) :
    (∑ t : TreeCell A,nearMass A R alpha t.val gamma) ≤
      (4*A.d*gamma*K:ℝ)*physicalMass A R alpha := by
  have hM : 0 < physicalMass A R alpha := by
    exact lt_of_lt_of_le (by norm_num : (0:ℝ)<1)
      ((tableCount_ge_one A).trans (table_count_le_mass A R alpha))
  have hh (t : TreeCell A) : nearMass A R alpha t.val gamma ≤
      (4*gamma*K:ℝ)*physicalMass A R alpha := by
    apply (div_le_iff₀ hM).mp
    exact near_mass_bound A R alpha gamma t.val t.property ha hg hW B K hB hBK hK
      (E.lowerTable t) (E.upperTable t) (E.lowerBounds t) (E.upperBounds t)
      (E.lowerRows t) (E.lowerColumns t) (E.upperRows t) (E.upperColumns t)
      (E.lowerAttains t) (E.upperAttains t)
  calc
    _ ≤ ∑ _t : TreeCell A,(4*gamma*K:ℝ)*physicalMass A R alpha :=
      Finset.sum_le_sum (fun t _ => hh t)
    _ = (Fintype.card (TreeCell A):ℝ)*((4*gamma*K:ℝ)*physicalMass A R alpha) := by simp
    _ ≤ (A.d:ℝ)*((4*gamma*K:ℝ)*physicalMass A R alpha) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast treeCell_card_le A) (by positivity)
    _ = _ := by ring

lemma mass_le_table_far_near (A : Instance I J) (R : RootedCompletion.Selection A.T) (alpha gamma : ℝ) (K : ℕ)
    (ha : 0 < alpha) (hg1 : gamma ≤ 1) (hscale : 4*(K:ℝ) ≤ alpha*gamma) :
    physicalMass A R alpha ≤ tableCount A+
      (∑ a : Profiles (cellWidth A),if 4*(K:ℝ) ≤ alpha*actualPenalty A R a
        then actualWeight A R alpha a else 0)+
      ∑ t : TreeCell A,nearMass A R alpha t.val gamma := by
  have hh := TerminalMassCover.mass_le_cover (actualWeight A R alpha) (Feasible A)
    (fun a => 4*(K:ℝ) ≤ alpha*actualPenalty A R a)
    (fun t : TreeCell A => fun a => a t.val ∈ cellPositions A t.val gamma)
    (fun a => RootedPenalty.physicalWeight_nonnegative A R alpha _)
    (fun a ha => feasible_weight_one A R alpha a ha)
    (by
      intro a hw hbad
      rcases infeasible_in_far_or_near A R alpha gamma K ha hg1 hscale a hw hbad with hf|⟨t,ht,hn⟩
      · exact Or.inl hf
      · exact Or.inr ⟨⟨t,ht⟩,hn⟩)
  change physicalMass A R alpha ≤ _ at hh
  rw [feasible_sum_eq_tableCount] at hh
  apply hh.trans_eq
  congr 1
  apply Finset.sum_congr rfl
  intro t _
  unfold nearMass
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : a t.val∈cellPositions A t.val gamma <;> simp only [ha,ite_true,ite_false]

/-- The terminal normalizer estimate follows from the finite table
bijection, root integrality, far bound and tree-marginal estimates.
The manuscript's explicit choices of K, gamma and the final coefficient
satisfy its arithmetic conditions. -/
theorem terminal_count_estimate (A : Instance I J) (R : RootedCompletion.Selection A.T) (E : Endpoints A)
    (alpha gamma epsilon : ℝ) (B K : ℕ)
    (ha : 0 < alpha) (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    (he : 0 < epsilon) (he1 : epsilon < 1)
    (hscale : 4*(K:ℝ) ≤ alpha*gamma) (hnear : 4*(A.d:ℝ)*gamma*K ≤ epsilon/128)
    (hfar : (2:ℝ)^(-(3*K:ℕ):ℝ) ≤ epsilon/128)
    (hW : 20*A.d ≤ A.W) (hB : (∏ a : I×J,(A.b a.1 a.2+1)) ≤ 2^B)
    (hBK : 2*B ≤ K) (hK : 0 < K) :
    tableCount A ≤ CommonBasesFPRAS.slotTotal TwoLiftStates.pairs (RootedFactorialApplication.f A R alpha) ∅ ∧
      CommonBasesFPRAS.slotTotal TwoLiftStates.pairs (RootedFactorialApplication.f A R alpha) ∅ ≤ (1+epsilon/32)*tableCount A := by
  rw [normalizer_eq_physical_mass]
  have hZM : tableCount A ≤ physicalMass A R alpha := table_count_le_mass A R alpha
  have hM1 := (tableCount_ge_one A).trans hZM
  have hM : 0 ≤ physicalMass A R alpha := by linarith
  have hcover := mass_le_table_far_near A R alpha gamma K ha hg1 hscale
  have hfarMass := (far_mass_le A R alpha B K hW hB hBK).trans hfar
  have hfarScaled : (∑ a : Profiles (cellWidth A),if 4*(K:ℝ) ≤ alpha*actualPenalty A R a
      then actualWeight A R alpha a else 0) ≤ (epsilon/128)*physicalMass A R alpha := by
    exact hfarMass.trans (by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hM1
        (show 0 ≤ epsilon/128 by positivity))
  have hnearMass := total_near_mass_le A R E alpha gamma ha.le hg hW B K hB hBK hK
  have hnearScaled : (∑ t : TreeCell A,nearMass A R alpha t.val gamma) ≤
      (epsilon/128)*physicalMass A R alpha :=
    hnearMass.trans (mul_le_mul_of_nonneg_right hnear hM)
  have hbad : physicalMass A R alpha ≤ tableCount A+(epsilon/64)*physicalMass A R alpha := by
    linarith
  exact TerminalMassCover.relative_count_bound (tableCount A) (physicalMass A R alpha) epsilon
    (by linarith [tableCount_ge_one A]) he he1 hZM hbad

end ContingencyTables.RootedTerminalMass

end OAI
