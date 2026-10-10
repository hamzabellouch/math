import OAI.Combinatorics.ContingencyTables.Counting.CompanionTerminalRegions
import OAI.Combinatorics.ContingencyTables.Transport.TerminalMassCover

namespace OAI

/-! # The actual terminal companion normalizer approximates the table count -/

namespace ContingencyTables.CompanionTerminalMass

open scoped BigOperators Classical
open CompanionFactorialApplication CompanionPhysicalTables CompanionPhysicalNormalizer
open CompanionFarMass CompanionNearMass CompanionTerminalRegions BalancedCellFibres TreeMarginalSignature

variable {I J : Type*} [Fintype I] [Fintype J]

abbrev TreeCell (A : Instance I J) := {t : I×J // A.T.Adj (.inl t.1) (.inr t.2)}

/-- These are the actual attained minima and maxima after the paper's
integer bound-tightening step. They are feasible tables, not marginal
mass or signature assumptions. -/
structure Endpoints (A : Instance I J) where
  lowerTable : TreeCell A → I → J → ℤ
  upperTable : TreeCell A → I → J → ℤ
  lowerBounds : ∀ t i j,0 ≤ lowerTable t i j ∧ lowerTable t i j ≤ A.b i j
  upperBounds : ∀ t i j,0 ≤ upperTable t i j ∧ upperTable t i j ≤ A.b i j
  lowerRows : ∀ t i,(∑ j,lowerTable t i j)=A.r i
  lowerColumns : ∀ t j,(∑ i,lowerTable t i j)=A.c j
  upperRows : ∀ t i,(∑ j,upperTable t i j)=A.r i
  upperColumns : ∀ t j,(∑ i,upperTable t i j)=A.c j
  lowerAttains : ∀ t,lowerTable t t.val.1 t.val.2=0
  upperAttains : ∀ t,upperTable t t.val.1 t.val.2=(A.b t.val.1 t.val.2:ℤ)

noncomputable def tableCount (A : Instance I J) : ℝ :=
  Fintype.card (BoundedTable (fun i => (A.r i).toNat) (fun j => (A.c j).toNat) A.b)

lemma tableCount_ge_one (A : Instance I J) : 1 ≤ tableCount A := by
  have ha : Feasible A (tableAssignment A A.X A.hX) := by
    unfold Feasible
    rw [physicalTable_assignment]
    exact ⟨A.hX,A.hXr,A.hXc⟩
  have hpos : 0 < Fintype.card (PhysicalTables A) :=
    Fintype.card_pos_iff.mpr ⟨⟨tableAssignment A A.X A.hX,ha⟩⟩
  have hh : 1 ≤ Fintype.card (PhysicalTables A) := hpos
  rw [cardinality_eq] at hh
  unfold tableCount
  exact_mod_cast hh

lemma treeCell_card_le (A : Instance I J) : Fintype.card (TreeCell A) ≤ A.d := by
  exact (Fintype.card_le_of_injective (fun t : TreeCell A => t.val) Subtype.val_injective).trans
    (by simpa only [Fintype.card_prod] using A.hcard)

/-- Actual endpoint tables and the proved scalar signature estimates
control the entire union of narrow tree violations. -/
lemma total_near_mass_le (A : Instance I J) (E : Endpoints A) (alpha gamma : ℝ)
    (ha : 0 ≤ alpha) (hg : 0 < gamma) (hW : 20*A.d ≤ A.W) (B K : ℕ)
    (hB : (∏ a : I×J,(A.b a.1 a.2+1)) ≤ 2^B) (hBK : 2*B ≤ K) (hK : 0 < K) :
    (∑ t : TreeCell A,nearMass A alpha t.val gamma) ≤
      (4*A.d*gamma*K:ℝ)*physicalMass A alpha := by
  have hM : 0 < physicalMass A alpha := by
    exact lt_of_lt_of_le (by norm_num : (0:ℝ)<1)
      ((tableCount_ge_one A).trans (table_count_le_mass A alpha))
  have hh (t : TreeCell A) : nearMass A alpha t.val gamma ≤
      (4*gamma*K:ℝ)*physicalMass A alpha := by
    apply (div_le_iff₀ hM).mp
    exact near_mass_bound A alpha gamma t.val t.property ha hg hW B K hB hBK hK
      (E.lowerTable t) (E.upperTable t) (E.lowerBounds t) (E.upperBounds t)
      (E.lowerRows t) (E.lowerColumns t) (E.upperRows t) (E.upperColumns t)
      (E.lowerAttains t) (E.upperAttains t)
  calc
    _ ≤ ∑ _t : TreeCell A,(4*gamma*K:ℝ)*physicalMass A alpha :=
      Finset.sum_le_sum (fun t _ => hh t)
    _ = (Fintype.card (TreeCell A):ℝ)*((4*gamma*K:ℝ)*physicalMass A alpha) := by simp
    _ ≤ (A.d:ℝ)*((4*gamma*K:ℝ)*physicalMass A alpha) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast treeCell_card_le A) (by positivity)
    _ = _ := by ring

lemma feasible_sum_eq_tableCount (A : Instance I J) :
    (∑ a : Profiles (cellWidth A),if Feasible A a then (1:ℝ) else 0)=tableCount A := by
  have hh : (∑ a : Profiles (cellWidth A),if Feasible A a then (1:ℝ) else 0)=
      (Fintype.card (PhysicalTables A):ℝ) := by simp [PhysicalTables,Fintype.card_subtype]
  rw [hh,cardinality_eq]
  rfl

lemma mass_le_table_far_near (A : Instance I J) (alpha gamma : ℝ) (K : ℕ)
    (ha : 0 < alpha) (hg1 : gamma ≤ 1) (hscale : 4*(K:ℝ) ≤ alpha*gamma) :
    physicalMass A alpha ≤ tableCount A+
      (∑ a : Profiles (cellWidth A),if 4*(K:ℝ) ≤ alpha*actualPenalty A a
        then actualWeight A alpha a else 0)+
      ∑ t : TreeCell A,nearMass A alpha t.val gamma := by
  have hh := TerminalMassCover.mass_le_cover (actualWeight A alpha) (Feasible A)
    (fun a => 4*(K:ℝ) ≤ alpha*actualPenalty A a)
    (fun t : TreeCell A => fun a => a t.val ∈ cellPositions A t.val gamma)
    (fun a => ForestPenaltyApplication.physicalWeight_nonnegative _ _ _ _ _ _ _ _)
    (fun a ha => feasible_weight_one A alpha a ha)
    (by
      intro a hw hbad
      rcases infeasible_in_far_or_near A alpha gamma K ha hg1 hscale a hw hbad with hf|⟨t,ht,hn⟩
      · exact Or.inl hf
      · exact Or.inr ⟨⟨t,ht⟩,hn⟩)
  change physicalMass A alpha ≤ _ at hh
  rw [feasible_sum_eq_tableCount] at hh
  apply hh.trans_eq
  congr 1
  apply Finset.sum_congr rfl
  intro t _
  unfold nearMass
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : a t.val∈cellPositions A t.val gamma <;> simp only [ha,ite_true,ite_false]

/-- This is the literal terminal normalizer estimate. The finite table
bijection, root integrality, far bound and actual tree-marginal estimates
are all proved. Arithmetic conditions below are discharged by the
manuscript's explicit choices of K, gamma and the final coefficient. -/
theorem terminal_count_estimate (A : Instance I J) (E : Endpoints A)
    (alpha gamma epsilon : ℝ) (B K : ℕ)
    (ha : 0 < alpha) (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    (he : 0 < epsilon) (he1 : epsilon < 1)
    (hscale : 4*(K:ℝ) ≤ alpha*gamma) (hnear : 4*(A.d:ℝ)*gamma*K ≤ epsilon/128)
    (hfar : (2:ℝ)^(-(3*K:ℕ):ℝ) ≤ epsilon/128)
    (hW : 20*A.d ≤ A.W) (hB : (∏ a : I×J,(A.b a.1 a.2+1)) ≤ 2^B)
    (hBK : 2*B ≤ K) (hK : 0 < K) :
    tableCount A ≤ CommonBasesFPRAS.slotTotal TwoLiftStates.pairs (f A alpha) ∅ ∧
      CommonBasesFPRAS.slotTotal TwoLiftStates.pairs (f A alpha) ∅ ≤ (1+epsilon/32)*tableCount A := by
  rw [normalizer_eq_physical_mass]
  have hZM : tableCount A ≤ physicalMass A alpha := table_count_le_mass A alpha
  have hM1 := (tableCount_ge_one A).trans hZM
  have hM : 0 ≤ physicalMass A alpha := by linarith
  have hcover := mass_le_table_far_near A alpha gamma K ha hg1 hscale
  have hfarMass := (far_mass_le A alpha B K hW hB hBK).trans hfar
  have hfarScaled : (∑ a : Profiles (cellWidth A),if 4*(K:ℝ) ≤ alpha*actualPenalty A a
      then actualWeight A alpha a else 0) ≤ (epsilon/128)*physicalMass A alpha := by
    exact hfarMass.trans (by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hM1
        (show 0 ≤ epsilon/128 by positivity))
  have hnearMass := total_near_mass_le A E alpha gamma ha.le hg hW B K hB hBK hK
  have hnearScaled : (∑ t : TreeCell A,nearMass A alpha t.val gamma) ≤
      (epsilon/128)*physicalMass A alpha :=
    hnearMass.trans (mul_le_mul_of_nonneg_right hnear hM)
  have hbad : physicalMass A alpha ≤ tableCount A+(epsilon/64)*physicalMass A alpha := by
    linarith
  exact TerminalMassCover.relative_count_bound (tableCount A) (physicalMass A alpha) epsilon
    (by linarith [tableCount_ge_one A]) he he1 hZM hbad

end ContingencyTables.CompanionTerminalMass

end OAI
