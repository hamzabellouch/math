import OAI.Combinatorics.ContingencyTables.Rooted.RootedPhysicalTables
import OAI.Combinatorics.ContingencyTables.Rooted.RootedNearMass
import OAI.Combinatorics.ContingencyTables.Counting.CompanionTerminalRegions

namespace OAI

/-! # Selected-root infeasibility lies in the literal far or near region -/

namespace ContingencyTables.RootedTerminalRegions

open scoped BigOperators Classical
open CompanionFactorialApplication CompanionPhysicalTables RootedFarMass RootedNearMass
open ForestPenaltyApplication TreeMarginalSignature BalancedCellFibres EqualitySoftening
open CompanionTerminalRegions (integerDeviation deviation_eq_integer nonTree_bounded
  treePenalty_nonnegative physicalRow_eq_table)
open CompanionNearMass (cellPositions)

variable {I J : Type*} [Fintype I] [Fintype J]

lemma rootPenalty_nonnegative (A : Instance I J) (R : RootedCompletion.Selection A.T) (a : Profiles (cellWidth A)) :
    0 ≤ RootedPenalty.rootPenalty A R (BalancedCellFibres.profile (cellWidth A) a) := by
  unfold RootedPenalty.rootPenalty
  apply Finset.sum_nonneg
  intro v _
  split_ifs <;> first | exact abs_nonneg _ | exact le_rfl

lemma root_deviation_le_penalty (A : Instance I J) (R : RootedCompletion.Selection A.T) (a : Profiles (cellWidth A)) (v : I⊕J)
    (hv : RootedPenalty.rootFlag R v=true) : |(integerDeviation A a v:ℝ)| ≤ actualPenalty A R a := by
  have hh := Finset.single_le_sum
    (f := fun g => if RootedPenalty.rootFlag R g then
      |deviation (ForestLiteralCount.lower A.T A.d A.b) (ForestLiteralCount.width A.T A.d A.b)
        A.r A.c (BalancedCellFibres.profile (cellWidth A) a) g| else 0)
    (fun g _ => by split_ifs <;> first | exact abs_nonneg _ | exact le_rfl)
    (Finset.mem_univ v)
  simp only [hv,ite_true,deviation_eq_integer] at hh
  exact hh.trans (by
    unfold actualPenalty RootedPenalty.penalty RootedPenalty.rootPenalty RootedPenalty.ell RootedPenalty.widths
    simp_rw [deviation_eq_integer]
    linarith [treePenalty_nonnegative A a])

lemma tree_distance_le_penalty (A : Instance I J) (R : RootedCompletion.Selection A.T) (a : Profiles (cellWidth A)) (t : I×J)
    (ht : A.T.Adj (.inl t.1) (.inr t.2)) :
    max 0 (max (-(physicalTable A a t.1 t.2:ℝ))
      ((physicalTable A a t.1 t.2:ℝ)-A.b t.1 t.2))/(A.b t.1 t.2:ℝ) ≤ actualPenalty A R a := by
  let z := BalancedCellFibres.profile (cellWidth A) a
  let D : I → J → ℝ := fun i j => if A.T.Adj (.inl i) (.inr j) then
    affineDistance (ForestLiteralCount.lower A.T A.d A.b i j) 1 (A.b i j) (z ((i,j),false)) /
      (A.b i j:ℝ) else 0
  have hD (i : I) (j : J) : 0 ≤ D i j := by
    dsimp only [D]
    split_ifs
    · exact div_nonneg (le_max_left _ _) (Nat.cast_nonneg _)
    · exact le_rfl
  have hinner := Finset.single_le_sum (fun j _ => hD t.1 j) (Finset.mem_univ t.2)
  have houter := Finset.single_le_sum
    (f := fun i => ∑ j,D i j)
    (fun i _ => Finset.sum_nonneg (fun j _ => hD i j)) (Finset.mem_univ t.1)
  have hh : D t.1 t.2 ≤ treePenalty A.T A.b (ForestLiteralCount.lower A.T A.d A.b) z :=
    hinner.trans houter
  dsimp only [D] at hh
  rw [ite_eq_left ht] at hh
  simp only [affineDistance,mul_one] at hh
  have hrow := physicalRow_eq_table A a t.1 t.2
  change (ForestLiteralCount.lower A.T A.d A.b t.1 t.2:ℝ)+(z ((t.1,t.2),false):ℝ)=_ at hrow
  rw [hrow] at hh
  exact hh.trans (by
    unfold actualPenalty RootedPenalty.penalty RootedPenalty.ell
    linarith [rootPenalty_nonnegative A R a])

/-- Positive mass and penalty below one force every literal margin to
hold: nonroots are exact indicators and root discrepancies are integral. -/
lemma margins_of_small_penalty (A : Instance I J) (R : RootedCompletion.Selection A.T) (alpha : ℝ)
    (a : Profiles (cellWidth A)) (hw : 0 < actualWeight A R alpha a)
    (hp : actualPenalty A R a < 1) :
    (∀ i,(∑ j,physicalTable A a i j)=A.r i) ∧
      (∀ j,(∑ i,physicalTable A a i j)=A.c j) := by
  have hnonroot : ∀ v,RootedPenalty.rootFlag R v=false → integerDeviation A a v=0 := by
    have hh := hw
    unfold actualWeight at hh
    rw [RootedPenalty.exact_eq] at hh
    by_cases h : ∀ g,RootedPenalty.rootFlag R g=false →
        deviation (RootedPenalty.ell A) (RootedPenalty.widths A)
          A.r A.c (BalancedCellFibres.profile (cellWidth A) a) g=0
    · intro v hv
      have hz := h v hv
      change deviation (ForestLiteralCount.lower A.T A.d A.b)
        (ForestLiteralCount.width A.T A.d A.b) A.r A.c
        (BalancedCellFibres.profile (cellWidth A) a) v=0 at hz
      rw [deviation_eq_integer] at hz
      exact_mod_cast hz
    · rw [ite_eq_right h] at hh
      exact False.elim ((lt_irrefl (0:ℝ)) hh)
  have hall (v : I⊕J) : integerDeviation A a v=0 := by
    cases hv : RootedPenalty.rootFlag R v
    · exact hnonroot v hv
    · have hh := (root_deviation_le_penalty A R a v hv).trans_lt hp
      have hz : |integerDeviation A a v| < (1:ℤ) := by exact_mod_cast hh
      have hz' := abs_lt.mp hz
      omega
  constructor
  · intro i
    have hh := hall (.inl i)
    simpa only [integerDeviation,Sum.elim_inl,sub_eq_zero] using hh
  · intro j
    have hh := hall (.inr j)
    simpa only [integerDeviation,Sum.elim_inr,sub_eq_zero] using hh

theorem infeasible_in_far_or_near (A : Instance I J) (R : RootedCompletion.Selection A.T) (alpha gamma : ℝ) (K : ℕ)
    (ha : 0 < alpha) (hg1 : gamma ≤ 1) (hscale : 4*(K:ℝ) ≤ alpha*gamma)
    (a : Profiles (cellWidth A)) (hw : 0 < actualWeight A R alpha a) (hbad : ¬Feasible A a) :
    4*(K:ℝ) ≤ alpha*actualPenalty A R a ∨
      ∃ t : I×J,A.T.Adj (.inl t.1) (.inr t.2) ∧ a t ∈ cellPositions A t gamma := by
  by_cases hfar : 4*(K:ℝ) ≤ alpha*actualPenalty A R a
  · exact Or.inl hfar
  right
  have hp : actualPenalty A R a < gamma := by
    have hh : alpha*actualPenalty A R a < alpha*gamma := (lt_of_not_ge hfar).trans_le hscale
    exact lt_of_mul_lt_mul_left hh ha.le
  have hm := margins_of_small_penalty A R alpha a hw (hp.trans_le hg1)
  have hcell : ¬∀ i j,0 ≤ physicalTable A a i j ∧ physicalTable A a i j ≤ A.b i j := by
    intro hc
    exact hbad ⟨hc,hm⟩
  obtain ⟨i,hi⟩ := not_forall.mp hcell
  obtain ⟨j,hviol⟩ := not_forall.mp hi
  have ht : A.T.Adj (.inl i) (.inr j) := by
    by_contra ht
    exact hviol (nonTree_bounded A a i j ht)
  refine ⟨(i,j),ht,?_⟩
  have hb : (0:ℝ) < A.b i j := by exact_mod_cast (A.hlarge i j (A.hTG ht)).2
  have hd := (tree_distance_le_penalty A R a (i,j) ht).trans_lt hp
  have hdist : max 0 (max (-(physicalTable A a i j:ℝ))
      ((physicalTable A a i j:ℝ)-A.b i j)) < gamma*A.b i j := (div_lt_iff₀ hb).mp hd
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _,?_⟩
  change ((physicalTable A a i j<0) ∧ -(physicalTable A a i j:ℝ)<gamma*A.b i j) ∨
    (((A.b i j:ℤ)<physicalTable A a i j) ∧ (physicalTable A a i j:ℝ)-A.b i j<gamma*A.b i j)
  by_cases hlo : 0 ≤ physicalTable A a i j
  · right
    refine ⟨lt_of_not_ge (fun hhi => hviol ⟨hlo,hhi⟩),?_⟩
    exact (le_max_right _ _).trans (le_max_right _ _) |>.trans_lt hdist
  · left
    exact ⟨lt_of_not_ge hlo,(le_max_left _ _).trans (le_max_right _ _) |>.trans_lt hdist⟩

end ContingencyTables.RootedTerminalRegions

end OAI
