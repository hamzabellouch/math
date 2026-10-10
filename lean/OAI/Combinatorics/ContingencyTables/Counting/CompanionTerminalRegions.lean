import OAI.Combinatorics.ContingencyTables.Counting.CompanionPhysicalTables
import OAI.Combinatorics.ContingencyTables.Counting.CompanionNearMass

namespace OAI

/-! # Literal infeasible physical profiles lie in the terminal far or near regions -/

namespace ContingencyTables.CompanionTerminalRegions

open scoped BigOperators Classical
open CompanionFactorialApplication CompanionPhysicalTables CompanionFarMass
open CompanionNearMass ForestPenaltyApplication TreeMarginalSignature BalancedCellFibres
open EqualitySoftening

variable {I J : Type*} [Fintype I] [Fintype J]

lemma physicalRow_eq_table (A : Instance I J) (a : Profiles (cellWidth A)) (i : I) (j : J) :
    physicalRow (ForestLiteralCount.lower A.T A.d A.b)
      (BalancedCellFibres.profile (cellWidth A) a) i j=(physicalTable A a i j:ℝ) := by
  simp only [physicalRow,BalancedCellFibres.profile,Bool.false_eq_true,ite_false,physicalTable,
    Int.cast_add,Int.cast_natCast]

lemma physicalColumn_eq_table (A : Instance I J) (a : Profiles (cellWidth A)) (i : I) (j : J) :
    physicalColumn (ForestLiteralCount.lower A.T A.d A.b) (ForestLiteralCount.width A.T A.d A.b)
      (BalancedCellFibres.profile (cellWidth A) a) i j=(physicalTable A a i j:ℝ) := by
  have hk : (a (i,j)).val ≤ cellWidth A (i,j) := Nat.le_of_lt_succ (a (i,j)).isLt
  simp only [physicalColumn,BalancedCellFibres.profile,ite_true,Nat.cast_sub hk]
  change (ForestLiteralCount.lower A.T A.d A.b i j:ℝ)+(cellWidth A (i,j):ℝ)-
    ((cellWidth A (i,j):ℝ)-((a (i,j)).val:ℝ))=(physicalTable A a i j:ℝ)
  simp only [physicalTable,Int.cast_add,Int.cast_natCast]
  ring

noncomputable def integerDeviation (A : Instance I J) (a : Profiles (cellWidth A)) : I⊕J → ℤ :=
  Sum.elim (fun i => (∑ j,physicalTable A a i j)-A.r i)
    (fun j => (∑ i,physicalTable A a i j)-A.c j)

lemma deviation_eq_integer (A : Instance I J) (a : Profiles (cellWidth A)) (v : I⊕J) :
    deviation (ForestLiteralCount.lower A.T A.d A.b) (ForestLiteralCount.width A.T A.d A.b)
      A.r A.c (BalancedCellFibres.profile (cellWidth A) a) v=(integerDeviation A a v:ℝ) := by
  cases v with
  | inl i =>
    simp only [deviation,integerDeviation,Sum.elim_inl]
    simp_rw [physicalRow_eq_table]
    push_cast
    rfl
  | inr j =>
    simp only [deviation,integerDeviation,Sum.elim_inr]
    simp_rw [physicalColumn_eq_table]
    push_cast
    rfl

lemma nonTree_bounded (A : Instance I J) (a : Profiles (cellWidth A)) (i : I) (j : J)
    (ht : ¬A.T.Adj (.inl i) (.inr j)) :
    0 ≤ physicalTable A a i j ∧ physicalTable A a i j ≤ A.b i j := by
  have hk : (a (i,j)).val ≤ cellWidth A (i,j) := Nat.le_of_lt_succ (a (i,j)).isLt
  simp only [cellWidth,ForestLiteralCount.width,ht,ite_false] at hk
  simp only [physicalTable,ForestLiteralCount.lower,ht,ite_false,zero_add]
  exact ⟨Nat.cast_nonneg _,by exact_mod_cast hk⟩

lemma treePenalty_nonnegative (A : Instance I J) (a : Profiles (cellWidth A)) :
    0 ≤ treePenalty A.T A.b (ForestLiteralCount.lower A.T A.d A.b)
      (BalancedCellFibres.profile (cellWidth A) a) := by
  unfold treePenalty
  apply Finset.sum_nonneg
  intro i _
  apply Finset.sum_nonneg
  intro j _
  split_ifs
  · exact div_nonneg (le_max_left _ _) (Nat.cast_nonneg _)
  · exact le_rfl

lemma rootPenalty_nonnegative (A : Instance I J) (a : Profiles (cellWidth A)) :
    0 ≤ rootPenalty A.T (ForestLiteralCount.lower A.T A.d A.b)
      (ForestLiteralCount.width A.T A.d A.b) A.r A.c (BalancedCellFibres.profile (cellWidth A) a) := by
  unfold rootPenalty
  apply Finset.sum_nonneg
  intro v _
  split_ifs <;> first | exact abs_nonneg _ | exact le_rfl

lemma root_deviation_le_penalty (A : Instance I J) (a : Profiles (cellWidth A)) (v : I⊕J)
    (hv : rootFlag A.T v=true) : |(integerDeviation A a v:ℝ)| ≤ actualPenalty A a := by
  have hh := Finset.single_le_sum
    (f := fun g => if rootFlag A.T g then
      |deviation (ForestLiteralCount.lower A.T A.d A.b) (ForestLiteralCount.width A.T A.d A.b)
        A.r A.c (BalancedCellFibres.profile (cellWidth A) a) g| else 0)
    (fun g _ => by split_ifs <;> first | exact abs_nonneg _ | exact le_rfl)
    (Finset.mem_univ v)
  simp only [hv,ite_true,deviation_eq_integer] at hh
  exact hh.trans (by
    unfold actualPenalty penalty rootPenalty
    simp_rw [deviation_eq_integer]
    linarith [treePenalty_nonnegative A a])

lemma tree_distance_le_penalty (A : Instance I J) (a : Profiles (cellWidth A)) (t : I×J)
    (ht : A.T.Adj (.inl t.1) (.inr t.2)) :
    max 0 (max (-(physicalTable A a t.1 t.2:ℝ))
      ((physicalTable A a t.1 t.2:ℝ)-A.b t.1 t.2))/(A.b t.1 t.2:ℝ) ≤ actualPenalty A a := by
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
    unfold actualPenalty penalty
    linarith [rootPenalty_nonnegative A a])

/-- Positive mass and penalty below one force every literal margin to
hold: nonroots are exact indicators and root discrepancies are integral. -/
lemma margins_of_small_penalty (A : Instance I J) (alpha : ℝ)
    (a : Profiles (cellWidth A)) (hw : 0 < actualWeight A alpha a)
    (hp : actualPenalty A a < 1) :
    (∀ i,(∑ j,physicalTable A a i j)=A.r i) ∧
      (∀ j,(∑ i,physicalTable A a i j)=A.c j) := by
  have hnonroot : ∀ v,rootFlag A.T v=false → integerDeviation A a v=0 := by
    have hh := hw
    unfold actualWeight at hh
    rw [exact_eq] at hh
    split_ifs at hh with h
    · intro v hv
      have hz := h v hv
      rw [deviation_eq_integer] at hz
      exact_mod_cast hz
    · exact False.elim (lt_irrefl 0 hh)
  have hall (v : I⊕J) : integerDeviation A a v=0 := by
    cases hv : rootFlag A.T v
    · exact hnonroot v hv
    · have hh := (root_deviation_le_penalty A a v hv).trans_lt hp
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

theorem infeasible_in_far_or_near (A : Instance I J) (alpha gamma : ℝ) (K : ℕ)
    (ha : 0 < alpha) (hg1 : gamma ≤ 1) (hscale : 4*(K:ℝ) ≤ alpha*gamma)
    (a : Profiles (cellWidth A)) (hw : 0 < actualWeight A alpha a) (hbad : ¬Feasible A a) :
    4*(K:ℝ) ≤ alpha*actualPenalty A a ∨
      ∃ t : I×J,A.T.Adj (.inl t.1) (.inr t.2) ∧ a t ∈ cellPositions A t gamma := by
  by_cases hfar : 4*(K:ℝ) ≤ alpha*actualPenalty A a
  · exact Or.inl hfar
  right
  have hp : actualPenalty A a < gamma := by
    have hh : alpha*actualPenalty A a < alpha*gamma := (lt_of_not_ge hfar).trans_le hscale
    exact lt_of_mul_lt_mul_left hh ha.le
  have hm := margins_of_small_penalty A alpha a hw (hp.trans_le hg1)
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
  have hd := (tree_distance_le_penalty A a (i,j) ht).trans_lt hp
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

end ContingencyTables.CompanionTerminalRegions

end OAI
