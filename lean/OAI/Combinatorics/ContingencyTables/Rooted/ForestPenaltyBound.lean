import OAI.Combinatorics.ContingencyTables.Counting.CompanionFactorialApplication
import OAI.Combinatorics.ContingencyTables.Rooted.ForestRootPenalty

namespace OAI

/-! # The literal companion completion penalty is bounded by H/A -/

namespace ContingencyTables.ForestPenaltyBound

open scoped BigOperators Classical
open SimpleGraph CompanionFactorialApplication ForestCountIdentification
open ForestAssignmentSplit ForestPhysicalCompletion ForestLiteralCount ForestRootPenalty
open BalancedBox

variable {I J : Type*} [Fintype I] [Fintype J]

noncomputable def penalty (A : Instance I J) (z : View A → ℕ) (f : FreeIndex A.small A.T A.b) : ℝ :=
  actualPenalty A.small A.T A.b (smallX A.small z) (smallY A.small z)
    (freeTable A.small A.T A.b f) A.r A.c
    (solved A.small A.T A.r A.c (fun i j => (smallX A.small z i j:ℤ))
      (fun i j => ((A.b i j-smallY A.small z i j:ℕ):ℤ))
      (fun i j => (freeTable A.small A.T A.b f i j:ℤ)))

theorem penalty_bound (A : Instance I J) (z : View A → ℕ) (hz : InBox (bounds A) z)
    (f : FreeIndex A.small A.T A.b) :
    0≤penalty A z f ∧ penalty A z f≤10*(A.d:ℝ)^2*((A.W:ℝ)+1) := by
  let x := smallX A.small z
  let y := smallY A.small z
  let free := freeTable A.small A.T A.b f
  let tree := solved A.small A.T A.r A.c (fun i j => (x i j:ℤ))
    (fun i j => ((A.b i j-y i j:ℕ):ℤ)) (fun i j => (free i j:ℤ))
  have hx : ∀ i j, A.small i j=true → x i j≤A.b i j := by
    intro i j hs
    simpa only [x,smallX,hs,dite_eq_left,bounds] using hz (⟨(i,j),hs⟩,false)
  have hroot := root_eq_large A.small A.b A.T A.hTG A.hT A.hmax
    (fun i j hs => (A.hlarge i j hs).2)
  have hR := rootPenalty_le A.small A.T A.hTG A.b x y free A.r A.c A.X
    A.hXr A.hXc hroot hx A.hX
  have hsmallSum : (∑ i, ∑ j, if A.small i j then (A.b i j:ℝ) else 0)≤
      (A.d:ℝ)*A.W := by
    calc
      _ ≤ ∑ _i : I, ∑ _j : J, (A.W:ℝ) := by
        apply Finset.sum_le_sum
        intro i _
        apply Finset.sum_le_sum
        intro j _
        by_cases hs : A.small i j=true
        · simp only [hs,ite_true]
          exact_mod_cast (A.hsmall i j hs).le
        · have hs' : A.small i j=false := Bool.eq_false_iff.mpr hs
          simp [hs']
      _ = (Fintype.card I*Fintype.card J:ℕ)*(A.W:ℝ) := by simp; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast A.hcard) (Nat.cast_nonneg _)
  have hinterval := solved_in_intervals A.small A.b A.T A.hTG A.hT A.hmax A.r A.c
    (fun i j => (x i j:ℤ)) (fun i j => ((A.b i j-y i j:ℕ):ℤ))
    (fun i j => (free i j:ℤ)) A.X A.d A.W A.hd A.hcard A.hlarge
    (by
      intro i j hs
      refine ⟨A.hsmall i j hs,⟨by positivity,by exact_mod_cast hx i j hs⟩,
        ⟨by positivity,by exact_mod_cast Nat.sub_le (A.b i j) (y i j)⟩⟩)
    (by
      intro i j hs ht
      exact ⟨by positivity,by exact_mod_cast freeTable_bound A.small A.T A.b f i j hs ht⟩)
    A.hX A.hXr A.hXc
  have hterm (i : I) (j : J) :
      0≤(if A.T.Adj (.inl i) (.inr j) then
        max 0 (max (-(tree i j:ℝ)) ((tree i j:ℝ)-A.b i j))/(A.b i j:ℝ) else 0) ∧
      (if A.T.Adj (.inl i) (.inr j) then
        max 0 (max (-(tree i j:ℝ)) ((tree i j:ℝ)-A.b i j))/(A.b i j:ℝ) else 0)≤10*(A.d:ℝ) := by
    by_cases ht : A.T.Adj (.inl i) (.inr j)
    · simp only [ht,ite_true]
      have hb : (0:ℝ)<A.b i j := by exact_mod_cast (A.hlarge i j (A.hTG ht)).2
      have hlo : -(10*(A.d:ℝ)*(A.b i j:ℝ))≤(tree i j:ℝ) := by
        exact_mod_cast (hinterval i j ht).1
      have hup : (tree i j:ℝ)≤10*(A.d:ℝ)*(A.b i j:ℝ) := by
        exact_mod_cast (hinterval i j ht).2
      refine ⟨div_nonneg (le_max_left _ _) hb.le,?_⟩
      rw [div_le_iff₀ hb]
      apply max_le
      · positivity
      · apply max_le <;> linarith
    · simp [ht]
  have htree0 := Finset.sum_nonneg (s := Finset.univ) (fun i _ =>
    Finset.sum_nonneg (s := Finset.univ) (fun j _ => (hterm i j).1))
  have htree := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    Finset.sum_le_sum (s := Finset.univ) (fun j _ => (hterm i j).2))
  have hcardR : (Fintype.card I*Fintype.card J:ℕ)≤(A.d:ℝ) := by exact_mod_cast A.hcard
  have hdR : (1:ℝ)≤A.d := by exact_mod_cast A.hd
  have hW : (0:ℝ)≤A.W := Nat.cast_nonneg _
  have htree' : (∑ i, ∑ j, if A.T.Adj (.inl i) (.inr j) then
      max 0 (max (-(tree i j:ℝ)) ((tree i j:ℝ)-A.b i j))/(A.b i j:ℝ) else 0)≤10*(A.d:ℝ)^2 := by
    calc
      _ ≤ (Fintype.card I*Fintype.card J:ℕ)*(10*(A.d:ℝ)) := by simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.cast_mul,mul_assoc] using htree
      _ ≤ (A.d:ℝ)*(10*(A.d:ℝ)) := mul_le_mul_of_nonneg_right hcardR (by positivity)
      _ = _ := by ring
  change 0≤actualPenalty A.small A.T A.b x y free A.r A.c tree ∧
    actualPenalty A.small A.T A.b x y free A.r A.c tree≤_
  unfold actualPenalty
  constructor
  · apply add_nonneg _ htree0
    exact Finset.sum_nonneg (fun a _ => by split_ifs <;> positivity)
  · have hsquare : (A.d:ℝ)≤(A.d:ℝ)^2 := by nlinarith
    have hscale := mul_le_mul_of_nonneg_right hsquare hW
    have hprod : 0≤(A.d:ℝ)^2*(A.W:ℝ) := mul_nonneg (sq_nonneg _) hW
    nlinarith

end ContingencyTables.ForestPenaltyBound

end OAI
