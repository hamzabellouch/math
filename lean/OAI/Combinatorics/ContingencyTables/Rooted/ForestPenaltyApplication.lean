import OAI.Combinatorics.ContingencyTables.Rooted.ForestPhysicalCompletion
import OAI.Combinatorics.ContingencyTables.Transport.EqualitySoftening
import OAI.Combinatorics.ContingencyTables.Transport.RowColumnPenalties

namespace OAI

/-!
# Literal companion row/column and unary tree penalties

The physical row view is ell+x; the physical column view is ell+M-y.
The line groups are the disjoint original row and column coordinates.
Roots are the actual chosen component roots of the large-cell forest.
Only the false (row) coordinate of each tree cell carries its interval
penalty. Thus the concrete exact factor family is precisely the source's
nonroot indicator times its root/tree penalty weight.
-/

namespace ContingencyTables.ForestPenaltyApplication

open scoped BigOperators Classical Matrix
open SimpleGraph CommonBasesFPRAS
open EqualitySoftening ProductIntegerSignature ScalarPenalty
open ForestCapacity GraphIntegralCompletion RowColumnPenalties

variable {I J : Type*} [Fintype I] [Fintype J]

noncomputable def physicalRow (ell : I → J → ℤ) (z : ((I×J)×Bool) → ℕ) (i : I) (j : J) : ℝ :=
  (ell i j:ℝ)+z ((i,j),false)

noncomputable def physicalColumn (ell : I → J → ℤ) (M : I → J → ℕ)
    (z : ((I×J)×Bool) → ℕ) (i : I) (j : J) : ℝ :=
  (ell i j:ℝ)+M i j-z ((i,j),true)

noncomputable def lineOffset (ell : I → J → ℤ) (M : I → J → ℕ)
    (r : I → ℤ) (c : J → ℤ) : I⊕J → ℝ :=
  Sum.elim (fun i => (∑ j, (ell i j:ℝ))-r i)
    (fun j => (∑ i, ((ell i j:ℝ)+M i j))-c j)

noncomputable def deviation (ell : I → J → ℤ) (M : I → J → ℕ)
    (r : I → ℤ) (c : J → ℤ) (z : ((I×J)×Bool) → ℕ) : I⊕J → ℝ :=
  Sum.elim (fun i => (∑ j, physicalRow ell z i j)-r i)
    (fun j => (∑ i, physicalColumn ell M z i j)-c j)

lemma line_affine (ell : I → J → ℤ) (M : I → J → ℕ) (r : I → ℤ) (c : J → ℤ)
    (z : ((I×J)×Bool) → ℕ) (g : I⊕J) :
    lineOffset ell M r c g+(lineTotal cellLine z g:ℝ)*viewSlope (I := I) (J := J) g=
      deviation ell M r c z g := by
  cases g with
  | inl i =>
    rw [lineTotal_row]
    simp only [lineOffset,deviation,Sum.elim_inl,viewSlope,mul_one,physicalRow,rowView]
    push_cast
    rw [Finset.sum_add_distrib]
    ring
  | inr j =>
    rw [lineTotal_column]
    simp only [lineOffset,deviation,Sum.elim_inr,viewSlope,mul_neg_one,physicalColumn]
    push_cast
    rw [Finset.sum_sub_distrib]
    ring

noncomputable def rootFlag (T : SimpleGraph (I⊕J)) (v : I⊕J) : Bool :=
  decide (v=componentRoot T v)

noncomputable def unaryRate (T : SimpleGraph (I⊕J)) (b : I → J → ℕ)
    (alpha : ℝ) (a : (I×J)×Bool) : ℝ :=
  if a.2=false ∧ T.Adj (.inl a.1.1) (.inr a.1.2) then alpha/b a.1.1 a.1.2 else 0

noncomputable def unaryEll (ell : I → J → ℤ) (a : (I×J)×Bool) : ℝ := ell a.1.1 a.1.2

def unarySlope (_ : (I×J)×Bool) : ℝ := 1

noncomputable def unaryCap (b : I → J → ℕ) (a : (I×J)×Bool) : ℝ := b a.1.1 a.1.2

noncomputable def rootPenalty (T : SimpleGraph (I⊕J)) (ell : I → J → ℤ) (M : I → J → ℕ)
    (r : I → ℤ) (c : J → ℤ) (z : ((I×J)×Bool) → ℕ) : ℝ :=
  ∑ g, if rootFlag T g then |deviation ell M r c z g| else 0

noncomputable def treePenalty (T : SimpleGraph (I⊕J)) (b : I → J → ℕ)
    (ell : I → J → ℤ) (z : ((I×J)×Bool) → ℕ) : ℝ :=
  ∑ i, ∑ j, if T.Adj (.inl i) (.inr j) then
    affineDistance (ell i j) 1 (b i j) (z ((i,j),false))/(b i j:ℝ) else 0

noncomputable def penalty (T : SimpleGraph (I⊕J)) (b : I → J → ℕ) (ell : I → J → ℤ)
    (M : I → J → ℕ) (r : I → ℤ) (c : J → ℤ) (z : ((I×J)×Bool) → ℕ) : ℝ :=
  rootPenalty T ell M r c z+treePenalty T b ell z

noncomputable def physicalWeight (T : SimpleGraph (I⊕J)) (b : I → J → ℕ) (ell : I → J → ℤ)
    (M : I → J → ℕ) (r : I → ℤ) (c : J → ℤ) (alpha : ℝ) :
    (((I×J)×Bool) → ℕ) → ℝ :=
  exactWeight cellLine (rootFlag T) (fun _ => alpha) (lineOffset ell M r c) viewSlope
    (unaryRate T b alpha) (unaryEll ell) unarySlope (unaryCap b)

private lemma line_product_eq (T : SimpleGraph (I⊕J)) (ell : I → J → ℤ)
    (M : I → J → ℕ) (r : I → ℤ) (c : J → ℤ) (alpha : ℝ)
    (z : ((I×J)×Bool) → ℕ)
    (h : ∀ g, rootFlag T g=false → deviation ell M r c z g=0) :
    (∏ g, exactLineFactor (rootFlag T) (fun _ => alpha) (lineOffset ell M r c)
      viewSlope g (lineTotal cellLine z g))=(2:ℝ)^(-alpha*rootPenalty T ell M r c z) := by
  have hp : ∀ g, exactLineFactor (rootFlag T) (fun _ => alpha) (lineOffset ell M r c)
      viewSlope g (lineTotal cellLine z g)=
      (2:ℝ)^(-alpha*(if rootFlag T g then |deviation ell M r c z g| else 0)) := by
    intro g
    simp only [exactLineFactor,factor,line_affine]
    cases hg : rootFlag T g
    · simp [h g hg]
    · simp
  simp_rw [hp]
  rw [← Real.rpow_sum_of_pos (by norm_num : (0:ℝ)<2)]
  congr 1
  simp only [rootPenalty,Finset.mul_sum]

private lemma unary_product_eq (T : SimpleGraph (I⊕J)) (b : I → J → ℕ)
    (ell : I → J → ℤ) (alpha : ℝ) (z : ((I×J)×Bool) → ℕ) :
    (∏ a, unaryFactor (unaryRate T b alpha) (unaryEll ell) unarySlope (unaryCap b) a (z a))=
      (2:ℝ)^(-alpha*treePenalty T b ell z) := by
  unfold unaryFactor factor
  rw [← Real.rpow_sum_of_pos (by norm_num : (0:ℝ)<2)]
  congr 1
  rw [Fintype.sum_prod_type]
  simp only [unaryRate,unaryEll,unarySlope,unaryCap,Fintype.sum_bool,Bool.true_eq_false,
    false_and,ite_false,zero_mul,neg_zero,zero_add,true_and]
  rw [Fintype.sum_prod_type]
  simp only [treePenalty,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> simp only [div_eq_mul_inv,mul_zero] <;> ring

/-- This is the companion's literal root/tree exponential weight with
exact nonroot margin indicators, in the actual row/column coordinates. -/
theorem exact_eq (T : SimpleGraph (I⊕J)) (b : I → J → ℕ) (ell : I → J → ℤ)
    (M : I → J → ℕ) (r : I → ℤ) (c : J → ℤ) (alpha : ℝ) (z : ((I×J)×Bool) → ℕ) :
    physicalWeight T b ell M r c alpha z=
      if (∀ g, rootFlag T g=false → deviation ell M r c z g=0)
      then (2:ℝ)^(-alpha*penalty T b ell M r c z) else 0 := by
  by_cases h : ∀ g, rootFlag T g=false → deviation ell M r c z g=0
  · rw [ite_eq_left h]
    unfold physicalWeight exactWeight productWeight penalty
    rw [line_product_eq T ell M r c alpha z h,unary_product_eq,
      ← Real.rpow_add (by norm_num : (0:ℝ)<2)]
    congr 1
    ring
  · rw [ite_eq_right h]
    push Not at h
    obtain ⟨g,hg,hdev⟩ := h
    have hzero : exactLineFactor (rootFlag T) (fun _ => alpha) (lineOffset ell M r c)
        viewSlope g (lineTotal cellLine z g)=0 := by
      simp [exactLineFactor,hg,line_affine,hdev]
    unfold physicalWeight exactWeight productWeight
    rw [Finset.prod_eq_zero (Finset.mem_univ g) hzero,zero_mul]

theorem physicalWeight_nonnegative (T : SimpleGraph (I⊕J)) (b : I → J → ℕ)
    (ell : I → J → ℤ) (M : I → J → ℕ) (r : I → ℤ) (c : J → ℤ)
    (alpha : ℝ) (z : ((I×J)×Bool) → ℕ) : 0≤physicalWeight T b ell M r c alpha z := by
  rw [exact_eq]
  split_ifs
  · exact (Real.rpow_pos_of_pos (by norm_num : (0:ℝ)<2) _).le
  · exact le_refl 0

/-- The concrete unsummed factor family has the required raw removal
signature; its line and unary roles have all been physically instantiated. -/
theorem exact_removal (T : SimpleGraph (I⊕J)) (b : I → J → ℕ) (ell : I → J → ℤ)
    (M : I → J → ℕ) (r : I → ℤ) (c : J → ℤ) (alpha : ℝ) (ha : 0≤alpha)
    (z : ((I×J)×Bool) → ℕ) :
    OnePositiveDirection
      (FactorialSignatures.integerRemovalMatrix (physicalWeight T b ell M r c alpha) z).toBilin' := by
  have hu : ∀ a : (I×J)×Bool, 0≤unaryRate T b alpha a := by
    intro a
    unfold unaryRate
    split_ifs
    · exact div_nonneg ha (Nat.cast_nonneg _)
    · exact le_refl 0
  have hs := exactWeight_removal (C := (I×J)×Bool) (G := I⊕J)
    cellLine (rootFlag T) (fun _ => alpha) (lineOffset ell M r c)
    viewSlope (unaryRate T b alpha) (unaryEll ell) unarySlope (unaryCap b)
    (fun _ => ha) hu z
  convert hs using 1
  congr 2 <;> exact Subsingleton.elim _ _

end ContingencyTables.ForestPenaltyApplication

end OAI
