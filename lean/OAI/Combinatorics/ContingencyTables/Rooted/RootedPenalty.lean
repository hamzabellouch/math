import OAI.Combinatorics.ContingencyTables.Rooted.RootedPhysicalCompletion
import OAI.Combinatorics.ContingencyTables.Rooted.ForestLiteralCount

namespace OAI

/-! # Physical factors with the executed component-root convention

The line factors use the explicitly selected roots. Their tree factors,
widths and doubled row/column coordinates are exactly the source data.
-/

namespace ContingencyTables.RootedPenalty

open scoped BigOperators Classical Matrix
open CommonBasesFPRAS CompanionFactorialApplication RootedCompletion
open ForestPenaltyApplication ForestLiteralCount EqualitySoftening
open ProductIntegerSignature RowColumnPenalties

variable {I J : Type*} [Fintype I] [Fintype J]

noncomputable def ell (A : Instance I J) : I → J → ℤ := lower A.T A.d A.b
noncomputable def widths (A : Instance I J) : I → J → ℕ := width A.T A.d A.b

noncomputable def rootFlag {T : SimpleGraph (I⊕J)} (S : Selection T) (v : I⊕J) : Bool :=
  decide (v=S.root v)

noncomputable def rootPenalty (A : Instance I J) (S : Selection A.T)
    (z : ((I×J)×Bool) → ℕ) : ℝ :=
  ∑ g,if rootFlag S g then |deviation (ell A) (widths A) A.r A.c z g| else 0

noncomputable def penalty (A : Instance I J) (S : Selection A.T)
    (z : ((I×J)×Bool) → ℕ) : ℝ :=
  rootPenalty A S z+treePenalty A.T A.b (ell A) z

noncomputable def physicalWeight (A : Instance I J) (S : Selection A.T) (alpha : ℝ) :
    (((I×J)×Bool) → ℕ) → ℝ :=
  exactWeight cellLine (rootFlag S) (fun _ => alpha)
    (lineOffset (ell A) (widths A) A.r A.c) viewSlope
    (unaryRate A.T A.b alpha) (unaryEll (ell A)) unarySlope (unaryCap A.b)

private lemma line_product_eq (A : Instance I J) (S : Selection A.T) (alpha : ℝ)
    (z : ((I×J)×Bool) → ℕ)
    (h : ∀ g,rootFlag S g=false → deviation (ell A) (widths A) A.r A.c z g=0) :
    (∏ g,exactLineFactor (rootFlag S) (fun _ => alpha)
      (lineOffset (ell A) (widths A) A.r A.c) viewSlope g (lineTotal cellLine z g))=
      (2:ℝ)^(-alpha*rootPenalty A S z) := by
  have hp : ∀ g,exactLineFactor (rootFlag S) (fun _ => alpha)
      (lineOffset (ell A) (widths A) A.r A.c) viewSlope g (lineTotal cellLine z g)=
      (2:ℝ)^(-alpha*(if rootFlag S g then
        |deviation (ell A) (widths A) A.r A.c z g| else 0)) := by
    intro g
    simp only [exactLineFactor,ScalarPenalty.factor,line_affine]
    cases hg : rootFlag S g
    · simp [h g hg]
    · simp
  simp_rw [hp]
  rw [←Real.rpow_sum_of_pos (by norm_num : (0:ℝ)<2)]
  congr 1
  simp only [rootPenalty,Finset.mul_sum]

private lemma unary_product_eq (A : Instance I J) (alpha : ℝ)
    (z : ((I×J)×Bool) → ℕ) :
    (∏ a,unaryFactor (unaryRate A.T A.b alpha) (unaryEll (ell A)) unarySlope
      (unaryCap A.b) a (z a))=(2:ℝ)^(-alpha*treePenalty A.T A.b (ell A) z) := by
  unfold unaryFactor ScalarPenalty.factor
  rw [←Real.rpow_sum_of_pos (by norm_num : (0:ℝ)<2)]
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

theorem exact_eq (A : Instance I J) (S : Selection A.T) (alpha : ℝ)
    (z : ((I×J)×Bool) → ℕ) :
    physicalWeight A S alpha z=
      if (∀ g,rootFlag S g=false → deviation (ell A) (widths A) A.r A.c z g=0)
      then (2:ℝ)^(-alpha*penalty A S z) else 0 := by
  by_cases h : ∀ g,rootFlag S g=false → deviation (ell A) (widths A) A.r A.c z g=0
  · rw [ite_eq_left h]
    unfold physicalWeight exactWeight productWeight penalty
    rw [line_product_eq A S alpha z h,unary_product_eq,
      ←Real.rpow_add (by norm_num : (0:ℝ)<2)]
    congr 1
    ring
  · rw [ite_eq_right h]
    push Not at h
    obtain ⟨g,hg,hdev⟩ := h
    have hz : exactLineFactor (rootFlag S) (fun _ => alpha)
        (lineOffset (ell A) (widths A) A.r A.c) viewSlope g (lineTotal cellLine z g)=0 := by
      simp [exactLineFactor,hg,line_affine,hdev]
    unfold physicalWeight exactWeight productWeight
    rw [Finset.prod_eq_zero (Finset.mem_univ g) hz,zero_mul]

theorem physicalWeight_nonnegative (A : Instance I J) (S : Selection A.T)
    (alpha : ℝ) (z : ((I×J)×Bool) → ℕ) : 0≤ physicalWeight A S alpha z := by
  rw [exact_eq]
  split_ifs
  · exact (Real.rpow_pos_of_pos (by norm_num : (0:ℝ)<2) _).le
  · exact le_rfl

theorem physicalWeight_removal (A : Instance I J) (S : Selection A.T)
    (alpha : ℝ) (ha : 0≤ alpha) (z : ((I×J)×Bool) → ℕ) :
    OnePositiveDirection
      (FactorialSignatures.integerRemovalMatrix (physicalWeight A S alpha) z).toBilin' := by
  have hu : ∀ a : (I×J)×Bool,0≤ unaryRate A.T A.b alpha a := by
    intro a
    unfold unaryRate
    split_ifs
    · exact div_nonneg ha (Nat.cast_nonneg _)
    · exact le_rfl
  have hs := exactWeight_removal cellLine (rootFlag S) (fun _ => alpha)
    (lineOffset (ell A) (widths A) A.r A.c) viewSlope
    (unaryRate A.T A.b alpha) (unaryEll (ell A)) unarySlope (unaryCap A.b)
    (fun _ => ha) hu z
  convert hs using 1
  congr 2 <;> exact Subsingleton.elim _ _

end ContingencyTables.RootedPenalty

end OAI
