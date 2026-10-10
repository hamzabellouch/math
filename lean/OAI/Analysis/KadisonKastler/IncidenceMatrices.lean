import OAI.Analysis.KadisonKastler.RectangularOperator
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Data.Fintype.Powerset

namespace OAI

/-!
# Incidence matrices in the free-word cuts

A matrix supported on a relation with row degree at most `R` and column
degree at most `C`, and contractive operator entries, has norm at most
`sqrt (R * C)`. The scalar correction in a preservation cut has precisely
this form.
-/

namespace KadisonKastler

open Finset

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {I J : Type*} [Fintype I] [Fintype J]

local instance incidenceOperatorOrder : PartialOrder (H →L[ℂ] H) :=
  CStarAlgebra.spectralOrder _
local instance incidenceOperatorStarOrder : StarOrderedRing (H →L[ℂ] H) :=
  CStarAlgebra.spectralOrderedRing _

/-- The row-column degree estimate, with the actual Hilbert-space matrix norm. -/
theorem norm_matrix_le_sqrt_degrees (T : CStarMatrix I J (H →L[ℂ] H))
    (E : I → J → Prop) [DecidableRel E] (R C : ℕ)
    (hzero : ∀ i j, ¬ E i j → T i j = 0)
    (hentry : ∀ i j, ‖T i j‖ ≤ 1)
    (hrow : ∀ i, #{j | E i j} ≤ R)
    (hcol : ∀ j, #{i | E i j} ≤ C) :
    ‖T‖ ≤ Real.sqrt ((R : ℝ) * C) := by
  classical
  rw [← norm_rectangularHilbertMatrix]
  apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
  intro x
  have happly (i : I) (j : J) : ‖T i j (x j)‖ ≤ ‖x j‖ := by
    calc
      _ ≤ ‖T i j‖ * ‖x j‖ := (T i j).le_opNorm (x j)
      _ ≤ 1 * ‖x j‖ := mul_le_mul_of_nonneg_right (hentry i j) (norm_nonneg (x j))
      _ = _ := one_mul _
  have heq (i : I) : (∑ j, T i j (x j)) = ∑ j ∈ univ.filter (E i), T i j (x j) := by
    apply (sum_subset (filter_subset _ _) ?_).symm
    intro j _ hj
    simp only [mem_filter, mem_univ, true_and] at hj
    simp [hzero i j hj]
  have hrows (i : I) : ‖∑ j, T i j (x j)‖ ^ 2 ≤
      (R : ℝ) * ∑ j ∈ univ.filter (E i), ‖x j‖ ^ 2 := by
    rw [heq]
    calc
      _ ≤ (∑ j ∈ univ.filter (E i), ‖T i j (x j)‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) _
      _ ≤ (#(univ.filter (E i)) : ℝ) *
          ∑ j ∈ univ.filter (E i), ‖T i j (x j)‖ ^ 2 :=
        sq_sum_le_card_mul_sum_sq
      _ ≤ (R : ℝ) * ∑ j ∈ univ.filter (E i), ‖x j‖ ^ 2 := by
        apply mul_le_mul
        · exact_mod_cast hrow i
        · exact sum_le_sum (fun j _ => pow_le_pow_left₀ (norm_nonneg _) (happly i j) _)
        · positivity
        · positivity
  have hsum : (∑ i, ∑ j ∈ univ.filter (E i), ‖x j‖ ^ 2) ≤
      (C : ℝ) * ∑ j, ‖x j‖ ^ 2 := by
    simp only [sum_filter]
    rw [sum_comm, mul_sum]
    apply sum_le_sum
    intro j _
    have he : (∑ i, if E i j then ‖x j‖ ^ 2 else 0) =
        (#(univ.filter (fun i => E i j)) : ℝ) * ‖x j‖ ^ 2 := by
      rw [← sum_filter]
      simp
    rw [he]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcol j) (sq_nonneg _)
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  rw [mul_pow, Real.sq_sqrt (by positivity), PiLp.norm_sq_eq_of_L2,
    PiLp.norm_sq_eq_of_L2]
  calc
    _ ≤ ∑ i, (R : ℝ) * ∑ j ∈ univ.filter (E i), ‖x j‖ ^ 2 :=
      sum_le_sum (fun i _ => by simpa only [rectangularHilbertMatrix_apply] using hrows i)
    _ = (R : ℝ) * (∑ i, ∑ j ∈ univ.filter (E i), ‖x j‖ ^ 2) := (mul_sum _ _ _).symm
    _ ≤ (R : ℝ) * ((C : ℝ) * ∑ j, ‖x j‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by ring

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The subset indices left after grouping the ordered labels of a cut. -/
abbrev WordSubset (W : Finset α) (p : ℕ) := {B : Finset α // B ⊆ W ∧ B.card = p}

theorem card_wordSubset (W : Finset α) (p : ℕ) :
    Fintype.card (WordSubset W p) = W.card.choose p := by
  rw [Fintype.card_of_subtype (W.powersetCard p) (fun _ => mem_powersetCard),
    card_powersetCard]

/-- Disjoint columns in one row are precisely the fixed-size subsets of
the complement of that row. -/
def disjointWordSubsetEquiv (W : Finset α) (A : Finset α) (p : ℕ) :
    {B : WordSubset W p // Disjoint A B.val} ≃ WordSubset (W \ A) p where
  toFun B := ⟨B.val.val, (subset_sdiff.mpr ⟨B.val.property.1, B.property.symm⟩),
    B.val.property.2⟩
  invFun B := ⟨⟨B.val, (subset_sdiff.mp B.property.1).1, B.property.2⟩,
    (subset_sdiff.mp B.property.1).2.symm⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem card_disjoint_wordSubsets (W : Finset α) (p q : ℕ)
    (hW : W.card = p + q + 1) (A : WordSubset W q) :
    #{B : WordSubset W p | Disjoint A.val B.val} = p + 1 := by
  rw [← Fintype.card_subtype, Fintype.card_congr
    (disjointWordSubsetEquiv W A.val p), card_wordSubset,
    card_sdiff_of_subset A.property.1, A.property.2, hW]
  have he : p + q + 1 - q = p + 1 := by omega
  rw [he, Nat.choose_succ_self_right]

/-- The scalar adjacency correction in a preservation cut. -/
theorem norm_preservation_adjacency_le (W : Finset α) (p q : ℕ)
    (hW : W.card = p + q + 1) :
    ‖(CStarMatrix.ofMatrix (fun (A : WordSubset W q) (B : WordSubset W p) =>
      if Disjoint A.val B.val then (1 : H →L[ℂ] H) else 0))‖ ≤
      Real.sqrt (((p + 1 : ℕ) : ℝ) * ((q + 1 : ℕ) : ℝ)) := by
  classical
  apply norm_matrix_le_sqrt_degrees _
    (fun (A : WordSubset W q) (B : WordSubset W p) => Disjoint A.val B.val) (p + 1) (q + 1)
  · intro A B h
    change (if Disjoint A.val B.val then (1 : H →L[ℂ] H) else 0) = 0
    simp [h]
  · intro A B
    change ‖if Disjoint A.val B.val then (1 : H →L[ℂ] H) else 0‖ ≤ 1
    split_ifs
    · exact ContinuousLinearMap.norm_id_le
    · simp
  · intro A
    exact (card_disjoint_wordSubsets W p q hW A).le
  · intro B
    have h := card_disjoint_wordSubsets W q p (by omega) B
    simpa only [disjoint_comm] using h.le

end

end KadisonKastler

end OAI
