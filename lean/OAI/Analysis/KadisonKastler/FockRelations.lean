import OAI.Analysis.KadisonKastler.CreationGram
import OAI.Analysis.KadisonKastler.FreeCuts

namespace OAI

/-!
# Structural free diagonal data and its consequences

This structure records the projection, support, covariance, and decomposition
identities of a free diagonal representation. Norm bounds are consequences,
not fields. No existence theorem for the structure is assumed here.
-/

namespace KadisonKastler

open Finset

noncomputable section

variable {ι α H : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance fockOperatorOrder : PartialOrder (H →L[ℂ] H) :=
  CStarAlgebra.spectralOrder _
local instance fockOperatorStarOrder : StarOrderedRing (H →L[ℂ] H) :=
  CStarAlgebra.spectralOrderedRing _

structure FreeDiagonalModel (ι α H : Type*) [Fintype α] [DecidableEq α]
    [Nonempty α] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] where
  e : ι → α → H →L[ℂ] H
  P : ι → H →L[ℂ] H
  C : ι → α → H →L[ℂ] H
  e_projection : ∀ i a, IsStarProjection (e i a)
  e_orthogonal : ∀ i a b, a ≠ b → e i a * e i b = 0
  e_sum : ∀ i, ∑ a, e i a = 1
  P_projection : ∀ i, IsStarProjection (P i)
  P_orthogonal : ∀ i j, i ≠ j → P i * P j = 0
  creation_range : ∀ i a, P i * C i a = C i a
  creation_domain : ∀ i a, C i a * (1 - P i) = C i a
  creation_gram : ∀ i a b, star (C i a) * C i b =
    ((Fintype.card α : ℂ)⁻¹ *
      ((if a = b then 1 else 0) - (Fintype.card α : ℂ)⁻¹)) • (1 - P i)
  centered_decomposition : ∀ i a,
    e i a - (Fintype.card α : ℂ)⁻¹ • 1 = C i a +
      P i * (e i a - (Fintype.card α : ℂ)⁻¹ • 1) * P i + star (C i a)

namespace FreeDiagonalModel

variable (M : FreeDiagonalModel ι α H)

def centered (i : ι) (a : α) : H →L[ℂ] H :=
  M.e i a - (Fintype.card α : ℂ)⁻¹ • 1

def D (i : ι) (a : α) : H →L[ℂ] H := M.P i * M.centered i a * M.P i

theorem centered_eq (i : ι) (a : α) :
    M.centered i a = M.C i a + M.D i a + star (M.C i a) :=
  M.centered_decomposition i a

theorem star_creation_right_support (i : ι) (a : α) :
    star (M.C i a) * M.P i = star (M.C i a) := by
  have h := congrArg star (M.creation_range i a)
  simpa only [star_mul, (M.P_projection i).isSelfAdjoint.star_eq] using h

theorem creation_mul_P (i : ι) (a : α) : M.C i a * M.P i = 0 := by
  have h := M.creation_domain i a
  rw [mul_sub, mul_one] at h
  exact sub_eq_self.mp h

theorem P_mul_star_creation (i : ι) (a : α) : M.P i * star (M.C i a) = 0 := by
  have h := congrArg star (M.creation_mul_P i a)
  simpa only [star_mul, star_zero, (M.P_projection i).isSelfAdjoint.star_eq] using h

theorem D_left_support (i : ι) (a : α) : M.P i * M.D i a = M.D i a := by
  simp only [D, ← mul_assoc, (M.P_projection i).isIdempotentElem.eq]

theorem D_right_support (i : ι) (a : α) : M.D i a * M.P i = M.D i a := by
  simp only [D, mul_assoc, (M.P_projection i).isIdempotentElem.eq]

omit [CompleteSpace H] in
private theorem mul_eq_zero_of_orthogonal_support (x y p q : H →L[ℂ] H)
    (hx : x * p = x) (hy : q * y = y) (hpq : p * q = 0) : x * y = 0 := by
  calc
    x * y = (x * p) * (q * y) := by rw [hx, hy]
    _ = x * (p * q) * y := by simp only [mul_assoc]
    _ = 0 := by rw [hpq, mul_zero, zero_mul]

/-- The four zero products used by the cut expansion follow from
orthogonality of the first-copy projections. -/
theorem star_creation_mul_creation {i j : ι} (hij : i ≠ j) (a b : α) :
    star (M.C i a) * M.C j b = 0 :=
  mul_eq_zero_of_orthogonal_support _ _ (M.P i) (M.P j)
    (M.star_creation_right_support i a) (M.creation_range j b) (M.P_orthogonal i j hij)

theorem star_creation_mul_D {i j : ι} (hij : i ≠ j) (a b : α) :
    star (M.C i a) * M.D j b = 0 :=
  mul_eq_zero_of_orthogonal_support _ _ (M.P i) (M.P j)
    (M.star_creation_right_support i a) (M.D_left_support j b) (M.P_orthogonal i j hij)

theorem D_mul_creation {i j : ι} (hij : i ≠ j) (a b : α) :
    M.D i a * M.C j b = 0 :=
  mul_eq_zero_of_orthogonal_support _ _ (M.P i) (M.P j)
    (M.D_right_support i a) (M.creation_range j b) (M.P_orthogonal i j hij)

theorem D_mul_D {i j : ι} (hij : i ≠ j) (a b : α) : M.D i a * M.D j b = 0 :=
  mul_eq_zero_of_orthogonal_support _ _ (M.P i) (M.P j)
    (M.D_right_support i a) (M.D_left_support j b) (M.P_orthogonal i j hij)

/-- The covariance identity gives the complete creation-row norm. -/
theorem norm_creation_row_le (i : ι) :
    ‖(CStarMatrix.ofMatrix (fun (_ : Unit) a => M.C i a))‖ ≤
      (Real.sqrt (Fintype.card α : ℝ))⁻¹ :=
  norm_creationRow_le (M.C i) (1 - M.P i) (M.P_projection i).one_sub (M.creation_gram i)

theorem norm_creation_le (i : ι) (a : α) :
    ‖M.C i a‖ ≤ (Real.sqrt (Fintype.card α : ℝ))⁻¹ := by
  have h := CStarMatrix.norm_entry_le_norm
    (M := CStarMatrix.ofMatrix (fun (_ : Unit) b => M.C i b)) (i := ()) (j := a)
  exact h.trans (M.norm_creation_row_le i)

theorem norm_star_creation_le (i : ι) (a : α) :
    ‖star (M.C i a)‖ ≤ (Real.sqrt (Fintype.card α : ℝ))⁻¹ := by
  rw [norm_star]
  exact M.norm_creation_le i a

/-- A projection centered by any scalar in `[0,1]` remains contractive. -/
private theorem norm_projection_sub_smul_one_le (E : H →L[ℂ] H)
    (hE : IsStarProjection E) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ‖E - (t : ℂ) • (1 : H →L[ℂ] H)‖ ≤ 1 := by
  have he : E - (t : ℂ) • (1 : H →L[ℂ] H) =
      ((1 - t : ℝ) : ℂ) • E - (t : ℂ) • (1 - E) := by
    rw [Complex.ofReal_sub, Complex.ofReal_one, sub_smul, one_smul, smul_sub]
    abel
  rw [he]
  calc
    _ ≤ ‖((1 - t : ℝ) : ℂ) • E‖ + ‖(t : ℂ) • (1 - E)‖ := norm_sub_le _ _
    _ = (1 - t) * ‖E‖ + t * ‖1 - E‖ := by
      rw [norm_smul, norm_smul, Complex.norm_real, Complex.norm_real,
        Real.norm_of_nonneg (sub_nonneg.mpr ht1), Real.norm_of_nonneg ht0]
    _ ≤ (1 - t) * 1 + t * 1 := add_le_add
      (mul_le_mul_of_nonneg_left (IsStarProjection.norm_le _ hE) (sub_nonneg.mpr ht1))
      (mul_le_mul_of_nonneg_left (IsStarProjection.norm_le _ hE.one_sub) ht0)
    _ = 1 := by ring

theorem norm_centered_le (i : ι) (a : α) : ‖M.centered i a‖ ≤ 1 := by
  have hc : (1 : ℝ) ≤ Fintype.card α := by exact_mod_cast Fintype.card_pos_iff.mpr ‹Nonempty α›
  have h := norm_projection_sub_smul_one_le (M.e i a) (M.e_projection i a)
    (t := (Fintype.card α : ℝ)⁻¹) (by positivity) (inv_le_one_of_one_le₀ hc)
  simpa only [centered, Complex.ofReal_inv, Complex.ofReal_natCast] using h

theorem norm_D_le (i : ι) (a : α) : ‖M.D i a‖ ≤ 1 := by
  have hP : ‖M.P i‖ ≤ 1 := IsStarProjection.norm_le _ (M.P_projection i)
  unfold D
  calc
    _ ≤ (‖M.P i‖ * ‖M.centered i a‖) * ‖M.P i‖ :=
      (norm_mul_le _ _).trans
        (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ (1 * 1) * 1 := mul_le_mul
      (mul_le_mul hP (M.norm_centered_le i a) (norm_nonneg _) zero_le_one)
      hP (norm_nonneg _) (by positivity)
    _ = 1 := by norm_num

/-- The structural model therefore supplies all analytic and algebraic
inputs to the proved single-centered-word estimate. -/
theorem norm_centered_word_le (label : ι → α) (l : List ι) (hl : l.Nodup) :
    ‖(l.map (fun i => M.centered i (label i))).prod‖ ≤
      (2 * l.length + 1 : ℝ) /
        Real.sqrt ((Fintype.card α : ℝ) ^ (l.length - 1)) := by
  have he : (l.map (fun i => M.centered i (label i))).prod =
      centeredLetterProduct (fun i => M.C i (label i)) (fun i => M.D i (label i))
        (fun i => star (M.C i (label i))) l := by
    unfold centeredLetterProduct
    congr 1
    apply List.map_congr_left
    intro i _
    exact M.centered_eq i (label i)
  rw [he]
  apply norm_centeredLetterProduct_le_inv_sqrt
  · intro i j hij
    exact M.star_creation_mul_creation hij (label i) (label j)
  · intro i j hij
    exact M.star_creation_mul_D hij (label i) (label j)
  · intro i j hij
    exact M.D_mul_creation hij (label i) (label j)
  · intro i j hij
    exact M.D_mul_D hij (label i) (label j)
  · exact_mod_cast Fintype.card_pos_iff.mpr ‹Nonempty α›
  · exact ContinuousLinearMap.norm_id_le
  · intro i
    exact M.norm_creation_le i (label i)
  · intro i
    exact M.norm_D_le i (label i)
  · intro i
    exact M.norm_star_creation_le i (label i)
  · exact hl

end FreeDiagonalModel

end

end KadisonKastler

end OAI
