import OAI.Analysis.Quasitrace.Matrix
import OAI.Analysis.Quasitrace.Order

namespace OAI

/-! Matrix order and the normalization of genuine corner extensions. -/

section

noncomputable section
open scoped ComplexOrder BigOperators CStarAlgebra
namespace Kaplansky
attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing
variable {A n : Type*} [CStarAlgebra A] [Fintype n] [DecidableEq n]

omit [Fintype n] in
@[simp] theorem corner_add (i : n) (a b : A) : corner i (a+b) = corner i a + corner i b := by
  change Matrix.single i i (a+b) = Matrix.single i i a + Matrix.single i i b
  exact Matrix.single_add i i a b
omit [Fintype n] in
@[simp] theorem corner_sub (i : n) (a b : A) : corner i (a-b) = corner i a - corner i b := by
  change Matrix.single i i (a-b) = Matrix.single i i a - Matrix.single i i b
  simp only [sub_eq_add_neg, Matrix.single_add, Matrix.single_neg]
omit [Fintype n] in
@[simp] theorem corner_smul (i : n) (c : ℂ) (a : A) : corner i (c • a) = c • corner i a := by
  change Matrix.single i i (c • a) = c • Matrix.single i i a
  simp
omit [Fintype n] in
@[simp] theorem corner_zero (i : n) : corner i (0 : A) = 0 := by
  change Matrix.single i i (0 : A) = 0
  simp

omit [Fintype n] in
@[simp] theorem diagonal_add (a b : n → A) :
    diagonal (a+b) = diagonal a + diagonal b := by
  change Matrix.diagonal (a+b) = Matrix.diagonal a + Matrix.diagonal b
  exact (Matrix.diagonal_add a b).symm
omit [Fintype n] in
@[simp] theorem diagonal_sub (a b : n → A) :
    diagonal (a-b) = diagonal a - diagonal b := by
  change Matrix.diagonal (a-b) = Matrix.diagonal a - Matrix.diagonal b
  exact (Matrix.diagonal_sub a b).symm
omit [Fintype n] in
@[simp] theorem diagonal_one : diagonal (fun _ : n => (1 : A)) = 1 := by
  change Matrix.diagonal (fun _ : n => (1 : A)) = 1
  rfl

theorem corner_nonneg (i : n) {a : A} (ha : 0 ≤ a) : 0 ≤ corner i a := by
  obtain ⟨x, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp ha
  rw [← corner_mul, ← corner_star]
  exact star_mul_self_nonneg _

theorem diagonal_nonneg (a : n → A) (ha : ∀ i, 0 ≤ a i) : 0 ≤ diagonal a := by
  rw [diagonal_eq_sum]
  exact Finset.sum_nonneg (fun i _ => corner_nonneg i (ha i))

theorem diagonal_positiveContraction (a : n → A) (ha : ∀ i, 0 ≤ a i)
    (hb : ∀ i, a i ≤ 1) : PositiveContraction (diagonal a) := by
  have hpos := diagonal_nonneg a ha
  choose x hx using fun i => CStarAlgebra.nonneg_iff_eq_star_mul_self.mp (ha i)
  refine ⟨⟨diagonal x, ?_⟩, ?_⟩
  · change Matrix.diagonal a = (Matrix.diagonal x).conjTranspose * Matrix.diagonal x
    rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
    congr 1
    exact funext hx
  rw [CStarAlgebra.norm_le_one_iff_of_nonneg _ hpos]
  apply sub_nonneg.mp
  have h := diagonal_nonneg (fun i => 1 - a i) (fun i => sub_nonneg.mpr (hb i))
  change 0 ≤ diagonal ((fun _ => (1 : A)) - a) at h
  rw [diagonal_sub, diagonal_one] at h
  exact h

theorem corner_positive_equal (τ : OneQuasitrace (CStarMatrix n n A)) (i j : n)
    {a : A} (ha : 0 ≤ a) : τ (corner i a) = τ (corner j a) := by
  obtain ⟨x, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp ha
  exact corner_square_equal τ i j x

theorem map_positive_diagonal (τ : OneQuasitrace (CStarMatrix n n A)) (k : n)
    (a : n → A) (ha : ∀ i, 0 ≤ a i) :
    τ (diagonal a) = ∑ i, τ (corner k (a i)) := by
  rw [map_diagonal τ a (fun i => (ha i).isSelfAdjoint)]
  exact Finset.sum_congr rfl (fun i _ => corner_positive_equal τ i k (ha i))

theorem corner_normalization (τ : OneQuasitrace (CStarMatrix n n A))
    (hτ : τ.Normalized) (k : n) : (Fintype.card n : ℂ) * τ (corner k (1 : A)) = 1 := by
  have h := map_positive_diagonal τ k (fun _ => (1 : A)) (fun _ => zero_le_one)
  change τ 1 = 1 at hτ
  simpa only [diagonal_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hτ] using h.symm

/-- Scalar translation uses the corner identity, not the ambient unit. -/
theorem corner_scalar_sub (τ : OneQuasitrace (CStarMatrix n n A)) (k : n)
    (c : ℝ) {a : A} (ha : IsSelfAdjoint a) :
    τ (corner k ((c : ℂ) • (1 : A) - a)) =
      (c : ℂ) * τ (corner k (1 : A)) - τ (corner k a) := by
  rw [corner_sub, corner_smul]
  have h1 := corner_selfAdjoint k (IsSelfAdjoint.one A)
  have hc : IsSelfAdjoint ((c : ℂ) • corner k (1 : A)) := by
    change star ((c : ℂ) • corner k (1 : A)) = _
    simp [star_smul, h1.star_eq]
  have hcomm : Commute ((c : ℂ) • corner k (1 : A)) (corner k a) := by
    change ((c : ℂ) • corner k (1 : A)) * corner k a = _
    simp [smul_mul_assoc, mul_smul_comm]
  rw [τ.map_sub hc (corner_selfAdjoint k ha) hcomm,
    τ.map_smul_selfAdjoint (c : ℂ) h1]

theorem corner_scalar_upper_bound (τ : OneQuasitrace (CStarMatrix n n A)) (k : n)
    (c : ℝ) {a : A} (ha : 0 ≤ a) (hca : a ≤ (c : ℂ) • (1 : A)) :
    (τ (corner k a)).re ≤ c * (τ (corner k (1 : A))).re := by
  have h := τ.map_nonneg (corner_nonneg k (sub_nonneg.mpr hca))
  rw [corner_scalar_sub τ k c ha.isSelfAdjoint] at h
  have hr : 0 ≤ ((c : ℂ) * τ (corner k (1 : A)) - τ (corner k a)).re := h.1
  simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero] at hr
  linarith

end Kaplansky

end
end

section

noncomputable section
open scoped ComplexOrder CStarAlgebra
namespace Kaplansky
attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing
variable {A : Type*} [CStarAlgebra A]

@[simp] theorem upperLeft_eq_corner (a : A) : upperLeft a = corner (0 : Fin 2) a := by
  ext i j
  change (if i = 0 ∧ j = 0 then a else 0) = (if 0 = i ∧ 0 = j then a else 0)
  simp only [eq_comm]

theorem extension_value_two (τ : OneQuasitrace A) (hτ : τ.Normalized)
    (σ : OneQuasitrace (CStarMatrix (Fin 2) (Fin 2) A))
    (hσ : ∀ a, σ (upperLeft a) = τ a) : σ 1 = 2 := by
  have h := map_positive_diagonal σ (0 : Fin 2) (fun _ => (1 : A))
    (fun _ => zero_le_one)
  have hcorner : σ (corner (0 : Fin 2) (1 : A)) = 1 := by
    rw [← upperLeft_eq_corner, hσ]
    exact hτ
  simpa [hcorner] using h

/-- A direct check that the target's matrix extension is not accidentally
required to be normalized. -/
theorem extension_not_normalized (τ : OneQuasitrace A) (hτ : τ.Normalized)
    (σ : OneQuasitrace (CStarMatrix (Fin 2) (Fin 2) A))
    (hσ : ∀ a, σ (upperLeft a) = τ a) : ¬ σ.Normalized := by
  intro h
  have ht := extension_value_two τ hτ σ hσ
  change σ 1 = 1 at h
  rw [h] at ht
  norm_num at ht

end Kaplansky

end
end

end OAI
