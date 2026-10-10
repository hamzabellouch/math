import Mathlib.LinearAlgebra.Matrix.Gershgorin
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.FieldTheory.Separable
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Algebra.Polynomial

namespace OAI

/-!
# Separated real spectra under small perturbations

The spectral step in EKL (2006), Lemma 5.3, can be obtained from diagonal
row dominance and the intermediate value theorem. The determinant keeps
its sign along a perturbation whose row sums are smaller than the
corresponding diagonal entries. Opposite endpoint signs then locate a
real characteristic root in each separated interval.
-/

noncomputable section
open Set Matrix
open scoped BigOperators Classical

namespace DukePrimeDegree

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma det_diagonal_add_ne_zero_of_row_norm
    (d : ι → ℝ) (E : Matrix ι ι ℝ)
    (hE : ∀ i, ∑ j, ‖E i j‖ < ‖d i‖) :
    (diagonal d + E).det ≠ 0 := by
  apply det_ne_zero_of_sum_row_lt_diag
  intro i
  have hsum : (∑ j ∈ Finset.univ.erase i, ‖E i j‖) + ‖E i i‖ =
      ∑ j, ‖E i j‖ := Finset.sum_erase_add _ _ (Finset.mem_univ i)
  have htri : ‖d i‖ ≤ ‖d i + E i i‖ + ‖E i i‖ := by
    simpa only [add_sub_cancel_right] using norm_sub_le (d i + E i i) (E i i)
  have hoff : (∑ j ∈ Finset.univ.erase i, ‖(diagonal d + E) i j‖) =
      ∑ j ∈ Finset.univ.erase i, ‖E i j‖ := by
    apply Finset.sum_congr rfl
    intro j hj
    have hji : j ≠ i := (Finset.mem_erase.mp hj).1
    simp [Matrix.add_apply, diagonal_apply_ne _ hji.symm]
  rw [hoff, Matrix.add_apply, diagonal_apply_eq]
  have := hE i
  linarith

lemma det_diagonal_add_same_sign
    (d : ι → ℝ) (E : Matrix ι ι ℝ)
    (hE : ∀ i, ∑ j, ‖E i j‖ < ‖d i‖) :
    0 < (diagonal d).det * (diagonal d + E).det := by
  let f : ℝ → ℝ := fun t => (diagonal d + t • E).det
  have hcont : Continuous f := by
    apply Continuous.matrix_det
    exact continuous_const.add (continuous_id.smul continuous_const)
  have hn : ∀ t ∈ Icc (0 : ℝ) 1, f t ≠ 0 := by
    intro t ht
    apply det_diagonal_add_ne_zero_of_row_norm
    intro i
    calc
      (∑ j, ‖(t • E) i j‖) = t * ∑ j, ‖E i j‖ := by
        simp only [Matrix.smul_apply, smul_eq_mul, norm_mul, Real.norm_eq_abs,
          abs_of_nonneg ht.1, Finset.mul_sum]
      _ ≤ ∑ j, ‖E i j‖ := mul_le_of_le_one_left (Finset.sum_nonneg fun _ _ => norm_nonneg _) ht.2
      _ < ‖d i‖ := hE i
  have hn0 : f 0 ≠ 0 := hn 0 ⟨le_rfl, zero_le_one⟩
  have hpos : 0 < f 0 * f 1 := by
    apply isPreconnected_Icc.lt_of_ne (hcont.continuousOn.const_mul (f 0))
    · intro t ht
      exact mul_ne_zero hn0 (hn t ht)
    · exact ⟨0, ⟨le_rfl, zero_le_one⟩, mul_self_pos.mpr hn0⟩
    · exact ⟨zero_le_one, le_rfl⟩
  simpa only [f, zero_smul, add_zero, one_smul] using hpos

lemma continuous_has_root_of_mul_neg {f : ℝ → ℝ} {a b : ℝ}
    (hf : ContinuousOn f (Icc a b)) (hab : a < b) (hsign : f a * f b < 0) :
    ∃ x ∈ Ioo a b, f x = 0 := by
  have hfa : f a ≠ 0 := by intro h; simp [h] at hsign
  have hfb : f b ≠ 0 := by intro h; simp [h] at hsign
  have hzero : ∃ x ∈ Icc a b, f x = 0 := by
    rcases mul_neg_iff.mp hsign with h | h
    · exact intermediate_value_Icc' hab.le hf ⟨h.2.le, h.1.le⟩
    · exact intermediate_value_Icc hab.le hf ⟨h.1.le, h.2.le⟩
  obtain ⟨x, hx, hfx⟩ := hzero
  refine ⟨x, ⟨lt_of_le_of_ne hx.1 ?_, lt_of_le_of_ne hx.2 ?_⟩, hfx⟩
  · intro hax
    exact hfa (hax ▸ hfx)
  · intro hxb
    exact hfb (hxb ▸ hfx)

/-- A diagonal root bracket survives perturbations controlled by row sums. -/
theorem charpoly_has_root_of_diagonal_bracket
    (w : ι → ℝ) (E : Matrix ι ι ℝ) {a b : ℝ} (hab : a < b)
    (ha : ∀ i, ∑ j, ‖E i j‖ < ‖a - w i‖)
    (hb : ∀ i, ∑ j, ‖E i j‖ < ‖b - w i‖)
    (hsign : (∏ i, (a - w i)) * (∏ i, (b - w i)) < 0) :
    ∃ x ∈ Ioo a b, (diagonal w + E).charpoly.eval x = 0 := by
  have heval (z : ℝ) :
      (diagonal w + E).charpoly.eval z =
        (diagonal (fun i => z - w i) + -E).det := by
    rw [Matrix.eval_charpoly]
    congr 1
    ext i j
    by_cases hij : i = j
    · subst j
      simp [Matrix.scalar_apply, Matrix.sub_apply, Matrix.add_apply]
      ring
    · simp [Matrix.scalar_apply, Matrix.sub_apply, Matrix.add_apply, hij]
  have hsa := det_diagonal_add_same_sign (fun i => a - w i) (-E) (by simpa using ha)
  have hsb := det_diagonal_add_same_sign (fun i => b - w i) (-E) (by simpa using hb)
  rw [Matrix.det_diagonal, ← heval] at hsa hsb
  apply continuous_has_root_of_mul_neg (Polynomial.continuous _).continuousOn hab
  rcases mul_neg_iff.mp hsign with h | h
  · have hleft : 0 < (diagonal w + E).charpoly.eval a := ((mul_pos_iff.mp hsa).resolve_right (fun hn => (not_lt_of_gt h.1) hn.1)).2
    have hright : (diagonal w + E).charpoly.eval b < 0 := ((mul_pos_iff.mp hsb).resolve_left (fun hp => (not_lt_of_gt hp.1) h.2)).2
    exact mul_neg_of_pos_of_neg hleft hright
  · have hleft : (diagonal w + E).charpoly.eval a < 0 := ((mul_pos_iff.mp hsa).resolve_left (fun hp => (not_lt_of_gt hp.1) h.1)).2
    have hright : 0 < (diagonal w + E).charpoly.eval b := ((mul_pos_iff.mp hsb).resolve_right (fun hn => (not_lt_of_gt h.2) hn.1)).2
    exact mul_neg_of_neg_of_pos hleft hright

lemma diagonal_bracket_sign (w : ι → ℝ) (k : ι) {a b : ℝ}
    (ha : a < w k) (hb : w k < b)
    (hout : ∀ j, j ≠ k → w j < a ∨ b < w j) :
    (∏ i, (a - w i)) * (∏ i, (b - w i)) < 0 := by
  rw [← Finset.prod_mul_distrib,
    ← Finset.mul_prod_erase _ _ (Finset.mem_univ k)]
  apply mul_neg_of_neg_of_pos
  · exact mul_neg_of_neg_of_pos (sub_neg.mpr ha) (sub_pos.mpr hb)
  · apply Finset.prod_pos
    intro j hj
    rcases hout j (Finset.mem_erase.mp hj).1 with h | h
    · exact mul_pos (sub_pos.mpr h) (sub_pos.mpr (h.trans (ha.trans hb)))
    · exact mul_pos_of_neg_of_neg (sub_neg.mpr ((ha.trans hb).trans h)) (sub_neg.mpr h)

/-- Disjoint brackets around all diagonal entries supply every characteristic root.
The bounds are on the actual perturbation, not on an assumed spectrum. -/
theorem charpoly_roots_of_separated_brackets
    (w : ι → ℝ) (E : Matrix ι ι ℝ) (a b : ι → ℝ)
    (ha : ∀ i, a i < w i) (hb : ∀ i, w i < b i)
    (hout : ∀ i j, j ≠ i → w j < a i ∨ b i < w j)
    (hdis : ∀ i j, i ≠ j → b i ≤ a j ∨ b j ≤ a i)
    (hEa : ∀ i k, ∑ j, ‖E k j‖ < ‖a i - w k‖)
    (hEb : ∀ i k, ∑ j, ‖E k j‖ < ‖b i - w k‖) :
    ∃ r : ι → ℝ, (∀ i, r i ∈ Ioo (a i) (b i) ∧
      (diagonal w + E).charpoly.eval (r i) = 0) ∧
      Function.Injective r ∧
      (diagonal w + E).charpoly.roots = (Finset.univ.image r).val ∧
      (diagonal w + E).charpoly.Splits ∧
      (diagonal w + E).charpoly.Separable := by
  have hex (i : ι) : ∃ x ∈ Ioo (a i) (b i), (diagonal w + E).charpoly.eval x = 0 :=
    charpoly_has_root_of_diagonal_bracket w E ((ha i).trans (hb i)) (hEa i) (hEb i)
      (diagonal_bracket_sign w i (ha i) (hb i) (hout i))
  choose r hr hroot using hex
  have hinj : Function.Injective r := by
    intro i j heq
    by_contra hne
    rcases hdis i j hne with h | h
    · have hi := (hr i).2
      have hj := (hr j).1
      linarith
    · have hi := (hr i).1
      have hj := (hr j).2
      linarith
  have hroots : (diagonal w + E).charpoly.roots = (Finset.univ.image r).val := by
    apply Polynomial.roots_eq_of_natDegree_le_card_of_ne_zero
    · intro x hx
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
      exact hroot i
    · rw [Matrix.charpoly_natDegree_eq_dim, Finset.card_image_of_injective _ hinj,
        Finset.card_univ]
    · exact (Matrix.charpoly_monic _).ne_zero
  have hsplit : (diagonal w + E).charpoly.Splits := by
    apply Polynomial.splits_iff_card_roots.mpr
    rw [hroots]
    change (Finset.univ.image r).card = (diagonal w + E).charpoly.natDegree
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ,
      Matrix.charpoly_natDegree_eq_dim]
  refine ⟨r, fun i => ⟨hr i, hroot i⟩, hinj, hroots, hsplit, ?_⟩
  apply (Polynomial.nodup_roots_iff_of_splits (Matrix.charpoly_monic _).ne_zero hsplit).mp
  rw [hroots]
  exact (Finset.univ.image r).nodup

end DukePrimeDegree

end

end OAI
