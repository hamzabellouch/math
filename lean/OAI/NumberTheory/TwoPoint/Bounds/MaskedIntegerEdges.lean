import OAI.NumberTheory.TwoPoint.Bounds.IntegerEdgeOperators
import OAI.NumberTheory.TwoPoint.Bounds.MaskedRows

namespace OAI

/-! Extra symmetric edge restrictions preserve the concrete graph estimates. -/

namespace TwoPointCorrelations

open Finset

variable {ι : Type*} [Fintype ι]

noncomputable def maskedIntegerEdgeMatrix
    (site : ι → ℤ) (Q : Finset ℕ) (u : ℕ → ℝ) (eligible : ℕ → Prop)
    (g center : ℤ → ℝ) (L K : ℝ) (extra : ℤ → Prop) (h d : ℕ)
    (gate : ι → ι → Prop) : ι → ι → ℂ :=
  maskMatrix gate (fun i j => (integerEdgeMatrix site Q u eligible g center L K extra h d i j : ℂ))

lemma maskedIntegerEdgeMatrix_symmetric
    (site : ι → ℤ) (Q : Finset ℕ) (u : ℕ → ℝ) (eligible : ℕ → Prop)
    (g center : ℤ → ℝ) (L K : ℝ) (extra : ℤ → Prop) (h d : ℕ)
    (gate : ι → ι → Prop) (hgate : ∀ i j, gate i j ↔ gate j i) (i j : ι) :
    maskedIntegerEdgeMatrix site Q u eligible g center L K extra h d gate i j =
      star (maskedIntegerEdgeMatrix site Q u eligible g center L K extra h d gate j i) := by
  classical
  simp only [maskedIntegerEdgeMatrix, maskMatrix, hgate i j]
  split_ifs
  · simp only [Complex.star_def, Complex.conj_ofReal]
    rw [integerEdgeMatrix_symmetric site Q u eligible g center L K extra h d i j]
  · simp

lemma maskedIntegerEdgeMatrix_weighted_row
    (site : ι → ℤ) (hinj : Function.Injective site)
    (Q : Finset ℕ) (u : ℕ → ℝ) (eligible : ℕ → Prop)
    (g center : ℤ → ℝ) (L K : ℝ) (extra : ℤ → Prop) (h d : ℕ)
    (gate : ι → ι → Prop)
    (hL : 0 < L) (hK : 0 ≤ K) (hu : ∀ q ∈ Q, 0 ≤ u q) (hg : ∀ n, 0 < g n)
    (hperiod : ∀ q ∈ Q, ∀ n, center (n + (h * q * d : ℕ)) = center n) (i : ι) :
    ∑ j, ‖maskedIntegerEdgeMatrix site Q u eligible g center L K extra h d gate i j‖ *
      g (site j) / g (site i) ≤ 2 * K * |center (site i)| := by
  apply maskMatrix_weighted_row gate _ (fun i => g (site i)) (fun i => |center (site i)|)
    (2 * K) (fun i => hg _)
  intro k
  simpa only [Complex.norm_real, Real.norm_eq_abs] using
    integerEdgeMatrix_weighted_row Q u eligible g center L K extra h d site hinj hL hK hu hg hperiod k

lemma maskedIntegerEdgeMatrix_level
    (site : ι → ℤ) (Q : Finset ℕ) (u : ℕ → ℝ) (eligible : ℕ → Prop)
    (g center : ℤ → ℝ) (L K : ℝ) (extra : ℤ → Prop) (h d : ℕ)
    (gate : ι → ι → Prop)
    (hperiod : ∀ q ∈ Q, ∀ n, center (n + (h * q * d : ℕ)) = center n) (i j : ι)
    (hij : maskedIntegerEdgeMatrix site Q u eligible g center L K extra h d gate i j ≠ 0) :
    |center (site i)| = |center (site j)| := by
  apply maskMatrix_level gate _ (fun i => |center (site i)|) _ i j hij
  intro k m hkm
  exact congrArg abs (integerEdgeMatrix_center_invariant Q u eligible g center L K extra h d
    site hperiod k m (fun hz => hkm (by simp [hz])))

/-- The full localized estimate survives all symmetric entry restrictions. -/
theorem maskedIntegerEdgeMatrix_localized_square
    (site : ι → ℤ) (hinj : Function.Injective site)
    (Q : Finset ℕ) (u : ℕ → ℝ) (eligible : ℕ → Prop)
    (g center : ℤ → ℝ) (L K : ℝ) (extra : ℤ → Prop) (h d : ℕ)
    (gate : ι → ι → Prop) (hgate : ∀ i j, gate i j ↔ gate j i)
    (hL : 0 < L) (hK : 0 ≤ K) (hu : ∀ q ∈ Q, 0 ≤ u q) (hg : ∀ n, 0 < g n)
    (hperiod : ∀ q ∈ Q, ∀ n, center (n + (h * q * d : ℕ)) = center n)
    (v : ι → ℂ) :
    (∑ i, ‖∑ j, maskedIntegerEdgeMatrix site Q u eligible g center L K extra h d gate i j * v j‖ ^ 2) ≤
      4 * K ^ 2 * ∑ i, |center (site i)| ^ 2 * ‖v i‖ ^ 2 := by
  have hs := weighted_matrix_localized_square
    (maskedIntegerEdgeMatrix site Q u eligible g center L K extra h d gate)
    (fun i => g (site i)) (fun i => |center (site i)|) (2 * K) (by positivity)
    (fun i => hg _) (fun i => abs_nonneg _)
    (fun i j => by rw [maskedIntegerEdgeMatrix_symmetric site Q u eligible g center L K extra h d gate hgate i j, norm_star])
    (maskedIntegerEdgeMatrix_level site Q u eligible g center L K extra h d gate hperiod)
    (maskedIntegerEdgeMatrix_weighted_row site hinj Q u eligible g center L K extra h d gate hL hK hu hg hperiod) v
  convert hs using 1
  ring

end TwoPointCorrelations

end OAI
