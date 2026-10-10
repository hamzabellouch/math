import OAI.NumberTheory.TwoPoint.Bounds.IntegerEdgeRows

namespace OAI

/-! Operator consequences of the concrete integer weighted-row estimate. -/

namespace TwoPointCorrelations

open Finset

variable {ι : Type*} [Fintype ι]

/-- The localized matrix-square estimate for the actual cutoff graph. -/
theorem integerEdgeMatrix_localized_square
    (site : ι → ℤ) (hinj : Function.Injective site)
    (Q : Finset ℕ) (u : ℕ → ℝ) (eligible : ℕ → Prop)
    (g center : ℤ → ℝ) (L K : ℝ) (extra : ℤ → Prop) (h d : ℕ)
    (hL : 0 < L) (hK : 0 ≤ K) (hu : ∀ q ∈ Q, 0 ≤ u q) (hg : ∀ n, 0 < g n)
    (hperiod : ∀ q ∈ Q, ∀ n, center (n + (h * q * d : ℕ)) = center n)
    (v : ι → ℂ) :
    (∑ i, ‖∑ j, (integerEdgeMatrix site Q u eligible g center L K extra h d i j : ℂ) * v j‖ ^ 2) ≤
      4 * K ^ 2 * ∑ i, |center (site i)| ^ 2 * ‖v i‖ ^ 2 := by
  have hbound := weighted_matrix_localized_square
    (fun i j => (integerEdgeMatrix site Q u eligible g center L K extra h d i j : ℂ))
    (fun i => g (site i)) (fun i => |center (site i)|) (2 * K) (by positivity)
    (fun i => hg _) (fun i => abs_nonneg _)
    (fun i j => by rw [integerEdgeMatrix_symmetric site Q u eligible g center L K extra h d i j])
    (fun i j hij => congrArg abs (integerEdgeMatrix_center_invariant Q u eligible g center L K extra h d
      site hperiod i j (fun hz => hij (by simp [hz]))))
    (fun i => by simpa only [Complex.norm_real, Real.norm_eq_abs] using
      integerEdgeMatrix_weighted_row Q u eligible g center L K extra h d site hinj hL hK hu hg hperiod i) v
  convert hbound using 1
  ring

/-- The single-operator bound `2K` for the actual centered integer graph. -/
theorem centeredIntegerEdge_operator_norm_le
    (site : ι → ℤ) (hinj : Function.Injective site)
    (Q P : Finset ℕ) (u : ℕ → ℝ) (eligible : ℕ → Prop)
    (g : ℤ → ℝ) (L K : ℝ) (extra : ℤ → Prop) (h d : ℕ)
    (hL : 0 < L) (hK : 0 ≤ K) (hu : ∀ q ∈ Q, 0 ≤ u q) (hg : ∀ n, 0 < g n)
    (hP : ∀ p ∈ P, p.Prime) (hd : ∀ p ∈ P, p ∣ d)
    (T : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι)
    (hT : ∀ v i, T v i = ∑ j,
      (integerEdgeMatrix site Q u eligible g (centeredTuple P) L K extra h d i j : ℂ) * v j) :
    ‖T‖ ≤ 2 * K := by
  have hperiod : ∀ q ∈ Q, ∀ n, centeredTuple P (n + (h * q * d : ℕ)) = centeredTuple P n :=
    fun q _ n => centeredTuple_padding_periodic P h d hd q n
  apply weighted_operator_norm_le T
    (fun i j => (integerEdgeMatrix site Q u eligible g (centeredTuple P) L K extra h d i j : ℂ))
    hT (fun i => g (site i)) (fun i => |centeredTuple P (site i)|) (2 * K) (by positivity)
    (fun i => hg _) (fun i => abs_nonneg _) (fun i => centeredTuple_abs_le_one P hP _)
  · intro i j
    rw [integerEdgeMatrix_symmetric site Q u eligible g (centeredTuple P) L K extra h d i j]
  · intro i j hij
    exact congrArg abs (integerEdgeMatrix_center_invariant Q u eligible g (centeredTuple P) L K extra h d
      site hperiod i j (fun hz => hij (by simp [hz])))
  · intro i
    simpa only [Complex.norm_real, Real.norm_eq_abs] using
      integerEdgeMatrix_weighted_row Q u eligible g (centeredTuple P) L K extra h d
        site hinj hL hK hu hg hperiod i

end TwoPointCorrelations

end OAI
