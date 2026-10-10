import OAI.NumberTheory.Ostmann.Construction.GiantOuterFactors
import OAI.NumberTheory.Ostmann.Arithmetic.MovingKernelPair

namespace OAI

/-! # The two-history kernel with its original outer priors and diagonal ratio -/

namespace Ostmann
open MeasureTheory
open scoped BigOperators Classical ComplexConjugate SchwartzMap

noncomputable def giantOuterWeight (φ : ℝ → ℝ) (Jleft Jright : ℝ) (diagonal : Bool)
    (L R : ℝ) : ℂ :=
  (positiveLogCutoff φ Jleft L : ℂ) * (positiveLogCutoff φ Jright R : ℂ) *
    (if diagonal then ((Real.exp Jright / R : ℝ) : ℂ) else 1)

noncomputable def movingOuterKernel {σ : Type*} (value : σ → ℕ) {n : ℕ}
    (T : Bool → MovingSlotData σ n) (nodes : Bool → List MovingFormulaNode) (ψ : 𝓢(ℝ, ℂ))
    (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi) (φ : ℝ → ℝ) (G : ℕ → ℝ)
    (Jleft Jright : ℝ) (diagonal : Bool) (L R : ℝ) : ℂ :=
  movingRealKernelPair value T nodes ψ X lo hi hlo hhi φ G L R *
    giantOuterWeight φ Jleft Jright diagonal L R

theorem giantOuterWeight_polynomial (L R : Polynomial ℝ) (φ : ℝ → ℝ)
    (Jleft Jright B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hφ : ∀ x, |φ x| ≤ B) (hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|)
    (hout : ∀ x, 1 ≤ |x| → φ x = 0) (diagonal : Bool) (x : ℝ) :
    giantOuterWeight φ Jleft Jright diagonal (L.eval x) (R.eval x) =
      (giantOuterScalar diagonal : ℂ) *
        smoothPolynomialWeight (giantOuterFactors L R φ Jleft Jright B D hB hD hφ hlip diagonal) x :=
  (giantOuterFactors_value L R φ Jleft Jright B D hB hD hφ hlip hout diagonal x).symm

theorem giantOuterWeight_norm (φ : ℝ → ℝ) (Jleft Jright B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hφ : ∀ x, |φ x| ≤ B) (hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|)
    (hout : ∀ x, 1 ≤ |x| → φ x = 0) (diagonal : Bool) (L R : ℝ) :
    ‖giantOuterWeight φ Jleft Jright diagonal L R‖ ≤
      giantOuterScalar diagonal * (2 * B + D * (Real.exp 2 - 1)) ^ 2 *
        (if diagonal then 1 + Real.exp 2 else 2) := by
  have hs : 0 ≤ giantOuterScalar diagonal := by cases diagonal <;> simp [giantOuterScalar, (Real.exp_pos _).le]
  have hv := giantOuterWeight_polynomial (Polynomial.C L) (Polynomial.C R) φ Jleft Jright B D
    hB hD hφ hlip hout diagonal 0
  simp only [Polynomial.eval_C] at hv
  rw [hv, norm_mul, Complex.norm_real, Real.norm_of_nonneg hs]
  have h := mul_le_mul_of_nonneg_left (smoothPolynomialWeight_norm
    (giantOuterFactors (Polynomial.C L) (Polynomial.C R) φ Jleft Jright B D hB hD hφ hlip diagonal) 0) hs
  rw [giantOuterFactors_budget] at h
  simpa only [mul_assoc] using h

theorem measurable_giantOuterWeight (φ : ℝ → ℝ) (Jleft Jright B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hφ : ∀ x, |φ x| ≤ B) (hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|)
    (hout : ∀ x, 1 ≤ |x| → φ x = 0) (diagonal : Bool) :
    Measurable (fun z : ℝ × ℝ => giantOuterWeight φ Jleft Jright diagonal z.1 z.2) := by
  have hc (J : ℝ) : Measurable (fun x => (positiveLogCutoff φ J x : ℂ)) := by
    have he (x : ℝ) := logCutoffPolynomialFactor_value Polynomial.X φ J B D hB hD hφ hlip hout x
    simp only [Polynomial.eval_X] at he
    exact ((logCutoffPolynomialFactor Polynomial.X φ J B D hB hD hφ hlip).continuous_value.congr he).measurable
  have hratio : Measurable (fun z : ℝ × ℝ => if diagonal then ((Real.exp Jright / z.2 : ℝ) : ℂ) else 1) := by
    cases diagonal
    · exact measurable_const
    · exact Complex.continuous_ofReal.measurable.comp (measurable_const.div measurable_snd)
  exact ((hc Jleft).comp measurable_fst |>.mul ((hc Jright).comp measurable_snd)).mul hratio

theorem measurable_movingOuterKernel {σ : Type*} (value : σ → ℕ) {n : ℕ}
    (T : Bool → MovingSlotData σ n) (nodes : Bool → List MovingFormulaNode) (ψ : 𝓢(ℝ, ℂ))
    (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi) (φ : ℝ → ℝ) (G : ℕ → ℝ)
    (Jleft Jright B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hφ : ∀ x, |φ x| ≤ B) (hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|)
    (hout : ∀ x, 1 ≤ |x| → φ x = 0) (diagonal : Bool) :
    Measurable (fun z : ℝ × ℝ => movingOuterKernel value T nodes ψ X lo hi hlo hhi φ G Jleft Jright diagonal z.1 z.2) :=
  (measurable_movingRealKernelPair value T nodes ψ X lo hi hlo hhi φ G B D hB hD hφ hlip hout).mul
    (measurable_giantOuterWeight φ Jleft Jright B D hB hD hφ hlip hout diagonal)

theorem movingOuterKernel_slice_polynomial {σ : Type*} (value : σ → ℕ) {n : ℕ}
    (T : Bool → MovingSlotData σ n) (nodes : Bool → List MovingFormulaNode) (ψ : 𝓢(ℝ, ℂ))
    (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi) (φ : ℝ → ℝ) (G : ℕ → ℝ)
    (Jleft Jright B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hφ : ∀ x, |φ x| ≤ B) (hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|)
    (hout : ∀ x, 1 ≤ |x| → φ x = 0) (diagonal coord : Bool) (fixed z : ℝ) :
    let W := fun b => movingSmoothPolynomialFactors value (T b)
      (movingCoordinateLeft coord fixed) (movingCoordinateRight coord fixed)
      ψ X lo hi hlo hhi φ G B D hB hD hφ hlip
    let O := giantOuterFactors (movingCoordinateLeft coord fixed) (movingCoordinateRight coord fixed)
      φ Jleft Jright B D hB hD hφ hlip diagonal
    movingOuterKernel value T nodes ψ X lo hi hlo hhi φ G Jleft Jright diagonal
      (movingRealPair coord fixed z false) (movingRealPair coord fixed z true) =
      ((giantOuterScalar diagonal : ℂ) *
        (movingRealGateWeight value (T false) (nodes false) X lo hi (movingRealPair coord fixed z) *
          conj (movingRealGateWeight value (T true) (nodes true) X lo hi (movingRealPair coord fixed z)))) *
        smoothPolynomialWeight (Fin.append (pairedPolynomialFactors (W false) (W true)) O) z := by
  dsimp only
  unfold movingOuterKernel
  rw [movingRealKernelPair_slice_polynomial value T nodes ψ X lo hi hlo hhi φ G B D hB hD hφ hlip hout]
  have hv := giantOuterWeight_polynomial (movingCoordinateLeft coord fixed) (movingCoordinateRight coord fixed)
    φ Jleft Jright B D hB hD hφ hlip hout diagonal z
  rw [(movingCoordinate_eval coord fixed z).1, (movingCoordinate_eval coord fixed z).2] at hv
  rw [hv]
  simp only [smoothPolynomialWeight, Fin.prod_univ_add, Fin.append_left, Fin.append_right]
  ring

end Ostmann

end OAI
