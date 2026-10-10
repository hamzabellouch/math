import Mathlib.Topology.Algebra.MvPolynomial
import OAI.NumberTheory.Ostmann.Arithmetic.MovingCanonicalComparison

namespace OAI

/-! # A single real smooth kernel for the two original giant coordinates -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate SchwartzMap

theorem MovingSlotReversal.continuous_realPivot {σ : Type*}
    (value : σ → ℕ) (s : MovingSlotReversal σ) {A : Type*} [TopologicalSpace A]
    (L R : A → ℝ) (hL : Continuous L) (hR : Continuous R) :
    Continuous (fun x => s.realPivot value (L x) (R x)) := by
  unfold realPivot
  exact ((continuous_const.mul hR).sub (continuous_const.mul hL)).div_const _

theorem MovingSlotData.continuous_realLeafModuli {σ : Type*} (value : σ → ℕ)
    {n : ℕ} (T : MovingSlotData σ n) {A : Type*} [TopologicalSpace A]
    (L R : A → ℝ) (hL : Continuous L) (hR : Continuous R) (i : TreeLeafIndex n) :
    Continuous (fun x => T.realLeafModuli value (L x) (R x) i) := by
  induction T generalizing L R with
  | leaf => exact (hL.mul hR).mul_const _
  | node s CL CR u left right ihL ihR =>
    have hp := (MovingSlotData.step s CL CR u left right false).continuous_realPivot value L R hL hR
    cases i with
    | inl i => exact ihL _ L hp hL i
    | inr i => exact ihR _ R hp hR i

noncomputable def movingRealFourierWeight {σ : Type*} (value : σ → ℕ)
    {n : ℕ} (T : MovingSlotData σ n) (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ)
    (hlo : 1 ≤ lo) (hhi : lo ≤ hi) (L R : ℝ) : ℂ :=
  ∏ i : TreeLeafIndex n,
    let v := (fourierPolynomialFactor Polynomial.X ψ (T.leafFrequencies i) lo hi hlo hhi).value
      (T.realLeafModuli value L R i / X)
    if treeLeafTupleEquiv Bool n (transferConjugations n false) i then conj v else v

theorem movingFourierPolynomialFactors_real {σ : Type*} (value : σ → ℕ)
    {n : ℕ} (T : MovingSlotData σ n) (L R : Polynomial ℝ) (ψ : 𝓢(ℝ, ℂ))
    (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi) (z : ℝ) :
    smoothPolynomialWeight (movingFourierPolynomialFactors value T L R ψ X lo hi hlo hhi) z =
      movingRealFourierWeight value T ψ X lo hi hlo hhi (L.eval z) (R.eval z) := by
  unfold smoothPolynomialWeight movingRealFourierWeight
  rw [← (movingLeafIndexEquiv n).prod_comp
    (fun j => (movingFourierPolynomialFactors value T L R ψ X lo hi hlo hhi j).value z)]
  apply Finset.prod_congr rfl
  intro i _
  simp only [movingFourierPolynomialFactors, Equiv.symm_apply_apply]
  split_ifs <;>
    simp only [ClippedPolynomialFactor.conjugate, ClippedPolynomialFactor.value,
      fourierPolynomialFactor, movingLeafNormalizedPolynomial_eval, T.leafPolynomials_real,
      Polynomial.eval_X]

theorem continuous_movingRealFourierWeight {σ : Type*} (value : σ → ℕ)
    {n : ℕ} (T : MovingSlotData σ n) (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ)
    (hlo : 1 ≤ lo) (hhi : lo ≤ hi) {A : Type*} [TopologicalSpace A]
    (L R : A → ℝ) (hL : Continuous L) (hR : Continuous R) :
    Continuous (fun x => movingRealFourierWeight value T ψ X lo hi hlo hhi (L x) (R x)) := by
  apply continuous_finsetProd
  intro i _
  have hc := (fourierPolynomialFactor Polynomial.X ψ (T.leafFrequencies i) lo hi hlo hhi).continuous_value.comp
    ((T.continuous_realLeafModuli value L R hL hR i).div_const X)
  dsimp only
  split_ifs
  · exact Complex.continuous_conj.comp hc
  · exact hc

theorem continuous_movingRealNodeCutoff {σ : Type*} (value : σ → ℕ)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hφ : ∀ x, |φ x| ≤ B) (hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|)
    (hout : ∀ x, 1 ≤ |x| → φ x = 0)
    {n : ℕ} (T : MovingSlotData σ n) {A : Type*} [TopologicalSpace A]
    (L R : A → ℝ) (hL : Continuous L) (hR : Continuous R) :
    Continuous (fun x => movingRealNodeCutoff value φ G T (L x) (R x)) := by
  have hp (g : ℝ) : Continuous (fun x => (positiveLogCutoff φ g x : ℂ)) := by
    have he (x : ℝ) := logCutoffPolynomialFactor_value Polynomial.X φ g B D hB hD hφ hlip hout x
    simp only [Polynomial.eval_X] at he
    exact ((logCutoffPolynomialFactor Polynomial.X φ g B D hB hD hφ hlip).continuous_value).congr he
  induction T generalizing L R with
  | leaf => exact continuous_const
  | @node n s CL CR u left right ihL ihR =>
    have hc := (MovingSlotData.step s CL CR u left right false).continuous_realPivot value L R hL hR
    exact (((hp (G (n + 1))).comp hc).mul (ihL _ L hc hL)).mul (ihR _ R hc hR)

noncomputable def movingRealSmoothWeight {σ : Type*} (value : σ → ℕ)
    {n : ℕ} (T : MovingSlotData σ n) (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ)
    (hlo : 1 ≤ lo) (hhi : lo ≤ hi) (φ : ℝ → ℝ) (G : ℕ → ℝ) (L R : ℝ) : ℂ :=
  movingRealFourierWeight value T ψ X lo hi hlo hhi L R * movingRealNodeCutoff value φ G T L R

theorem movingSmoothPolynomialFactors_real {σ : Type*} (value : σ → ℕ)
    {n : ℕ} (T : MovingSlotData σ n) (L R : Polynomial ℝ) (ψ : 𝓢(ℝ, ℂ))
    (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi) (φ : ℝ → ℝ) (G : ℕ → ℝ)
    (B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D) (hφ : ∀ x, |φ x| ≤ B)
    (hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|) (hout : ∀ x, 1 ≤ |x| → φ x = 0) (z : ℝ) :
    smoothPolynomialWeight (movingSmoothPolynomialFactors value T L R ψ X lo hi hlo hhi
      φ G B D hB hD hφ hlip) z =
        movingRealSmoothWeight value T ψ X lo hi hlo hhi φ G (L.eval z) (R.eval z) := by
  rw [movingSmoothPolynomialFactors_value value T L R ψ X lo hi hlo hhi φ G B D hB hD hφ hlip hout,
    movingFourierPolynomialFactors_real]
  rfl

theorem continuous_movingRealSmoothWeight {σ : Type*} (value : σ → ℕ)
    {n : ℕ} (T : MovingSlotData σ n) (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ)
    (hlo : 1 ≤ lo) (hhi : lo ≤ hi) (φ : ℝ → ℝ) (G : ℕ → ℝ) (B D : ℝ)
    (hB : 0 ≤ B) (hD : 0 ≤ D) (hφ : ∀ x, |φ x| ≤ B)
    (hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|) (hout : ∀ x, 1 ≤ |x| → φ x = 0)
    {A : Type*} [TopologicalSpace A] (L R : A → ℝ) (hL : Continuous L) (hR : Continuous R) :
    Continuous (fun x => movingRealSmoothWeight value T ψ X lo hi hlo hhi φ G (L x) (R x)) :=
  (continuous_movingRealFourierWeight value T ψ X lo hi hlo hhi L R hL hR).mul
    (continuous_movingRealNodeCutoff value φ G B D hB hD hφ hlip hout T L R hL hR)

end Ostmann

end OAI
