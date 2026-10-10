import OAI.NumberTheory.CubicMoment.Angular.AngularDistinguishedRowsSaving
import OAI.NumberTheory.CubicMoment.Angular.AngularKummerAlgebra
import OAI.NumberTheory.CubicMoment.Angular.AngularStoppedDistinguishedRows
import OAI.NumberTheory.CubicMoment.Decomposition.StoppedDistinguishedSaving
import OAI.NumberTheory.CubicMoment.Decomposition.StoppedDistinguishedRows

namespace OAI

/-! Cancellation for the literal distinguished role in the stopped beta
coefficient, with the ordered-tuple factorial retained. -/
noncomputable section
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

theorem angular_stoppedBeta_distinguished_saving (m : ℕ)
    (hEF : AngularKummerPrimeExplicitEstimate)
    (ℓ : ℤ) (hℓ : ℓ ≠ 0) {A D H E F : ℝ}
    (hA : 0 < A) (hD : 0 < D) (hH : 0 ≤ H) (hE : 0 ≤ E) (hF : 0 ≤ F) :
    ∃ K P₀ : ℝ, 0 < K ∧ 1 < P₀ ∧ ∀ (T B ρ a b w z u V : ℝ) (j : ℕ),
      1 ≤ T → 1 < ρ → ρ ≤ 2 → j < geometricBinCount ρ B →
      P₀ ≤ geometricBinLower ρ B j → T ≤ (Real.log (geometricBinLower ρ B j))^2 →
      0 ≤ b → 1 ≤ w → w ≤ z → 0 ≤ V → |u| ≤ T^H → 1+V ≤ T^F →
      b/geometricBinLower ρ B j < w^m →
      ∀ (W : ι → ℝ → ℂ) (D₀ : Finset Eisenstein),
      (∀ l x, ‖W l x‖ ≤ 1) → (∀ l, ContDiff ℝ ∞ (W l)) →
      (∀ l x, 0 < x → ‖deriv (W l) x‖*x ≤ V) →
      (∀ d ∈ D₀, primary d) →
      ∀ v e : Eisenstein, v ≠ 0 → (¬∃ n : Eisenstein, n^3 = v) → norm v ≤ T^A → e ≠ 0 →
      (∀ i, ∀ t ∈ coordinateComplementTuples (fun _ : ι => primeCutoff B) i ×ˢ D₀,
        Squarefree ((∏ l, t.1 l)*t.2) → norm ((∏ l, t.1 l)*t.2) ≤ b/geometricBinLower ρ B j →
        Real.log (norm ((∏ l, t.1 l)*(t.2*e))) ≤ T^E) →
      ∀ (j₀ k h : ℕ) (Z Q : ℝ) (early : Bool),
      ‖∑ n ∈ primaryPairSupport (orderedConvolutionSupport (fun _ : ι => primeCutoff B)) D₀,
        stoppedBeta (orderedConvolutionSupport (fun _ : ι => primeCutoff B)) D₀
          (distinguishedTupleCoefficient (fun _ : ι => primeCutoff B)
            (fun l p => W l (norm p)) primeDetectorCutoff w z) primeDetectorCutoff w
          (stoppedDistinguishedTest B ρ j j₀ k h Z Q early) n *
        (if Squarefree n ∧ IsCoprime n e ∧ a < norm n ∧ norm n ≤ b
          then normTwist u n*angularCubicSymbol ℓ n v else 0)‖ ≤ K*b/T^D := by
  choose C P hC hP hbound using fun i : ι =>
    angular_stopped_distinguished_rows_saving i m hEF ℓ hℓ hA hD hH hE hF
  let q : ℝ := ‖((Fintype.card ι).factorial:ℂ)⁻¹‖
  let K : ℝ := q*(∑ i, C i)+1
  let P₀ : ℝ := 2+∑ i, |P i|
  have hK : 0 < K := by
    have hs : 0 ≤ ∑ i, C i := Finset.sum_nonneg (fun i _ => (hC i).le)
    have hq : 0 ≤ q := _root_.norm_nonneg _
    dsimp [K]
    nlinarith [mul_nonneg hq hs]
  have hP₀ : 1 < P₀ := by
    dsimp [P₀]
    have hn : 0 ≤ ∑ i, |P i| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
    linarith
  refine ⟨K,P₀,hK,hP₀,?_⟩
  intro T B ρ a b w z u V j hT hρ hρ₂ hj hp hTP hb hw hwz hV hu hVF hsize
    W D₀ hW hWi hWd hD₀ v e hv hnc hNv he hNe j₀ k h Z Q early
  have hiP (i : ι) : P i ≤ geometricBinLower ρ B j := by
    apply le_trans ?_ hp
    calc
      P i ≤ |P i| := le_abs_self _
      _ ≤ ∑ l, |P l| := Finset.single_le_sum
        (f := fun l : ι => |P l|) (fun l _ => abs_nonneg (P l)) (Finset.mem_univ i)
      _ ≤ P₀ := by dsimp [P₀]; linarith
  have hrow (i : ι) :
      ‖angular_stoppedDistinguishedRows ℓ B ρ a b w z u j j₀ k h Z Q early W D₀ v e i‖ ≤ C i*b/T^D := by
    exact hbound i T B ρ a b w z u V j hT hρ hρ₂ hj (hiP i) hTP hb hw hwz hV hu hVF hsize
      (fun _ : ι => primeCutoff B) W D₀ (fun _ _ h => (mem_primeCutoff.mp h).1)
      hW (hWi i) (hWd i) hD₀ v e hv hnc hNv he (hNe i) j₀ k h Z Q early
  rw [angular_stoppedBeta_distinguished_rows ℓ B ρ a b w z u j j₀ k h Z Q early W D₀ hD₀ v e,norm_mul]
  change q*‖∑ i, angular_stoppedDistinguishedRows ℓ B ρ a b w z u j j₀ k h Z Q early W D₀ v e i‖ ≤ _
  calc
    _ ≤ q*∑ i, ‖angular_stoppedDistinguishedRows ℓ B ρ a b w z u j j₀ k h Z Q early W D₀ v e i‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (_root_.norm_nonneg _)
    _ ≤ q*∑ i, C i*b/T^D :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => hrow i)) (_root_.norm_nonneg _)
    _ = (q*∑ i, C i)*b/T^D := by rw [←Finset.sum_div,←Finset.sum_mul]; ring
    _ ≤ K*b/T^D := by
      apply div_le_div_of_nonneg_right ?_ (Real.rpow_pos_of_pos (zero_lt_one.trans_le hT) _).le
      apply mul_le_mul_of_nonneg_right ?_ hb
      dsimp [K]
      linarith

end CubicFirstMoment

end

end OAI
