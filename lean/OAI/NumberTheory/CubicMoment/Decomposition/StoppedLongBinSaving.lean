import OAI.NumberTheory.CubicMoment.Decomposition.StoppedAllTuples
import OAI.NumberTheory.CubicMoment.Decomposition.StoppedSelectedLogSaving
import OAI.NumberTheory.CubicMoment.Decomposition.StoppedBinMoment
import OAI.NumberTheory.CubicMoment.Decomposition.StoppedBinSaving

namespace OAI

/-! All long bins of the literal stopped coefficient have arbitrary
logarithmic saving. The number of bins is accounted for explicitly. -/
noncomputable section
open Filter
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def stoppedCharacterSum (B w z a b u : ℝ) (W : ι → ℝ → ℂ)
    (selected : Eisenstein → Eisenstein → Prop) (v e : Eisenstein) : ℂ :=
  ∑ n ∈ primaryPairSupport (orderedConvolutionSupport (fun _ : ι => primeCutoff B))
      (primaryElementBall B),
    stoppedBeta (orderedConvolutionSupport (fun _ : ι => primeCutoff B)) (primaryElementBall B)
      (distinguishedTupleCoefficient (fun _ : ι => primeCutoff B)
        (fun l p => W l (norm p)) primeDetectorCutoff w z) primeDetectorCutoff w selected n*
      (if Squarefree n ∧ IsCoprime n e ∧ a < norm n ∧ norm n ≤ b
        then normTwist u n*cubicSymbol n v else 0)

lemma stoppedCharacterSum_largest_roles (B ρ w z a b u : ℝ) (W : ι → ℝ → ℂ)
    {j : ℕ} (hj : j < geometricBinCount ρ B) (j₀ k h : ℕ) (Z Q : ℝ) (early : Bool)
    (v e : Eisenstein) :
    stoppedCharacterSum B w z a b u W (stoppedLargestBinTest B ρ j j₀ k h Z Q early) v e =
      stoppedCharacterSum B w z a b u W (stoppedDistinguishedTest B ρ j j₀ k h Z Q early) v e+
      stoppedCharacterSum B w z a b u W (stoppedSelectedTest B ρ j j₀ k h Z Q early) v e := by
  apply stopped_largest_bin_moment_roles
  · intro n hn
    exact primaryPairSupport_primary _ _
      (fun r hr => orderedPrimarySupport_primary _ (fun _ _ hp => (mem_primeCutoff.mp hp).1.1) hr)
      (fun d hd => (mem_primaryElementBall.mp hd).1) hn
  · intro n hn
    simp only [hn,false_and,ite_false]
  · exact hj

theorem stoppedBeta_long_bins_log_saving (m : ℕ)
    (hSW : KummerPrimeSiegelWalfisz) {A D H E F J ξ : ℝ}
    (hA : 0 < A) (hD : 0 < D) (hH : 0 ≤ H) (hF : 0 ≤ F) (hJ : 0 ≤ J)
    (hξ : 0 < ξ) (hξz : ξ ≤ 2/5) (hgap : 1 < ξ*m) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ X : ℝ in atTop,
      ∀ (δ a b u V : ℝ), 0 < δ → δ ≤ 1 → (Real.log X)^(-J) ≤ δ →
      0 ≤ b → b ≤ X → 0 ≤ V → |u| ≤ (Real.log X)^H → 1+V ≤ (Real.log X)^F →
      ∀ W : ι → ℝ → ℂ, (∀ l x, ‖W l x‖ ≤ 1) → (∀ l, ContDiff ℝ ∞ (W l)) →
      (∀ l x, 0 < x → ‖deriv (W l) x‖*x ≤ V) →
      ∀ v e : Eisenstein, v ≠ 0 → (¬∃ n : Eisenstein, n^3 = v) →
      norm v ≤ (Real.log X)^A → e ≠ 0 → norm e ≤ X^E →
      ∀ (j₀ k h : ℕ) (Z Q : ℝ) (early : Bool),
      ‖∑ j ∈ stoppedLongBins X (1+δ) (Real.exp (Real.sqrt (Real.log X))),
        stoppedCharacterSum X (X^ξ) (X^(2/5:ℝ)) a b u W
          (stoppedLargestBinTest X (1+δ) j j₀ k h Z Q early) v e‖ ≤ K*b/(Real.log X)^D := by
  have hD' : 0 < D+J+1 := by linarith
  obtain ⟨Kd,hKd,hd⟩ := stoppedBeta_distinguished_log_saving_all (ι := ι) m hSW
    (C := 1) (D := D+J+1) (E := E) hA hD' hH hF hξ hgap
  obtain ⟨Ks,hKs,hs⟩ := stoppedBeta_selected_log_saving (ι := ι) m hSW
    (C := 1) (D := D+J+1) (E := E) hA hD' hH hξ hgap
  refine ⟨3*(Kd+Ks),by positivity,?_⟩
  filter_upwards [hd,hs,eventually_gt_atTop (1:ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ))] with X hd hs hX hL
  intro δ a b u V hδ hδone hwidth hb hbX hV hu hVF W hW hWi hWd
    v e hv hnc hNv he heX j₀ k h Z Q early
  have hXp : 0 < X := zero_lt_one.trans hX
  have hρ : 1 < 1+δ := by linarith
  have hρ₂ : 1+δ ≤ 2 := by linarith
  have hwz : X^ξ ≤ X^(2/5:ℝ) := Real.rpow_le_rpow_of_exponent_le hX.le hξz
  let S := stoppedLongBins X (1+δ) (Real.exp (Real.sqrt (Real.log X)))
  let f := fun j => stoppedCharacterSum X (X^ξ) (X^(2/5:ℝ)) a b u W
    (stoppedLargestBinTest X (1+δ) j j₀ k h Z Q early) v e
  have hS : S ⊆ Finset.range (geometricBinCount (1+δ) X) := Finset.filter_subset _ _
  have hf (j : ℕ) (hj : j ∈ S) : ‖f j‖ ≤ (Kd+Ks)*b/(Real.log X)^(D+J+1) := by
    obtain ⟨hj,hP⟩ := Finset.mem_filter.mp hj
    have hj' := Finset.mem_range.mp hj
    have hdist := hd X (1+δ) a b (X^(2/5:ℝ)) u V j hρ hρ₂ hj' hP hb
      (by simpa only [Real.rpow_one] using hbX) hwz hV hu hVF W (primaryElementBall X)
      hW hWi hWd (fun d hd => (mem_primaryElementBall.mp hd).1)
      v e hv hnc hNv he heX j₀ k h Z Q early
    have hsel := hs X (1+δ) a b (X^(2/5:ℝ)) u j hρ hρ₂ hj' hP hbX hb
      (by simpa only [Real.rpow_one] using hbX) hwz hu W hW v e hv hnc hNv he heX
      j₀ k h Z Q early
    change ‖stoppedCharacterSum _ _ _ _ _ _ _ _ _ _‖ ≤ _
    rw [stoppedCharacterSum_largest_roles X (1+δ) (X^ξ) (X^(2/5:ℝ)) a b u W
      hj' j₀ k h Z Q early v e]
    apply (norm_add_le _ _).trans
    apply (add_le_add hdist hsel).trans_eq
    ring
  simpa only [mul_one, show (2:ℝ)+1=3 by norm_num] using geometric_bin_log_saving hXp hL hX.le
    (by rw [Real.rpow_one]) (by norm_num : (0:ℝ) ≤ 1) hJ hδ hδone hwidth
    (add_nonneg hKd.le hKs.le) hb S hS f hf

end CubicFirstMoment

end

end OAI
