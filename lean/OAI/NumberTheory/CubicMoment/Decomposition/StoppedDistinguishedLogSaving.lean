import OAI.NumberTheory.CubicMoment.Decomposition.StoppedDistinguishedSaving
import OAI.NumberTheory.CubicMoment.Decomposition.StoppedPrimeScale

namespace OAI

/-! Uniform log-X saving for the literal distinguished role. Polynomial
exclusions and the complementary roughness condition are derived from
their actual norm bounds, rather than added prime-row assumptions. -/
noncomputable section
open Filter
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

theorem stoppedBeta_distinguished_log_saving (m : ℕ)
    (hSW : KummerPrimeSiegelWalfisz) {A D H E F C ξ : ℝ}
    (hA : 0 < A) (hD : 0 < D) (hH : 0 ≤ H) (hF : 0 ≤ F)
    (hξ : 0 < ξ) (hgap : C < ξ*m) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ X : ℝ in atTop,
      ∀ (B ρ a b z u V : ℝ) (j : ℕ),
      1 < ρ → ρ ≤ 2 → j < geometricBinCount ρ B →
      Real.exp (Real.sqrt (Real.log X))/2 ≤ geometricBinLower ρ B j →
      0 ≤ b → b ≤ X^C → X^ξ ≤ z → 0 ≤ V →
      |u| ≤ (Real.log X)^H → 1+V ≤ (Real.log X)^F →
      ∀ (W : ι → ℝ → ℂ) (D₀ : Finset Eisenstein),
      (∀ l x, ‖W l x‖ ≤ 1) → (∀ l, ContDiff ℝ ∞ (W l)) →
      (∀ l x, 0 < x → ‖deriv (W l) x‖*x ≤ V) →
      (∀ d ∈ D₀, primary d) →
      ∀ v e : Eisenstein, v ≠ 0 → (¬∃ n : Eisenstein, n^3 = v) →
      norm v ≤ (Real.log X)^A → e ≠ 0 → norm e ≤ X^E →
      ∀ (j₀ k h : ℕ) (Z Q : ℝ) (early : Bool),
      ‖∑ n ∈ primaryPairSupport (orderedConvolutionSupport (fun _ : ι => primeCutoff B)) D₀,
        stoppedBeta (orderedConvolutionSupport (fun _ : ι => primeCutoff B)) D₀
          (distinguishedTupleCoefficient (fun _ : ι => primeCutoff B)
            (fun l p => W l (norm p)) primeDetectorCutoff (X^ξ) z) primeDetectorCutoff (X^ξ)
          (stoppedDistinguishedTest B ρ j j₀ k h Z Q early) n *
        (if Squarefree n ∧ IsCoprime n e ∧ a < norm n ∧ norm n ≤ b
          then normTwist u n*cubicSymbol n v else 0)‖ ≤ K*b/(Real.log X)^D := by
  obtain ⟨K,P₀,hK,hP₀,hbound⟩ := stoppedBeta_distinguished_saving (ι := ι) m hSW
    (A := A+1) (D := D) (H := H+1) (E := 2) (F := F+1)
    (by linarith) hD (by linarith) (by norm_num) (by linarith)
  refine ⟨K*4^D,by positivity,?_⟩
  filter_upwards [long_prime_logarithmic_window hP₀,
    eventually_log_parameter_power 1 A,eventually_log_parameter_power 1 H,
    eventually_log_parameter_power 1 F,eventually_log_parameter_power (C+E) 1,
    eventually_gt_atTop (1:ℝ)] with X hwindow hscaleA hscaleH hscaleF hscaleE hX
  intro B ρ a b z u V j hρ hρ₂ hj hPlong hb hbX hwz hV hu hVF
    W D₀ hW hWi hWd hD₀ v e hv hnc hNv he heX j₀ k h Z Q early
  have hXp : 0 < X := zero_lt_one.trans hX
  have hLp : 0 < Real.log X := Real.log_pos hX
  have hP := hwindow.2 _ hPlong
  have hw : 1 ≤ X^ξ := Real.one_le_rpow hX.le hξ.le
  have hsize : b/geometricBinLower ρ B j < (X^ξ)^m :=
    stopped_complement_power_bound hX hgap hb hbX (geometricBinLower_gt_one hρ hj).le
  have hNe (i : ι) (t : (ι → Eisenstein) × Eisenstein)
      (ht : t ∈ coordinateComplementTuples (fun _ : ι => primeCutoff B) i ×ˢ D₀)
      (_hs : Squarefree ((∏ l, t.1 l)*t.2))
      (hn : norm ((∏ l, t.1 l)*t.2) ≤ b/geometricBinLower ρ B j) :
      Real.log (norm ((∏ l, t.1 l)*(t.2*e))) ≤ (Real.log X/4)^(2:ℝ) := by
    obtain ⟨hg,hd⟩ := Finset.mem_product.mp ht
    have hprod := complementTuple_primary (fun _ : ι => primeCutoff B)
      (fun _ _ hp => (mem_primeCutoff.mp hp).1) i hg
    apply (stopped_complement_exclusion_log hprod (hD₀ _ hd) he hXp hb hbX
      (geometricBinLower_gt_one hρ hj).le hn heX).trans
    simpa only [Real.rpow_one,show (1:ℝ)+1=2 by norm_num] using hscaleE.2
  have hh := hbound (Real.log X/4) B ρ a b (X^ξ) z u V j hwindow.1 hρ hρ₂ hj
    hP.1 hP.2 hb hw hwz hV (hu.trans (by simpa only [one_mul] using hscaleH.2))
    (hVF.trans (by simpa only [one_mul] using hscaleF.2)) hsize W D₀ hW hWi hWd hD₀
    v e hv hnc (hNv.trans (by simpa only [one_mul] using hscaleA.2)) he hNe
    j₀ k h Z Q early
  apply hh.trans_eq
  rw [prime_parameter_log_saving hLp]
  ring

end CubicFirstMoment

end

end OAI
