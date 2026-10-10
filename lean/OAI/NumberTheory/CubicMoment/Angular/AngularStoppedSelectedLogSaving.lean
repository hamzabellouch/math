import OAI.NumberTheory.CubicMoment.Angular.AngularKummerAlgebra
import OAI.NumberTheory.CubicMoment.Angular.AngularStoppedSelectedDistinguished
import OAI.NumberTheory.CubicMoment.Decomposition.StoppedSelectedLogSaving
import OAI.NumberTheory.CubicMoment.Decomposition.StoppedSelectedDistinguished
import OAI.NumberTheory.CubicMoment.Decomposition.StoppedPrimeScale

namespace OAI

/-! The selected-divisor role has the same log-X saving as the
distinguished role, for the literal stopped coefficient. -/
noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem angular_stoppedBeta_selected_log_saving (m : ℕ)
    (hEF : AngularKummerPrimeExplicitEstimate)
    (ℓ : ℤ) (hℓ : ℓ ≠ 0) {A D H E C ξ : ℝ}
    (hA : 0 < A) (hD : 0 < D) (hH : 0 ≤ H)
    (hξ : 0 < ξ) (hgap : C < ξ*m) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ X : ℝ in atTop,
      ∀ (B ρ a b z u : ℝ) (j : ℕ),
      1 < ρ → ρ ≤ 2 → j < geometricBinCount ρ B →
      Real.exp (Real.sqrt (Real.log X))/2 ≤ geometricBinLower ρ B j →
      b ≤ B → 0 ≤ b → b ≤ X^C → X^ξ ≤ z → |u| ≤ (Real.log X)^H →
      ∀ W : ι → ℝ → ℂ, (∀ l x, ‖W l x‖ ≤ 1) →
      ∀ v e : Eisenstein, v ≠ 0 → (¬∃ n : Eisenstein, n^3 = v) →
      norm v ≤ (Real.log X)^A → e ≠ 0 → norm e ≤ X^E →
      ∀ (j₀ k h : ℕ) (Z Q : ℝ) (early : Bool),
      ‖∑ n ∈ primaryPairSupport (orderedConvolutionSupport (fun _ : ι => primeCutoff B))
          (primaryElementBall B),
        stoppedBeta (orderedConvolutionSupport (fun _ : ι => primeCutoff B)) (primaryElementBall B)
          (distinguishedTupleCoefficient (fun _ : ι => primeCutoff B)
            (fun l p => W l (norm p)) primeDetectorCutoff (X^ξ) z) primeDetectorCutoff (X^ξ)
          (stoppedSelectedTest B ρ j j₀ k h Z Q early) n *
        (if Squarefree n ∧ IsCoprime n e ∧ a < norm n ∧ norm n ≤ b
          then normTwist u n*angularCubicSymbol ℓ n v else 0)‖ ≤ K*b/(Real.log X)^D := by
  obtain ⟨K,P₀,hK,hP₀,hbound⟩ := angular_stoppedBeta_selected_distinguished_saving (ι := ι) m hEF ℓ hℓ
    (A := A+1) (D := D) (H := H+1) (E := 2)
    (by linarith) hD (by linarith) (by norm_num)
  refine ⟨K*4^D,by positivity,?_⟩
  filter_upwards [long_prime_logarithmic_window hP₀,
    eventually_log_parameter_power 1 A,eventually_log_parameter_power 1 H,
    eventually_log_parameter_power (C+E) 1,eventually_gt_atTop (1:ℝ)] with
      X hwindow hscaleA hscaleH hscaleE hX
  intro B ρ a b z u j hρ hρ₂ hj hPlong hbB hb hbX hwz hu W hW
    v e hv hnc hNv he heX j₀ k h Z Q early
  have hXp : 0 < X := zero_lt_one.trans hX
  have hLp : 0 < Real.log X := Real.log_pos hX
  have hP := hwindow.2 _ hPlong
  have hw : 1 ≤ X^ξ := Real.one_le_rpow hX.le hξ.le
  have hsize : b/geometricBinLower ρ B j < (X^ξ)^m :=
    stopped_complement_power_bound hX hgap hb hbX (geometricBinLower_gt_one hρ hj).le
  have hNe (t : Eisenstein × Eisenstein)
      (ht : t ∈ orderedConvolutionSupport (fun _ : ι => primeCutoff B) ×ˢ primaryElementBall B)
      (_hs : Squarefree (t.1*t.2)) (hn : norm (t.1*t.2) ≤ b/geometricBinLower ρ B j) :
      Real.log (norm (t.2*(t.1*e))) ≤ (Real.log X/4)^(2:ℝ) := by
    obtain ⟨hr,hd⟩ := Finset.mem_product.mp ht
    have hprod := orderedPrimarySupport_primary (fun _ : ι => primeCutoff B)
      (fun _ _ hp => (mem_primeCutoff.mp hp).1.1) hr
    have heq : t.2*(t.1*e) = t.1*(t.2*e) := by ring
    rw [heq]
    apply (stopped_complement_exclusion_log hprod (mem_primaryElementBall.mp hd).1 he hXp
      hb hbX (geometricBinLower_gt_one hρ hj).le hn heX).trans
    simpa only [Real.rpow_one,show (1:ℝ)+1=2 by norm_num] using hscaleE.2
  have hh := hbound (Real.log X/4) B ρ a b (X^ξ) z u j hwindow.1 hρ hρ₂ hj hP.1 hP.2
    hbB hb hw hwz (hu.trans (by simpa only [one_mul] using hscaleH.2)) hsize W hW
    v e hv hnc (hNv.trans (by simpa only [one_mul] using hscaleA.2)) he hNe
    j₀ k h Z Q early
  apply hh.trans_eq
  rw [prime_parameter_log_saving hLp]
  ring

end CubicFirstMoment

end

end OAI
