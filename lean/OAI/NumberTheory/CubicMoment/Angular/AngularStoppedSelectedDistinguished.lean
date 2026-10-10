import OAI.NumberTheory.CubicMoment.Angular.AngularKummerAlgebra
import OAI.NumberTheory.CubicMoment.Angular.AngularStoppedSelectedBeta
import OAI.NumberTheory.CubicMoment.Angular.AngularStoppedSelectedMoment
import OAI.NumberTheory.CubicMoment.Decomposition.StoppedSelectedDistinguished
import OAI.NumberTheory.CubicMoment.Decomposition.StoppedSelectedBeta
import OAI.NumberTheory.CubicMoment.Decomposition.DistinguishedRoughness
import OAI.NumberTheory.CubicMoment.Estimates.PrimaryConvolutionEnergy

namespace OAI

/-! The selected-divisor role with the actual distinguished-tuple
coefficient. Its roughness and coefficient bound are proved internally. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem angular_stoppedBeta_selected_distinguished_saving (m : ℕ)
    (hEF : AngularKummerPrimeExplicitEstimate)
    (ℓ : ℤ) (hℓ : ℓ ≠ 0) {A D H E : ℝ}
    (hA : 0 < A) (hD : 0 < D) (hH : 0 ≤ H) (hE : 0 ≤ E) :
    ∃ K P₀ : ℝ, 0 < K ∧ 1 < P₀ ∧ ∀ (T B ρ a b w z u : ℝ) (j : ℕ),
      1 ≤ T → 1 < ρ → ρ ≤ 2 → j < geometricBinCount ρ B →
      P₀ ≤ geometricBinLower ρ B j → T ≤ (Real.log (geometricBinLower ρ B j))^2 →
      b ≤ B → 0 ≤ b → 1 ≤ w → w ≤ z → |u| ≤ T^H →
      b/geometricBinLower ρ B j < w^m →
      ∀ W : ι → ℝ → ℂ, (∀ l x, ‖W l x‖ ≤ 1) →
      ∀ v e : Eisenstein, v ≠ 0 → (¬∃ n : Eisenstein, n^3 = v) → norm v ≤ T^A → e ≠ 0 →
      (∀ t ∈ orderedConvolutionSupport (fun _ : ι => primeCutoff B) ×ˢ primaryElementBall B,
        Squarefree (t.1*t.2) → norm (t.1*t.2) ≤ b/geometricBinLower ρ B j →
        Real.log (norm (t.2*(t.1*e))) ≤ T^E) →
      ∀ (j₀ k h : ℕ) (Z Q : ℝ) (early : Bool),
      ‖∑ n ∈ primaryPairSupport (orderedConvolutionSupport (fun _ : ι => primeCutoff B))
          (primaryElementBall B),
        stoppedBeta (orderedConvolutionSupport (fun _ : ι => primeCutoff B)) (primaryElementBall B)
          (distinguishedTupleCoefficient (fun _ : ι => primeCutoff B)
            (fun l p => W l (norm p)) primeDetectorCutoff w z) primeDetectorCutoff w
          (stoppedSelectedTest B ρ j j₀ k h Z Q early) n *
        (if Squarefree n ∧ IsCoprime n e ∧ a < norm n ∧ norm n ≤ b
          then normTwist u n*angularCubicSymbol ℓ n v else 0)‖ ≤ K*b/T^D := by
  obtain ⟨K,P₀,hK,hP₀,hbound⟩ := angular_stopped_selected_original_saving hEF ℓ hℓ hA hD hH hE
  let M : ℝ := ‖((Fintype.card ι).factorial:ℂ)⁻¹‖*
    ((Fintype.card ι)^(Fintype.card ι):ℕ)+1
  have hM : 0 < M := by dsimp [M]; positivity
  refine ⟨18*((2^m:ℕ)*M)*K,P₀,by positivity,hP₀,?_⟩
  intro T B ρ a b w z u j hT hρ hρ₂ hj hP hTP hbB hb hw hwz hu hsize W hW
    v e hv hnc hNv he hNe j₀ k h Z Q early
  let S := fun _ : ι => primeCutoff B
  let R := orderedConvolutionSupport S
  let f := distinguishedTupleCoefficient S (fun l p => W l (norm p)) primeDetectorCutoff w z
  have hS : ∀ l, ∀ p ∈ S l, primaryPrime p := fun _ _ hp => (mem_primeCutoff.mp hp).1
  have hR : ∀ r ∈ R, primary r := fun _ hr =>
    orderedPrimarySupport_primary S (fun l p hp => (hS l p hp).1) hr
  have hf : ∀ r ∈ R, ‖f r‖ ≤ M := by
    intro r _
    apply (distinguishedTupleCoefficient_norm S hS (fun l p => W l (norm p))
      (fun l p _ => hW l _) (fun x => ⟨primeDetectorCutoff_nonneg x,primeDetectorCutoff_le_one x⟩)
      w z r).trans
    dsimp [M]
    linarith
  let R₁ := R.filter (fun r => f r ≠ 0)
  have hR₁ : ∀ r ∈ R₁, primary r := fun r hr => hR r (Finset.mem_filter.mp hr).1
  have hrough : ∀ r ∈ R₁, ∀ p ∈ primaryPrimeFactors r, w ≤ norm p := by
    intro r hr p hp
    have hp' := primaryPrimeFactor_spec (hR₁ r hr) hp
    exact (distinguishedTupleCoefficient_prime_support S hS (fun l p => W l (norm p))
      (fun _ _ hx => primeDetectorCutoff_one hx) (fun _ hx => primeDetectorCutoff_zero hx)
      (zero_lt_one.trans_le hw) hwz (Finset.mem_filter.mp hr).2 hp'.1 hp'.2).1.le
  have heq : (∑ r ∈ R, f r*∑ d ∈ selectedStoppedDivisorSet B ρ a b j j₀ k h Z Q early r e,
      cutoffMoebius primeDetectorCutoff w d*normTwist u (r*d)*angularCubicSymbol ℓ (r*d) v) =
    ∑ r ∈ R₁, f r*∑ d ∈ selectedStoppedDivisorSet B ρ a b j j₀ k h Z Q early r e,
      cutoffMoebius primeDetectorCutoff w d*normTwist u (r*d)*angularCubicSymbol ℓ (r*d) v := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro r hr
    by_cases hz : f r = 0 <;> simp only [hz,ne_eq,not_true_eq_false,not_false_eq_true,
      ite_false,ite_true,zero_mul]
  rw [angular_stoppedBeta_selected_identity ℓ hj Z Q early R hR f v e,heq]
  exact hbound T B ρ a b w u j hT hρ hρ₂ hj hP hTP hbB hb hw hu R₁ f M m hR₁ hM.le
    (fun r hr => hf r (Finset.mem_filter.mp hr).1) hrough hsize v e hv hnc hNv he
    (by
      intro t ht
      obtain ⟨ht,hs,hn⟩ := Finset.mem_filter.mp ht
      obtain ⟨hr,hd⟩ := Finset.mem_product.mp ht
      exact hNe t (Finset.mem_product.mpr ⟨(Finset.mem_filter.mp hr).1,hd⟩) hs hn)
    j₀ k h Z Q early

end CubicFirstMoment

end

end OAI
