import OAI.NumberTheory.CubicMoment.Angular.AngularKummerAlgebra
import OAI.NumberTheory.CubicMoment.Angular.AngularLongPrimeSW
import OAI.NumberTheory.CubicMoment.Estimates.LongPrimeWeights
import OAI.NumberTheory.CubicMoment.Estimates.PrimeExclusionLog

namespace OAI

/-! A concrete free selected-bin prime satisfies the needed prime
cancellation, uniformly in its cutoff scale and interval endpoints. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem angular_long_prime_cutoff_bound (hEF : AngularKummerPrimeExplicitEstimate)
    (ℓ : ℤ) (hℓ : ℓ ≠ 0)
    {A D : ℝ} (hA : 0 < A) (hD : 0 < D) :
    ∃ C P₀ : ℝ, 0 < C ∧ 1 < P₀ ∧ ∀ (T P a b c u : ℝ),
      1 ≤ T → P₀ ≤ P → T ≤ (Real.log P)^2 →
      P ≤ a → a ≤ b → b ≤ 2*P → 0 < c →
      ∀ v : Eisenstein, v ≠ 0 → (¬∃ j : Eisenstein, j^3 = v) → norm v ≤ T^A →
      ‖∑ p ∈ (primeCutoff b).filter (fun p => a < norm p),
        (primeDetectorCutoff (norm p/c):ℂ)*mellinPhase u (norm p)*angularCubicSymbol ℓ p v‖ ≤
        C*P/T^D*(1+|u|) := by
  obtain ⟨C,P₀,hC,hP₀,hbound⟩ := angular_long_prime_interval_bound hEF ℓ hℓ hA hD
  obtain ⟨V,hV,hvar⟩ := long_prime_cutoff_variation
  refine ⟨2*C*(V+2),P₀,by positivity,hP₀,?_⟩
  intro T P a b c u hT hP hTP ha hab hb hc v hv hnc hNv
  have hP0 : 0 < P := zero_lt_one.trans (hP₀.trans_le hP)
  obtain ⟨hdiff,hint,hvariation⟩ := hvar c P 2 a b u hc hP0 (by norm_num) ha hab hb
  have hVbound : 2+(2-1)*(V+|u|) ≤ (V+2)*(1+|u|) := by
    nlinarith [abs_nonneg u,mul_nonneg hV (abs_nonneg u)]
  have hf : 0 ≤ C*(2*P)/T^D := by positivity
  calc
    _ ≤ (C*(2*P)/T^D)*(2+(2-1)*(V+|u|)) :=
      (hbound T P 2 a b hT hP hTP ha hab hb v hv hnc hNv _ hdiff hint).trans
        (mul_le_mul_of_nonneg_left hvariation hf)
    _ ≤ (C*(2*P)/T^D)*((V+2)*(1+|u|)) := mul_le_mul_of_nonneg_left hVbound hf
    _ = _ := by ring

/-- The exact logarithmic deletion error is retained, so this theorem
also applies to the polynomial-norm exclusions in the stopped sequence. -/
theorem angular_long_prime_cutoff_excluded_bound (hEF : AngularKummerPrimeExplicitEstimate)
    (ℓ : ℤ) (hℓ : ℓ ≠ 0)
    {A D : ℝ} (hA : 0 < A) (hD : 0 < D) :
    ∃ C P₀ : ℝ, 0 < C ∧ 1 < P₀ ∧ ∀ (T P a b c u : ℝ),
      1 ≤ T → P₀ ≤ P → T ≤ (Real.log P)^2 →
      P ≤ a → a ≤ b → b ≤ 2*P → 0 < c →
      ∀ v e : Eisenstein, v ≠ 0 → (¬∃ j : Eisenstein, j^3 = v) → norm v ≤ T^A → e ≠ 0 →
      ‖∑ p ∈ ((primeCutoff b).filter (fun p => a < norm p)).filter (fun p => IsCoprime p e),
        (primeDetectorCutoff (norm p/c):ℂ)*mellinPhase u (norm p)*angularCubicSymbol ℓ p v‖ ≤
        C*P/T^D*(1+|u|)+Real.log (norm e)/Real.log 2 := by
  obtain ⟨C,P₀,hC,hP₀,hbound⟩ := angular_long_prime_cutoff_bound hEF ℓ hℓ hA hD
  refine ⟨C,P₀,hC,hP₀,?_⟩
  intro T P a b c u hT hP hTP ha hab hb hc v e hv hnc hNv he
  let S := (primeCutoff b).filter (fun p => a < norm p)
  let f := fun p : Eisenstein =>
    (primeDetectorCutoff (norm p/c):ℂ)*mellinPhase u (norm p)*angularCubicSymbol ℓ p v
  have hS (p : Eisenstein) (hp : p ∈ S) : primaryPrime p :=
    (mem_primeCutoff.mp (Finset.mem_filter.mp hp).1).1
  have hweight (p : Eisenstein) (hp : p ∈ S) : ‖f p‖ ≤ 1 := by
    dsimp [f]
    rw [norm_mul,norm_mul,mellinPhase_norm,mul_one]
    exact (mul_le_mul (primeDetectorCutoff_rescaled_norm c (norm p))
      (angularCubicSymbol_norm_le_one ℓ (hS p hp).1 v) (_root_.norm_nonneg _) zero_le_one).trans_eq
      (one_mul 1)
  have herr := prime_exclusion_logarithmic S hS e he f zero_le_one hweight
  have hnorm : ‖∑ p ∈ S with IsCoprime p e, f p‖ ≤
      ‖∑ p ∈ S, f p‖+‖(∑ p ∈ S, f p)-(∑ p ∈ S with IsCoprime p e, f p)‖ := by
    simpa only [sub_sub_cancel] using norm_sub_le (∑ p ∈ S, f p)
      ((∑ p ∈ S, f p)-(∑ p ∈ S with IsCoprime p e, f p))
  exact hnorm.trans (add_le_add (hbound T P a b c u hT hP hTP ha hab hb hc v hv hnc hNv)
    (by simpa only [one_mul] using herr))

end CubicFirstMoment

end

end OAI
