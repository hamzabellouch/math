import OAI.NumberTheory.CubicMoment.Angular.AngularKummerAlgebra
import OAI.NumberTheory.CubicMoment.Angular.AngularLongDistinguishedPrime
import OAI.NumberTheory.CubicMoment.Estimates.LongDistinguishedPrime
import OAI.NumberTheory.CubicMoment.Estimates.PrimeExclusionLog
import OAI.NumberTheory.CubicMoment.Estimates.LongPrimePowers

namespace OAI

/-! Exclusion and arbitrary logarithmic saving for the actual smooth
weight of a distinguished free prime. The bounds retain the derivative
cost and are uniform in the two detector scales. -/
noncomputable section
open Filter
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem angular_long_distinguished_prime_excluded_bound (hEF : AngularKummerPrimeExplicitEstimate)
    (ℓ : ℤ) (hℓ : ℓ ≠ 0)
    {A D : ℝ} (hA : 0 < A) (hD : 0 < D) :
    ∃ K P₀ : ℝ, 0 < K ∧ 1 < P₀ ∧ ∀ (T P a b w z u M V : ℝ),
      1 ≤ T → P₀ ≤ P → T ≤ (Real.log P)^2 →
      P ≤ a → a ≤ b → b ≤ 2*P → 0 < w → 0 < z → 0 ≤ M → 0 ≤ V →
      ∀ W : ℝ → ℂ, ContDiff ℝ ∞ W →
      (∀ x, ‖W x‖ ≤ M) → (∀ x, 0 < x → ‖deriv W x‖*x ≤ V) →
      ∀ v e : Eisenstein, v ≠ 0 → (¬∃ j : Eisenstein, j^3 = v) →
      norm v ≤ T^A → e ≠ 0 →
      ‖∑ p ∈ ((primeCutoff b).filter (fun p => a < norm p)).filter
          (fun p => IsCoprime p e),
        distinguishedRadialWeight W w z (norm p)*mellinPhase u (norm p)*angularCubicSymbol ℓ p v‖ ≤
        K*P/T^D*((M+V)*(1+|u|))+M*(Real.log (norm e)/Real.log 2) := by
  obtain ⟨K,P₀,hK,hP₀,hbound⟩ := angular_long_distinguished_prime_bound hEF ℓ hℓ hA hD
  refine ⟨K,P₀,hK,hP₀,?_⟩
  intro T P a b w z u M V hT hP hTP ha hab hb hw hz hM hV W hW hWn hWd v e hv hnc hNv he
  let S := (primeCutoff b).filter (fun p => a < norm p)
  let f := fun p : Eisenstein =>
    distinguishedRadialWeight W w z (norm p)*mellinPhase u (norm p)*angularCubicSymbol ℓ p v
  have hS (p : Eisenstein) (hp : p ∈ S) : primaryPrime p :=
    (mem_primeCutoff.mp (Finset.mem_filter.mp hp).1).1
  have hf (p : Eisenstein) (hp : p ∈ S) : ‖f p‖ ≤ M := by
    dsimp [f,distinguishedRadialWeight]
    rw [norm_mul,norm_mul,norm_mul,mellinPhase_norm,mul_one]
    have hfirst : ‖W (norm p)‖*
        ‖(primeDetectorCutoff (norm p/w):ℂ)-(primeDetectorCutoff (norm p/z):ℂ)‖ ≤ M := by
      exact (mul_le_mul (hWn _) (detector_difference_norm w z (norm p))
        (_root_.norm_nonneg _) hM).trans_eq (mul_one M)
    exact (mul_le_mul hfirst (angularCubicSymbol_norm_le_one ℓ (hS p hp).1 v)
      (_root_.norm_nonneg _) hM).trans_eq (mul_one M)
  have hex := prime_exclusion_logarithmic S hS e he f hM hf
  change ‖∑ p ∈ S with IsCoprime p e, f p‖ ≤ _
  calc
    _ ≤ ‖∑ p ∈ S, f p‖+
        ‖(∑ p ∈ S, f p)-(∑ p ∈ S with IsCoprime p e, f p)‖ :=
      norm_le_norm_add_norm_sub _ _
    _ ≤ K*P/T^D*((M+V)*(1+|u|))+M*(Real.log (norm e)/Real.log 2) :=
      add_le_add (hbound T P a b w z u M V hT hP hTP ha hab hb hw hz hM hV W
        hW hWn hWd v hv hnc hNv) hex

theorem angular_long_distinguished_prime_saving (hEF : AngularKummerPrimeExplicitEstimate)
    (ℓ : ℤ) (hℓ : ℓ ≠ 0)
    {A D H E F : ℝ} (hA : 0 < A) (hD : 0 < D)
    (hH : 0 ≤ H) (hE : 0 ≤ E) (hF : 0 ≤ F) :
    ∃ K P₀ : ℝ, 0 < K ∧ 1 < P₀ ∧ ∀ (T P a b w z u M V : ℝ),
      1 ≤ T → P₀ ≤ P → T ≤ (Real.log P)^2 →
      P ≤ a → a ≤ b → b ≤ 2*P → 0 < w → 0 < z → 0 ≤ M → 0 ≤ V →
      |u| ≤ T^H → M+V ≤ T^F →
      ∀ W : ℝ → ℂ, ContDiff ℝ ∞ W →
      (∀ x, ‖W x‖ ≤ M) → (∀ x, 0 < x → ‖deriv W x‖*x ≤ V) →
      ∀ v e : Eisenstein, v ≠ 0 → (¬∃ j : Eisenstein, j^3 = v) →
      norm v ≤ T^A → e ≠ 0 → Real.log (norm e) ≤ T^E →
      ‖∑ p ∈ ((primeCutoff b).filter (fun p => a < norm p)).filter
          (fun p => IsCoprime p e),
        distinguishedRadialWeight W w z (norm p)*mellinPhase u (norm p)*angularCubicSymbol ℓ p v‖ ≤
        K*P/T^D := by
  obtain ⟨K,P₀,hK,hP₀,hbound⟩ := angular_long_distinguished_prime_excluded_bound hEF ℓ hℓ hA
    (add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg hD hF) hH)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨P₁,hP₁⟩ := eventually_atTop.mp
    (long_prime_power_absorption (C := (Real.log 2)⁻¹) (D := D) (E := F+E)
      (inv_nonneg.mpr hlog2.le) hD.le (add_nonneg hF hE))
  refine ⟨2*K+1,max P₀ P₁,by positivity,lt_of_lt_of_le hP₀ (le_max_left _ _),?_⟩
  intro T P a b w z u M V hT hP hTP ha hab hb hw hz hM hV hu hMV W hW hWn hWd
    v e hv hnc hNv he hNe
  have hT0 : 0 < T := zero_lt_one.trans_le hT
  have hP0 : 0 < P := zero_lt_one.trans (hP₀.trans_le ((le_max_left _ _).trans hP))
  have hheight : 1+|u| ≤ 2*T^H := by
    linarith [Real.one_le_rpow hT hH]
  have hMbound : M ≤ T^F := (le_add_of_nonneg_right hV).trans hMV
  have hmain : K*P/T^(D+F+H)*((M+V)*(1+|u|)) ≤ 2*K*P/T^D := by
    calc
      _ ≤ K*P/T^(D+F+H)*(T^F*(2*T^H)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul hMV hheight
          (by positivity) (Real.rpow_nonneg hT0.le _)) (by positivity)
      _ = _ := by
        rw [Real.rpow_add hT0,Real.rpow_add hT0]
        field_simp
  have herror : M*(Real.log (norm e)/Real.log 2) ≤ P/T^D := by
    calc
      _ ≤ T^F*(T^E/Real.log 2) := mul_le_mul hMbound
        ((div_le_div_iff_of_pos_right hlog2).mpr hNe)
        (div_nonneg (Real.log_nonneg (one_le_norm he)) hlog2.le)
        (Real.rpow_nonneg hT0.le _)
      _ = (Real.log 2)⁻¹*T^(F+E) := by rw [Real.rpow_add hT0]; ring
      _ ≤ _ := hP₁ P ((le_max_right _ _).trans hP) T hT hTP
  apply (hbound T P a b w z u M V hT ((le_max_left _ _).trans hP) hTP ha hab hb
    hw hz hM hV W hW hWn hWd v e hv hnc hNv he).trans
  calc
    _ ≤ 2*K*P/T^D+P/T^D := add_le_add hmain herror
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
