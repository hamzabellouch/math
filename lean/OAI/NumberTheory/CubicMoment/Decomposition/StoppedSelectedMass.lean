import OAI.NumberTheory.CubicMoment.Decomposition.StoppedSelectedRow
import OAI.NumberTheory.CubicMoment.Decomposition.StoppedComplementMass

namespace OAI

/-! Summing the actual selected-prime rows over complementary products.
The linear complementary mass is proved from roughness; it is not a
Siegel--Walfisz hypothesis about the collected coefficient. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem stopped_selected_prime_mass_saving (hSW : KummerPrimeSiegelWalfisz)
    {A D H E : ℝ} (hA : 0 < A) (hD : 0 < D) (hH : 0 ≤ H) (hE : 0 ≤ E) :
    ∃ K P₀ : ℝ, 0 < K ∧ 1 < P₀ ∧ ∀ (T B ρ w u : ℝ) (j : ℕ),
      1 ≤ T → 1 < ρ → ρ ≤ 2 → j < geometricBinCount ρ B →
      P₀ ≤ geometricBinLower ρ B j → T ≤ (Real.log (geometricBinLower ρ B j))^2 →
      1 ≤ w → |u| ≤ T^H →
      ∀ (R S : Finset Eisenstein) (f : Eisenstein → ℂ) (M Y : ℝ) (m : ℕ),
      (∀ r ∈ R, primary r) → (∀ c ∈ S, primary c) → 0 ≤ M → 0 ≤ Y →
      (∀ r ∈ R, ‖f r‖ ≤ M) →
      (∀ r ∈ R, ∀ p ∈ primaryPrimeFactors r, w ≤ norm p) → Y < w^m →
      ∀ v e : Eisenstein, v ≠ 0 → (¬∃ k : Eisenstein, k^3 = v) → norm v ≤ T^A → e ≠ 0 →
      (∀ t ∈ (R ×ˢ S).filter (fun t => Squarefree (t.1*t.2) ∧ norm (t.1*t.2) ≤ Y),
        Real.log (norm (t.2*(t.1*e))) ≤ T^E) →
      ∀ (a b : Eisenstein × Eisenstein → ℝ) (j₀ k h : ℕ) (Z Q : ℝ) (early : Bool),
      ‖∑ t ∈ (R ×ˢ S).filter (fun t => Squarefree (t.1*t.2) ∧ norm (t.1*t.2) ≤ Y),
        f t.1*stoppedSelectedPrimeRow B ρ (a t) (b t) w u j j₀ k h Z Q early t.1 t.2 v e‖ ≤
        (18*Y*((2^m:ℕ)*M))*(K*geometricBinLower ρ B j/T^D) := by
  obtain ⟨K,P₀,hK,hP₀,hbound⟩ := stopped_selected_prime_row_saving hSW hA hD hH hE
  refine ⟨K,P₀,hK,hP₀,?_⟩
  intro T B ρ w u j hT hρ hρ₂ hj hP hTP hw hu R S f M Y m hR hS hM hY hf hrough hsize
    v e hv hnc hNv he hlog a b j₀ k h Z Q early
  let U := (R ×ˢ S).filter (fun t => Squarefree (t.1*t.2) ∧ norm (t.1*t.2) ≤ Y)
  have hP0 : 0 < geometricBinLower ρ B j := zero_lt_one.trans (hP₀.trans_le hP)
  have hcost : 0 ≤ K*geometricBinLower ρ B j/T^D := by positivity
  have hrow (t : Eisenstein × Eisenstein) (ht : t ∈ U) :
      ‖stoppedSelectedPrimeRow B ρ (a t) (b t) w u j j₀ k h Z Q early t.1 t.2 v e‖ ≤
        K*geometricBinLower ρ B j/T^D := by
    obtain ⟨ht,hprop⟩ := Finset.mem_filter.mp ht
    obtain ⟨hr,hc⟩ := Finset.mem_product.mp ht
    exact hbound T B ρ (a t) (b t) w u j hT hρ hρ₂ hj hP hTP (zero_lt_one.trans_le hw) hu
      t.1 t.2 v e (hR _ hr) (hS _ hc) (squarefree_mul_iff.mp hprop.1).2.2
      hv hnc hNv he (hlog t (Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hr,hc⟩,hprop⟩))
      j₀ k h Z Q early
  change ‖∑ t ∈ U, f t.1*stoppedSelectedPrimeRow B ρ (a t) (b t) w u j j₀ k h Z Q early t.1 t.2 v e‖ ≤ _
  calc
    _ ≤ ∑ t ∈ U, ‖f t.1*stoppedSelectedPrimeRow B ρ (a t) (b t) w u j j₀ k h Z Q early t.1 t.2 v e‖ :=
      norm_sum_le _ _
    _ ≤ ∑ t ∈ U, ‖f t.1‖*(K*geometricBinLower ρ B j/T^D) := by
      apply Finset.sum_le_sum
      intro t ht
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hrow t ht) (_root_.norm_nonneg _)
    _ = (∑ t ∈ U, ‖f t.1‖)*(K*geometricBinLower ρ B j/T^D) := (Finset.sum_mul _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (stopped_complement_mass R S hR hS f hM hY hf hw hrough hsize) hcost

end CubicFirstMoment

end

end OAI
