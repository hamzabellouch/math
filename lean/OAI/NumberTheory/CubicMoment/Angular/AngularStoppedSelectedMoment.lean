import OAI.NumberTheory.CubicMoment.Angular.AngularKummerAlgebra
import OAI.NumberTheory.CubicMoment.Angular.AngularStoppedSelectedCollection
import OAI.NumberTheory.CubicMoment.Angular.AngularStoppedSelectedRow
import OAI.NumberTheory.CubicMoment.Decomposition.StoppedSelectedMoment
import OAI.NumberTheory.CubicMoment.Decomposition.StoppedSelectedCollection
import OAI.NumberTheory.CubicMoment.Decomposition.StoppedSelectedMass

namespace OAI

/-! Original selected-side stopped sums, after their exact free-prime
reindexing. The complementary cutoff is derived from the actual bin. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem angular_selectedStopped_original_collection (ℓ : ℤ) {B ρ a b w u : ℝ}
    (hρ : 1 < ρ) (hρ₂ : ρ ≤ 2) {j j₀ k h : ℕ}
    (hj : j < geometricBinCount ρ B) (Z Q : ℝ) (early : Bool)
    (R : Finset Eisenstein) (hR : ∀ r ∈ R, primary r)
    (f : Eisenstein → ℂ) (v e : Eisenstein) (hbB : b ≤ B) :
    (∑ r ∈ R, f r*∑ d ∈ selectedStoppedDivisorSet B ρ a b j j₀ k h Z Q early r e,
      cutoffMoebius primeDetectorCutoff w d*normTwist u (r*d)*angularCubicSymbol ℓ (r*d) v) =
      ∑ t ∈ (R ×ˢ primaryElementBall B).filter
        (fun t => Squarefree (t.1*t.2) ∧ norm (t.1*t.2) ≤ b/geometricBinLower ρ B j),
        if IsCoprime (t.1*t.2) e then f t.1*
          angular_stoppedSelectedPrimeRow ℓ B ρ (a/norm (t.1*t.2)) (b/norm (t.1*t.2)) w u
            j j₀ k h Z Q early t.1 t.2 v e else 0 := by
  rw [Finset.sum_filter,Finset.sum_product]
  apply Finset.sum_congr rfl
  intro r hr
  rw [angular_selectedStopped_original_rows ℓ B ρ a b w u j j₀ k h Z Q early r v e (hR r hr) hbB,
    Finset.mul_sum,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro c hc
  have hc' := (mem_primaryElementBall.mp hc).1
  by_cases hs : Squarefree (r*c)
  · by_cases he : IsCoprime (r*c) e
    · by_cases hn : norm (r*c) ≤ b/geometricBinLower ρ B j
      · simp only [hs,he,hn,and_self,ite_true]
      · have hz := angular_selectedStopped_row_eq_zero ℓ hρ hρ₂ hj (hR r hr) hc'
          (lt_of_not_ge hn) (v := v) (e := e) (a := a) (w := w) (u := u)
          (j₀ := j₀) (k := k) (h := h) (Z := Z) (Q := Q) (early := early)
        simp only [hs,he,hn,and_false,ite_false,and_true,ite_true,hz,mul_zero]
    · simp only [hs,he,and_false,ite_false]
      split_ifs <;> rfl
  · simp only [hs,false_and,ite_false]


theorem angular_stopped_selected_original_saving (hEF : AngularKummerPrimeExplicitEstimate)
    (ℓ : ℤ) (hℓ : ℓ ≠ 0)
    {A D H E : ℝ} (hA : 0 < A) (hD : 0 < D) (hH : 0 ≤ H) (hE : 0 ≤ E) :
    ∃ K P₀ : ℝ, 0 < K ∧ 1 < P₀ ∧ ∀ (T B ρ a b w u : ℝ) (j : ℕ),
      1 ≤ T → 1 < ρ → ρ ≤ 2 → j < geometricBinCount ρ B →
      P₀ ≤ geometricBinLower ρ B j → T ≤ (Real.log (geometricBinLower ρ B j))^2 →
      b ≤ B → 0 ≤ b → 1 ≤ w → |u| ≤ T^H →
      ∀ (R : Finset Eisenstein) (f : Eisenstein → ℂ) (M : ℝ) (m : ℕ),
      (∀ r ∈ R, primary r) → 0 ≤ M → (∀ r ∈ R, ‖f r‖ ≤ M) →
      (∀ r ∈ R, ∀ p ∈ primaryPrimeFactors r, w ≤ norm p) →
      b/geometricBinLower ρ B j < w^m →
      ∀ v e : Eisenstein, v ≠ 0 → (¬∃ n : Eisenstein, n^3 = v) → norm v ≤ T^A → e ≠ 0 →
      (∀ t ∈ (R ×ˢ primaryElementBall B).filter
        (fun t => Squarefree (t.1*t.2) ∧ norm (t.1*t.2) ≤ b/geometricBinLower ρ B j),
        Real.log (norm (t.2*(t.1*e))) ≤ T^E) →
      ∀ (j₀ k h : ℕ) (Z Q : ℝ) (early : Bool),
      ‖∑ r ∈ R, f r*∑ d ∈ selectedStoppedDivisorSet B ρ a b j j₀ k h Z Q early r e,
        cutoffMoebius primeDetectorCutoff w d*normTwist u (r*d)*angularCubicSymbol ℓ (r*d) v‖ ≤
        (18*((2^m:ℕ)*M)*K)*b/T^D := by
  obtain ⟨K,P₀,hK,hP₀,hrow⟩ := angular_stopped_selected_prime_row_saving hEF ℓ hℓ hA hD hH hE
  refine ⟨K,P₀,hK,hP₀,?_⟩
  intro T B ρ a b w u j hT hρ hρ₂ hj hP hTP hbB hb hw hu R f M m hR hM hf hrough hsize
    v e hv hnc hNv he hlog j₀ k h Z Q early
  have hPpos : 0 < geometricBinLower ρ B j := zero_lt_one.trans (hP₀.trans_le hP)
  let U := (R ×ˢ primaryElementBall B).filter
    (fun t => Squarefree (t.1*t.2) ∧ norm (t.1*t.2) ≤ b/geometricBinLower ρ B j)
  let C := K*geometricBinLower ρ B j/T^D
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hbound (t : Eisenstein × Eisenstein) (ht : t ∈ U) :
      ‖if IsCoprime (t.1*t.2) e then f t.1*
          angular_stoppedSelectedPrimeRow ℓ B ρ (a/norm (t.1*t.2)) (b/norm (t.1*t.2)) w u
            j j₀ k h Z Q early t.1 t.2 v e else 0‖ ≤ ‖f t.1‖*C := by
    by_cases hcop : IsCoprime (t.1*t.2) e
    · rw [ite_eq_left hcop,norm_mul]
      obtain ⟨ht,hprop⟩ := Finset.mem_filter.mp ht
      obtain ⟨hr,hc⟩ := Finset.mem_product.mp ht
      exact mul_le_mul_of_nonneg_left
        (hrow T B ρ _ _ w u j hT hρ hρ₂ hj hP hTP (zero_lt_one.trans_le hw) hu
          t.1 t.2 v e (hR _ hr) (mem_primaryElementBall.mp hc).1
          (squarefree_mul_iff.mp hprop.1).2.2 hv hnc hNv he
          (hlog t (Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hr,hc⟩,hprop⟩))
          j₀ k h Z Q early) (_root_.norm_nonneg _)
    · rw [ite_eq_right hcop,norm_zero]
      exact mul_nonneg (_root_.norm_nonneg _) hC
  rw [angular_selectedStopped_original_collection ℓ hρ hρ₂ hj Z Q early R hR f v e hbB]
  change ‖∑ t ∈ U, _‖ ≤ _
  calc
    _ ≤ ∑ t ∈ U, ‖if IsCoprime (t.1*t.2) e then f t.1*
        angular_stoppedSelectedPrimeRow ℓ B ρ (a/norm (t.1*t.2)) (b/norm (t.1*t.2)) w u
          j j₀ k h Z Q early t.1 t.2 v e else 0‖ := norm_sum_le _ _
    _ ≤ ∑ t ∈ U, ‖f t.1‖*C := Finset.sum_le_sum hbound
    _ = (∑ t ∈ U, ‖f t.1‖)*C := (Finset.sum_mul _ _ _).symm
    _ ≤ (18*(b/geometricBinLower ρ B j)*((2^m:ℕ)*M))*C :=
      mul_le_mul_of_nonneg_right
        (stopped_complement_mass R (primaryElementBall B) hR
          (fun c hc => (mem_primaryElementBall.mp hc).1) f hM
          (div_nonneg hb hPpos.le) hf hw hrough hsize) hC
    _ = _ := by
      dsimp [C]
      field_simp [ne_of_gt hPpos]

end CubicFirstMoment

end

end OAI
