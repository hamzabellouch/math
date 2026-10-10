import OAI.NumberTheory.CubicMoment.Decomposition.DistinguishedComplementMass
import OAI.NumberTheory.CubicMoment.Decomposition.DistinguishedPrimeZero

namespace OAI

/-! Summed distinguished-coordinate cancellation. The total complementary
mass is derived for the actual tuple weights and the actual norm cutoff. -/
noncomputable section
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem stopped_distinguished_rows_saving (i : ι) (m : ℕ)
    (hSW : KummerPrimeSiegelWalfisz) {A D H E F : ℝ}
    (hA : 0 < A) (hD : 0 < D) (hH : 0 ≤ H) (hE : 0 ≤ E) (hF : 0 ≤ F) :
    ∃ K P₀ : ℝ, 0 < K ∧ 1 < P₀ ∧ ∀ (T B ρ a b w z u V : ℝ) (j : ℕ),
      1 ≤ T → 1 < ρ → ρ ≤ 2 → j < geometricBinCount ρ B →
      P₀ ≤ geometricBinLower ρ B j → T ≤ (Real.log (geometricBinLower ρ B j))^2 →
      0 ≤ b → 1 ≤ w → w ≤ z → 0 ≤ V → |u| ≤ T^H → 1+V ≤ T^F →
      b/geometricBinLower ρ B j < w^m →
      ∀ (S : ι → Finset Eisenstein) (W : ι → ℝ → ℂ) (D₀ : Finset Eisenstein),
      (∀ l, ∀ p ∈ S l, primaryPrime p) → (∀ l x, ‖W l x‖ ≤ 1) →
      ContDiff ℝ ∞ (W i) → (∀ x, 0 < x → ‖deriv (W i) x‖*x ≤ V) →
      (∀ d ∈ D₀, primary d) →
      ∀ v e : Eisenstein, v ≠ 0 → (¬∃ n : Eisenstein, n^3 = v) → norm v ≤ T^A → e ≠ 0 →
      (∀ t ∈ coordinateComplementTuples S i ×ˢ D₀,
        Squarefree ((∏ l, t.1 l)*t.2) → norm ((∏ l, t.1 l)*t.2) ≤ b/geometricBinLower ρ B j →
        Real.log (norm ((∏ l, t.1 l)*(t.2*e))) ≤ T^E) →
      ∀ (j₀ k h : ℕ) (Z Q : ℝ) (early : Bool),
      ‖∑ t ∈ (coordinateComplementTuples S i ×ˢ D₀).filter
          (fun t => Squarefree ((∏ l, t.1 l)*t.2) ∧ IsCoprime ((∏ l, t.1 l)*t.2) e),
        (∏ l ∈ Finset.univ.erase i, distinguishedRadialWeight (W l) w z (norm (t.1 l)))*
        (∑ p ∈ stoppedDistinguishedPrimeSet B ρ a b j j₀ k h Z Q early
            (∏ l, t.1 l) t.2 ((∏ l, t.1 l)*(t.2*e)),
          cutoffMoebius primeDetectorCutoff w t.2*distinguishedRadialWeight (W i) w z (norm p)*
            normTwist u (((∏ l, t.1 l)*p)*t.2)*cubicSymbol (((∏ l, t.1 l)*p)*t.2) v)‖ ≤
        K*b/T^D := by
  obtain ⟨K,P₀,hK,hP₀,hbound⟩ := stopped_distinguished_full_saving hSW hA hD hH hE hF
  let C : ℝ := 18*((2^m:ℕ)*(((Fintype.card ι)^(Fintype.card ι):ℕ)+1))*K
  refine ⟨C,P₀,by dsimp [C]; positivity,hP₀,?_⟩
  intro T B ρ a b w z u V j hT hρ hρ₂ hj hP hTP hb hw hwz hV hu hVF hsize
    S W D₀ hS hW hWi hWd hD₀ v e hv hnc hNv he hNe j₀ k h Z Q early
  let P := geometricBinLower ρ B j
  let U := coordinateComplementTuples S i ×ˢ D₀
  let wt := fun t : (ι → Eisenstein) × Eisenstein =>
    ∏ l ∈ Finset.univ.erase i, distinguishedRadialWeight (W l) w z (norm (t.1 l))
  let row := fun t : (ι → Eisenstein) × Eisenstein =>
    ∑ p ∈ stoppedDistinguishedPrimeSet B ρ a b j j₀ k h Z Q early
        (∏ l, t.1 l) t.2 ((∏ l, t.1 l)*(t.2*e)),
      cutoffMoebius primeDetectorCutoff w t.2*distinguishedRadialWeight (W i) w z (norm p)*
        normTwist u (((∏ l, t.1 l)*p)*t.2)*cubicSymbol (((∏ l, t.1 l)*p)*t.2) v
  let U₁ := U.filter (fun t => Squarefree ((∏ l, t.1 l)*t.2) ∧ norm ((∏ l, t.1 l)*t.2) ≤ b/P)
  have hPpos : 0 < P := zero_lt_one.trans (geometricBinLower_gt_one hρ hj)
  have hTpos : 0 < T := zero_lt_one.trans_le hT
  have hY : 0 ≤ b/P := div_nonneg hb hPpos.le
  have hrow (t : (ι → Eisenstein) × Eisenstein) (ht : t ∈ U₁) : ‖row t‖ ≤ K*P/T^D := by
    obtain ⟨ht,hs,hn⟩ := Finset.mem_filter.mp ht
    obtain ⟨hg,hd⟩ := Finset.mem_product.mp ht
    exact hbound T B ρ a b w z u 1 V j hT hρ hρ₂ hj hP hTP
      (zero_lt_one.trans_le hw) ((zero_lt_one.trans_le hw).trans_le hwz) (by norm_num)
      hV hu hVF (W i) hWi (hW i) hWd (∏ l, t.1 l) t.2 v e
      (complementTuple_primary S hS i hg) (hD₀ t.2 hd) hv hnc hNv he (hNe t ht hs hn)
      j₀ k h Z Q early
  have heq : (∑ t ∈ U.filter (fun t => Squarefree ((∏ l, t.1 l)*t.2) ∧
        IsCoprime ((∏ l, t.1 l)*t.2) e), wt t*row t) =
      ∑ t ∈ U₁, if IsCoprime ((∏ l, t.1 l)*t.2) e then wt t*row t else 0 := by
    simp only [U₁,Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro t ht
    obtain ⟨hg,hd⟩ := Finset.mem_product.mp ht
    by_cases hs : Squarefree ((∏ l, t.1 l)*t.2)
    · by_cases hn : norm ((∏ l, t.1 l)*t.2) ≤ b/P
      · by_cases hc : IsCoprime ((∏ l, t.1 l)*t.2) e <;> simp only [hs,hn,hc,and_self,ite_true,and_false,ite_false]
      · have hz : row t = 0 := stoppedDistinguished_row_eq_zero hρ hρ₂ hj
          (complementTuple_primary S hS i hg) (hD₀ t.2 hd) (lt_of_not_ge hn) _
        simp only [hs,hn,hz,and_false,mul_zero,ite_self]
    · simp only [hs,false_and,ite_false]
  change ‖∑ t ∈ U.filter (fun t => Squarefree ((∏ l, t.1 l)*t.2) ∧
    IsCoprime ((∏ l, t.1 l)*t.2) e), wt t*row t‖ ≤ _
  rw [heq]
  calc
    _ ≤ ∑ t ∈ U₁, ‖wt t‖*(K*P/T^D) := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro t ht
      split_ifs
      · rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hrow t ht) (_root_.norm_nonneg _)
      · rw [norm_zero]
        positivity
    _ = (∑ t ∈ U₁, ‖wt t‖)*(K*P/T^D) := (Finset.sum_mul _ _ _).symm
    _ ≤ (18*(b/P)*((2^m:ℕ)*((Fintype.card ι)^(Fintype.card ι):ℕ)))*(K*P/T^D) := by
      apply mul_le_mul_of_nonneg_right ?_ (by positivity)
      simpa only [U₁,U,wt,norm_prod] using
        distinguished_complement_tuple_mass S hS i W hW D₀ hD₀ hY hw hwz hsize
    _ ≤ C*b/T^D := by
      have hmono : (((Fintype.card ι)^(Fintype.card ι):ℕ):ℝ) ≤
          (((Fintype.card ι)^(Fintype.card ι):ℕ):ℝ)+1 := by linarith
      dsimp [C]
      have hscale : (18*(b/P)*((2^m:ℕ)*((Fintype.card ι)^(Fintype.card ι):ℕ)))*(K*P/T^D) =
          (18*((2^m:ℕ)*((Fintype.card ι)^(Fintype.card ι):ℕ))*K)*b/T^D := by
        field_simp
      rw [hscale]
      gcongr

end CubicFirstMoment

end

end OAI
