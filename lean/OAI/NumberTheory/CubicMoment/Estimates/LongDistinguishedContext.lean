import OAI.NumberTheory.CubicMoment.Estimates.LongDistinguishedSaving
import OAI.NumberTheory.CubicMoment.Estimates.LargestPrimeCancellation

namespace OAI

/-! A distinguished free prime is cancelled with the actual largest-prime
tie rule relative to the entire fixed complement. -/
noncomputable section
open Filter
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem long_distinguished_context_saving (hSW : KummerPrimeSiegelWalfisz)
    {A D H E F : ℝ} (hA : 0 < A) (hD : 0 < D)
    (hH : 0 ≤ H) (hE : 0 ≤ E) (hF : 0 ≤ F) :
    ∃ K P₀ : ℝ, 0 < K ∧ 1 < P₀ ∧ ∀ (T P a b w z u M V : ℝ),
      1 ≤ T → P₀ ≤ P → T ≤ (Real.log P)^2 →
      P ≤ a → a ≤ b → b ≤ 2*P → 0 < w → 0 < z → 0 ≤ M → 0 ≤ V →
      |u| ≤ T^H → M+V ≤ T^F →
      ∀ W : ℝ → ℂ, ContDiff ℝ ∞ W →
      (∀ x, ‖W x‖ ≤ M) → (∀ x, 0 < x → ‖deriv W x‖*x ≤ V) →
      ∀ (v e : Eisenstein) (C : Finset Eisenstein), v ≠ 0 →
      (¬∃ j : Eisenstein, j^3 = v) → norm v ≤ T^A → e ≠ 0 →
      Real.log (norm e) ≤ T^E →
      ‖∑ p ∈ (((primeCutoff b).filter (fun p => a < norm p)).filter
          (fun p => IsCoprime p e)).filter (fun p => largestPrimePredicate primeTieCode C p),
        distinguishedRadialWeight W w z (norm p)*mellinPhase u (norm p)*cubicSymbol p v‖ ≤
        K*P/T^D := by
  obtain ⟨K,P₀,hK,hP₀,hbound⟩ := long_distinguished_prime_saving hSW hA hD hH hE hF
  obtain ⟨P₁,hP₁⟩ := eventually_atTop.mp
    (long_prime_power_absorption (C := 4) (D := D) (E := F)
      (by norm_num) hD.le hF)
  refine ⟨K+1,max P₀ P₁,by positivity,lt_of_lt_of_le hP₀ (le_max_left _ _),?_⟩
  intro T P a b w z u M V hT hP hTP ha hab hb hw hz hM hV hu hMV W hW hWn hWd
    v e C hv hnc hNv he hNe
  have hP0 : 0 < P := zero_lt_one.trans (hP₀.trans_le ((le_max_left _ _).trans hP))
  let S := ((primeCutoff b).filter (fun p => a < norm p)).filter (fun p => IsCoprime p e)
  let f := fun p : Eisenstein =>
    distinguishedRadialWeight W w z (norm p)*mellinPhase u (norm p)*cubicSymbol p v
  let m : ℝ := ((C.sup normNat:ℕ):ℝ)
  have hS (p : Eisenstein) (hp : p ∈ S) : primaryPrime p :=
    (mem_primeCutoff.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1).1
  have hf (p : Eisenstein) (hp : p ∈ S) : ‖f p‖ ≤ M := by
    dsimp [f,distinguishedRadialWeight]
    rw [norm_mul,norm_mul,norm_mul,mellinPhase_norm,mul_one]
    have hfirst : ‖W (norm p)‖*
        ‖(primeDetectorCutoff (norm p/w):ℂ)-(primeDetectorCutoff (norm p/z):ℂ)‖ ≤ M :=
      (mul_le_mul (hWn _) (detector_difference_norm w z (norm p))
        (_root_.norm_nonneg _) hM).trans_eq (mul_one M)
    exact (mul_le_mul hfirst (norm_cubicSymbol_le_one (hS p hp).1 v)
      (_root_.norm_nonneg _) hM).trans_eq (mul_one M)
  have hend := largestPrime_endpoint_difference primeTieCode C S hS f hM hf
  have hinterval : (∑ p ∈ S with m < norm p, f p) =
      ∑ p ∈ ((primeCutoff b).filter (fun p => max a m < norm p)).filter
        (fun p => IsCoprime p e), f p := by
    apply Finset.sum_congr _ (fun _ _ => rfl)
    ext p
    simp only [S,Finset.mem_filter,max_lt_iff]
    tauto
  have hsum : ‖∑ p ∈ S with m < norm p, f p‖ ≤ K*P/T^D := by
    rw [hinterval]
    by_cases hm : max a m ≤ b
    · exact hbound T P (max a m) b w z u M V hT ((le_max_left _ _).trans hP) hTP
        (ha.trans (le_max_left _ _)) hm hb hw hz hM hV hu hMV W hW hWn hWd
        v e hv hnc hNv he hNe
    · have hempty : ((primeCutoff b).filter (fun p => max a m < norm p)).filter
          (fun p => IsCoprime p e) = ∅ := by
        apply Finset.eq_empty_of_forall_notMem
        intro p hp
        obtain ⟨hp,_⟩ := Finset.mem_filter.mp hp
        obtain ⟨hp,hl⟩ := Finset.mem_filter.mp hp
        exact hm (hl.le.trans (mem_primeCutoff.mp hp).2)
      rw [hempty,Finset.sum_empty,norm_zero]
      positivity
  have hfour : 4*M ≤ P/T^D :=
    (mul_le_mul_of_nonneg_left ((le_add_of_nonneg_right hV).trans hMV) (by norm_num)).trans
      (hP₁ P ((le_max_right _ _).trans hP) T hT hTP)
  change ‖∑ p ∈ S with largestPrimePredicate primeTieCode C p, f p‖ ≤ _
  calc
    _ ≤ ‖∑ p ∈ S with m < norm p, f p‖+
        ‖(∑ p ∈ S with largestPrimePredicate primeTieCode C p, f p)-
          (∑ p ∈ S with m < norm p, f p)‖ := norm_le_norm_add_norm_sub' _ _
    _ ≤ K*P/T^D+4*M := add_le_add hsum hend
    _ ≤ K*P/T^D+P/T^D := add_le_add le_rfl hfour
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
