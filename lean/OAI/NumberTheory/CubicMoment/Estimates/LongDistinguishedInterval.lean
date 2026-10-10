import OAI.NumberTheory.CubicMoment.Estimates.LongDistinguishedContext
import OAI.NumberTheory.CubicMoment.Estimates.PrimeMixedInterval

namespace OAI

/-! The half-open intersections supplied by the actual stopping tests
inherit prime cancellation. Only the two final endpoint norms are lost. -/
noncomputable section
open Filter
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem long_distinguished_mixed_interval_saving (hSW : KummerPrimeSiegelWalfisz)
    {A D H E F : ℝ} (hA : 0 < A) (hD : 0 < D)
    (hH : 0 ≤ H) (hE : 0 ≤ E) (hF : 0 ≤ F) :
    ∃ K P₀ : ℝ, 0 < K ∧ 1 < P₀ ∧ ∀ (T P B a l b h w z u M V : ℝ),
      1 ≤ T → P₀ ≤ P → T ≤ (Real.log P)^2 →
      P ≤ max a l → min b h ≤ 2*P → 0 < w → 0 < z → 0 ≤ M → 0 ≤ V →
      |u| ≤ T^H → M+V ≤ T^F →
      ∀ W : ℝ → ℂ, ContDiff ℝ ∞ W →
      (∀ x, ‖W x‖ ≤ M) → (∀ x, 0 < x → ‖deriv W x‖*x ≤ V) →
      ∀ (v e : Eisenstein) (C : Finset Eisenstein), v ≠ 0 →
      (¬∃ n : Eisenstein, n^3 = v) → norm v ≤ T^A → e ≠ 0 →
      Real.log (norm e) ≤ T^E →
      ‖∑ p ∈ (((primeCutoff B).filter (fun p => IsCoprime p e)).filter
          (fun p => largestPrimePredicate primeTieCode C p)).filter
          (fun p => a < norm p ∧ l ≤ norm p ∧ norm p < b ∧ norm p ≤ h),
        distinguishedRadialWeight W w z (norm p)*mellinPhase u (norm p)*cubicSymbol p v‖ ≤
        K*P/T^D := by
  obtain ⟨K,P₀,hK,hP₀,hbound⟩ := long_distinguished_context_saving hSW hA hD hH hE hF
  obtain ⟨P₁,hP₁⟩ := eventually_atTop.mp
    (long_prime_power_absorption (C := 4) (D := D) (E := F)
      (by norm_num) hD.le hF)
  refine ⟨K+1,max P₀ P₁,by positivity,lt_of_lt_of_le hP₀ (le_max_left _ _),?_⟩
  intro T P B a l b h w z u M V hT hP hTP hlow hupp hw hz hM hV hheight hMV W hW hWn hWd
    v e C hv hnc hNv he hNe
  have hPpos : 0 < P := zero_lt_one.trans (hP₀.trans_le ((le_max_left _ _).trans hP))
  let S := ((primeCutoff B).filter (fun p => IsCoprime p e)).filter
    (fun p => largestPrimePredicate primeTieCode C p)
  let f := fun p : Eisenstein =>
    distinguishedRadialWeight W w z (norm p)*mellinPhase u (norm p)*cubicSymbol p v
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
  have hend := prime_interval_endpoint_difference S hS
    (fun p => a < norm p ∧ l ≤ norm p ∧ norm p < b ∧ norm p ≤ h)
    (fun p => max a l < norm p ∧ norm p ≤ min b h) (max a l) (min b h)
    (fun p _ hlo hhi => mixed_norm_interval_away hlo hhi) f hM hf
  have hinterval : (∑ p ∈ S with max a l < norm p ∧ norm p ≤ min b h, f p) =
      ∑ p ∈ (((primeCutoff (min B (min b h))).filter (fun p => max a l < norm p)).filter
        (fun p => IsCoprime p e)).filter
        (fun p => largestPrimePredicate primeTieCode C p), f p := by
    apply Finset.sum_congr _ (fun _ _ => rfl)
    ext p
    simp only [S,Finset.mem_filter,mem_primeCutoff,le_min_iff]
    tauto
  have hmain : ‖∑ p ∈ S with max a l < norm p ∧ norm p ≤ min b h, f p‖ ≤ K*P/T^D := by
    rw [hinterval]
    by_cases hab : max a l ≤ min B (min b h)
    · exact hbound T P (max a l) (min B (min b h)) w z u M V hT
        ((le_max_left _ _).trans hP) hTP hlow hab ((min_le_right _ _).trans hupp)
        hw hz hM hV hheight hMV W hW hWn hWd v e C hv hnc hNv he hNe
    · have hempty : (((primeCutoff (min B (min b h))).filter (fun p => max a l < norm p)).filter
          (fun p => IsCoprime p e)).filter (fun p => largestPrimePredicate primeTieCode C p) = ∅ := by
        apply Finset.eq_empty_of_forall_notMem
        intro p hp
        have hm := Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1
        exact hab (hm.2.le.trans (mem_primeCutoff.mp hm.1).2)
      rw [hempty,Finset.sum_empty,norm_zero]
      positivity
  have herr : 4*M ≤ P/T^D :=
    (mul_le_mul_of_nonneg_left ((le_add_of_nonneg_right hV).trans hMV) (by norm_num)).trans
      (hP₁ P ((le_max_right _ _).trans hP) T hT hTP)
  change ‖∑ p ∈ S with a < norm p ∧ l ≤ norm p ∧ norm p < b ∧ norm p ≤ h, f p‖ ≤ _
  calc
    _ ≤ ‖∑ p ∈ S with max a l < norm p ∧ norm p ≤ min b h, f p‖+
        ‖(∑ p ∈ S with a < norm p ∧ l ≤ norm p ∧ norm p < b ∧ norm p ≤ h, f p)-
          (∑ p ∈ S with max a l < norm p ∧ norm p ≤ min b h, f p)‖ :=
      norm_le_norm_add_norm_sub' _ _
    _ ≤ K*P/T^D+4*M := add_le_add hmain (by
      convert hend using 1
      congr 2
      all_goals
        apply Finset.sum_congr
        · ext p
          simp only [Finset.mem_filter]
        · intro p hp
          rfl)
    _ ≤ K*P/T^D+P/T^D := add_le_add le_rfl herr
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
