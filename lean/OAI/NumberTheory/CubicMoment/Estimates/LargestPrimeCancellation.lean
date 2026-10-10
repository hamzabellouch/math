import OAI.NumberTheory.CubicMoment.Estimates.LongPrimeSaving
import OAI.NumberTheory.CubicMoment.Estimates.LargestPrimeSelection
import OAI.NumberTheory.CubicMoment.Estimates.PrimeNormEndpoints

namespace OAI

/-! The actual largest-prime restriction costs only the two equal-norm
endpoints. The cancellation is still the published prime input, not a
sequence-condition hypothesis. -/
noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma largestPrime_endpoint_difference (code : Eisenstein → ℕ)
    (C S : Finset Eisenstein) (hS : ∀ p ∈ S, primaryPrime p)
    (f : Eisenstein → ℂ) {M : ℝ} (hM : 0 ≤ M) (hf : ∀ p ∈ S, ‖f p‖ ≤ M) :
    ‖(∑ p ∈ S with largestPrimePredicate code C p, f p)-
      (∑ p ∈ S with ((C.sup normNat:ℕ):ℝ) < norm p, f p)‖ ≤ 4*M := by
  apply prime_interval_endpoint_difference S hS _ _
    ((C.sup normNat:ℕ):ℝ) ((C.sup normNat:ℕ):ℝ) _ f hM hf
  intro p hp hn _
  have hne : normNat p ≠ C.sup normNat := by
    intro h
    apply hn
    rw [←normNat_cast p,h]
  simpa only [←normNat_cast p,Nat.cast_lt] using
    largestPrimePredicate_away_tie code C p hne

theorem long_prime_largest_moebius_saving (hSW : KummerPrimeSiegelWalfisz)
    {A D H E : ℝ} (hA : 0 < A) (hD : 0 < D) (hH : 0 ≤ H) (hE : 0 ≤ E) :
    ∃ K P₀ : ℝ, 0 < K ∧ 1 < P₀ ∧ ∀ (T P a b w u : ℝ),
      1 ≤ T → P₀ ≤ P → T ≤ (Real.log P)^2 →
      P ≤ a → a ≤ b → b ≤ 2*P → 0 < w → |u| ≤ T^H →
      ∀ c v e : Eisenstein, primary c → Squarefree c → v ≠ 0 →
        (¬∃ j : Eisenstein, j^3 = v) → norm v ≤ T^A → e ≠ 0 →
        Real.log (norm (c*e)) ≤ T^E →
      ‖∑ p ∈ (((primeCutoff b).filter (fun p => a < norm p)).filter
          (fun p => IsCoprime p (c*e))).filter
          (fun p => largestPrimePredicate primeTieCode (primaryPrimeFactors c) p),
        cutoffMoebius primeDetectorCutoff w (p*c)*normTwist u (p*c)*cubicSymbol (p*c) v‖ ≤
        K*P/T^D := by
  obtain ⟨K,P₀,hK,hP₀,hbound⟩ := long_prime_moebius_saving hSW hA hD hH hE
  obtain ⟨P₁,hP₁⟩ := eventually_atTop.mp
    (long_prime_power_absorption (C := 4) (D := D) (E := 0)
      (by norm_num) hD.le (by norm_num))
  refine ⟨K+1,max P₀ P₁,by positivity,lt_of_lt_of_le hP₀ (le_max_left _ _),?_⟩
  intro T P a b w u hT hP hTP ha hab hb hw hu c v e hc hs hv hnc hNv he hNe
  have hP0 : 0 < P := zero_lt_one.trans (hP₀.trans_le ((le_max_left _ _).trans hP))
  let S := ((primeCutoff b).filter (fun p => a < norm p)).filter
    (fun p => IsCoprime p (c*e))
  let f := fun p : Eisenstein => cutoffMoebius primeDetectorCutoff w (p*c)*
    normTwist u (p*c)*cubicSymbol (p*c) v
  let m : ℝ := (((primaryPrimeFactors c).sup normNat:ℕ):ℝ)
  have hS (p : Eisenstein) (hp : p ∈ S) : primaryPrime p :=
    (mem_primeCutoff.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1).1
  have hf (p : Eisenstein) (hp : p ∈ S) : ‖f p‖ ≤ 1 := by
    dsimp [f]
    rw [norm_mul,norm_mul,norm_normTwist,mul_one]
    exact (mul_le_mul (cutoffMoebius_norm_le_one
      (fun x => ⟨primeDetectorCutoff_nonneg x,primeDetectorCutoff_le_one x⟩) w (p*c))
      (norm_cubicSymbol_le_one (primary_mul (hS p hp).1 hc) v)
      (_root_.norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
  have hend := largestPrime_endpoint_difference primeTieCode (primaryPrimeFactors c) S hS
    f zero_le_one hf
  have hinterval :
      (∑ p ∈ S with m < norm p, f p) =
      ∑ p ∈ ((primeCutoff b).filter (fun p => max a m < norm p)).filter
        (fun p => IsCoprime p (c*e)), f p := by
    apply Finset.sum_congr _ (fun _ _ => rfl)
    ext p
    simp only [S,Finset.mem_filter,max_lt_iff]
    tauto
  have hsum : ‖∑ p ∈ S with m < norm p, f p‖ ≤ K*P/T^D := by
    rw [hinterval]
    by_cases hm : max a m ≤ b
    · exact hbound T P (max a m) b w u hT ((le_max_left _ _).trans hP) hTP
        (ha.trans (le_max_left _ _)) hm hb hw hu c v e hc hs hv hnc hNv he hNe
    · have hempty : ((primeCutoff b).filter (fun p => max a m < norm p)).filter
          (fun p => IsCoprime p (c*e)) = ∅ := by
        apply Finset.eq_empty_of_forall_notMem
        intro p hp
        obtain ⟨hp,_⟩ := Finset.mem_filter.mp hp
        obtain ⟨hp,hl⟩ := Finset.mem_filter.mp hp
        exact hm (hl.le.trans (mem_primeCutoff.mp hp).2)
      rw [hempty,Finset.sum_empty,norm_zero]
      positivity
  have hfour : (4:ℝ) ≤ P/T^D := by
    simpa only [Real.rpow_zero,mul_one] using
      hP₁ P ((le_max_right _ _).trans hP) T hT hTP
  change ‖∑ p ∈ S with largestPrimePredicate primeTieCode (primaryPrimeFactors c) p, f p‖ ≤ _
  calc
    _ ≤ ‖∑ p ∈ S with m < norm p, f p‖+
        ‖(∑ p ∈ S with largestPrimePredicate primeTieCode (primaryPrimeFactors c) p, f p)-
          (∑ p ∈ S with m < norm p, f p)‖ := by
      exact norm_le_norm_add_norm_sub' _ _
    _ ≤ K*P/T^D+4 := add_le_add hsum (by simpa only [mul_one] using hend)
    _ ≤ K*P/T^D+P/T^D := add_le_add le_rfl hfour
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
