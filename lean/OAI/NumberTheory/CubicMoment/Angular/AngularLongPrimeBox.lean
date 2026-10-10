import OAI.NumberTheory.CubicMoment.Angular.AngularLongPrimeContext
import OAI.NumberTheory.CubicMoment.Angular.AngularKummerAlgebra
import OAI.NumberTheory.CubicMoment.Angular.AngularLongPrimeBin
import OAI.NumberTheory.CubicMoment.Estimates.LongPrimeBin

namespace OAI

/-! The actual geometric selected-prime bin inherits the published prime
saving. Its endpoint convention and largest-prime tie rule are retained. -/
noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem angular_long_prime_geometric_interval_moebius_saving (hEF : AngularKummerPrimeExplicitEstimate)
    (ℓ : ℤ) (hℓ : ℓ ≠ 0)
    {A D H E : ℝ} (hA : 0 < A) (hD : 0 < D) (hH : 0 ≤ H) (hE : 0 ≤ E) :
    ∃ K P₀ : ℝ, 0 < K ∧ 1 < P₀ ∧ ∀ (T B ρ w u a b : ℝ) (j : ℕ),
      1 ≤ T → 1 < ρ → ρ ≤ 2 → j < geometricBinCount ρ B →
      P₀ ≤ geometricBinLower ρ B j → T ≤ (Real.log (geometricBinLower ρ B j))^2 →
      0 < w → |u| ≤ T^H →
      ∀ (c v e : Eisenstein) (C : Finset Eisenstein), primary c → Squarefree c → v ≠ 0 →
        (¬∃ k : Eisenstein, k^3 = v) → norm v ≤ T^A → e ≠ 0 →
        Real.log (norm (c*e)) ≤ T^E →
      ‖∑ p ∈ (((primeCutoff B).filter (fun p => a < norm p ∧ norm p ≤ b)).filter (fun p => IsCoprime p (c*e))).filter
          (fun p => largestPrimePredicate primeTieCode C p ∧ geometricPrimeBin ρ B p = j),
        cutoffMoebius primeDetectorCutoff w (p*c)*normTwist u (p*c)*angularCubicSymbol ℓ (p*c) v‖ ≤
        K*geometricBinLower ρ B j/T^D := by
  obtain ⟨K,P₀,hK,hP₀,hbound⟩ := angular_long_prime_context_moebius_saving hEF ℓ hℓ hA hD hH hE
  obtain ⟨P₁,hP₁⟩ := eventually_atTop.mp
    (long_prime_power_absorption (C := 4) (D := D) (E := 0)
      (by norm_num) hD.le (by norm_num))
  refine ⟨K+1,max P₀ P₁,by positivity,lt_of_lt_of_le hP₀ (le_max_left _ _),?_⟩
  intro T B ρ w u a b j hT hρ hρ₂ hj hP hTP hw hu c v e C hc hs hv hnc hNv he hNe
  let P := geometricBinLower ρ B j
  have hP0 : 0 < P := zero_lt_one.trans
    (hP₀.trans_le ((le_max_left _ _).trans hP))
  let S := (((primeCutoff B).filter (fun p => a < norm p ∧ norm p ≤ b)).filter (fun p => IsCoprime p (c*e))).filter
    (fun p => largestPrimePredicate primeTieCode C p)
  let f := fun p : Eisenstein => cutoffMoebius primeDetectorCutoff w (p*c)*
    normTwist u (p*c)*angularCubicSymbol ℓ (p*c) v
  have hS (p : Eisenstein) (hp : p ∈ S) : primaryPrime p ∧ norm p ≤ B :=
    mem_primeCutoff.mp (Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1).1
  have hf (p : Eisenstein) (hp : p ∈ S) : ‖f p‖ ≤ 1 := by
    dsimp [f]
    rw [norm_mul,norm_mul,norm_normTwist,mul_one]
    exact (mul_le_mul (cutoffMoebius_norm_le_one
      (fun x => ⟨primeDetectorCutoff_nonneg x,primeDetectorCutoff_le_one x⟩) w (p*c))
      (angularCubicSymbol_norm_le_one ℓ (primary_mul (hS p hp).1.1 hc) v)
      (_root_.norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
  have hend := geometricPrimeBin_endpoint_difference hρ hρ₂ hj S hS f zero_le_one hf
  have hinterval : (∑ p ∈ S with P < norm p ∧ norm p ≤ ρ*P, f p) =
      ∑ p ∈ (((primeCutoff (min (min B b) (ρ*P))).filter (fun p => max a P < norm p)).filter
        (fun p => IsCoprime p (c*e))).filter
        (fun p => largestPrimePredicate primeTieCode C p), f p := by
    apply Finset.sum_congr _ (fun _ _ => rfl)
    ext p
    simp only [S,Finset.mem_filter,mem_primeCutoff,le_min_iff,max_lt_iff]
    tauto
  have hsum : ‖∑ p ∈ S with P < norm p ∧ norm p ≤ ρ*P, f p‖ ≤ K*P/T^D := by
    rw [hinterval]
    by_cases hm : max a P ≤ min (min B b) (ρ*P)
    · exact hbound T P (max a P) (min (min B b) (ρ*P)) w u hT ((le_max_left _ _).trans hP)
        hTP (le_max_right _ _) hm ((min_le_right _ _).trans (mul_le_mul_of_nonneg_right hρ₂ hP0.le))
        hw hu c v e C hc hs hv hnc hNv he hNe
    · have hempty : (((primeCutoff (min (min B b) (ρ*P))).filter (fun p => max a P < norm p)).filter
          (fun p => IsCoprime p (c*e))).filter
          (fun p => largestPrimePredicate primeTieCode C p) = ∅ := by
        apply Finset.eq_empty_of_forall_notMem
        intro p hp
        have hpc := Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1
        exact hm (hpc.2.le.trans (mem_primeCutoff.mp hpc.1).2)
      rw [hempty,Finset.sum_empty,norm_zero]
      positivity
  have hfour : (4:ℝ) ≤ P/T^D := by
    simpa only [Real.rpow_zero,mul_one] using
      hP₁ P ((le_max_right _ _).trans hP) T hT hTP
  have hset : (((primeCutoff B).filter (fun p => a < norm p ∧ norm p ≤ b)).filter (fun p => IsCoprime p (c*e))).filter
      (fun p => largestPrimePredicate primeTieCode C p ∧ geometricPrimeBin ρ B p = j) =
      S.filter (fun p => geometricPrimeBin ρ B p = j) := by
    ext p
    simp only [S,Finset.mem_filter]
    tauto
  rw [hset]
  change ‖∑ p ∈ S with geometricPrimeBin ρ B p = j, f p‖ ≤ _
  calc
    _ ≤ ‖∑ p ∈ S with P < norm p ∧ norm p ≤ ρ*P, f p‖+
        ‖(∑ p ∈ S with geometricPrimeBin ρ B p = j, f p)-
          (∑ p ∈ S with P < norm p ∧ norm p ≤ ρ*P, f p)‖ := norm_le_norm_add_norm_sub' _ _
    _ ≤ K*P/T^D+4 := add_le_add hsum (by simpa only [mul_one] using hend)
    _ ≤ K*P/T^D+P/T^D := add_le_add le_rfl hfour
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
