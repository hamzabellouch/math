import OAI.NumberTheory.CubicMoment.Angular.AngularStoppedCharacterRows
import OAI.NumberTheory.CubicMoment.Angular.AngularStoppedLargeDivisorRows
import OAI.NumberTheory.CubicMoment.Angular.AngularStoppedMellinRows
import OAI.NumberTheory.CubicMoment.Decomposition.StoppedLargeDivisorMass
import OAI.NumberTheory.CubicMoment.Decomposition.StoppedLargeDivisorRows
import OAI.NumberTheory.CubicMoment.Estimates.PrimeSubsetBounds

namespace OAI

/-! Sum the large-divisor rows using genuine quotient lengths. The
distinct-prime-subset map is injective, so the estimates involve convergent
lattice norm series and no cardinality of the ambient prime set. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem angular_stopped_large_divisor_mass (ℓ : ℤ) {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η) :
    ∃ K : ℝ, 0 < K ∧ ∀ (X w z l b u M B D : ℝ)
      (W : ι → ℝ → ℂ) (selected : Eisenstein → Eisenstein → Prop)
      (e : Eisenstein) (U H : Finset Eisenstein),
      0 < b → 1 ≤ B → 0 < D → (∀ p ∈ U, primaryPrime p) →
      (∀ n ∈ stoppedIntervalSupport ι X l b e,
        ‖angularStoppedRowCoefficient ℓ X w z u W selected n‖ ≤ M) →
      (∀ v ∈ H, v ≠ 0 ∧ norm v ≤ B) →
      (∑ s ∈ U.powerset.filter (fun s => D < norm (∏ p ∈ s,p) ∧ norm (∏ p ∈ s,p) ≤ b),
        ∑ v ∈ H, ‖∑ n ∈ (stoppedIntervalSupport ι X l b e).filter
            (fun n => (∏ p ∈ s,p) ∣ n),
          angularStoppedRowCoefficient ℓ X w z u W selected n*cubicSymbol n v‖^2) ≤
      K*(2*B*b)^ε*M^2*(
        B*b*b^η*(∑' n : Eisenstein, norm n^(-(1+η)))+
        B^(2/3:ℝ)*b^(5/3:ℝ)*(∑' n : Eisenstein, norm n^(-(5/3:ℝ)))+
        B^(1/3:ℝ)*b^2*D^(-(1/2:ℝ))*(∑' n : Eisenstein, norm n^(-(3/2:ℝ)))) := by
  obtain ⟨K,hK,hbound⟩ := angular_stopped_large_divisor_row ℓ (ι := ι) hε
  refine ⟨K,hK,?_⟩
  intro X w z l b u M B D W selected e U H hb hB hD hU hcoeff hH
  let A := U.powerset.filter
    (fun s => D < norm (∏ p ∈ s,p) ∧ norm (∏ p ∈ s,p) ≤ b)
  let P := K*(2*B*b)^ε*M^2
  let F := fun s : Finset Eisenstein =>
    B*b*norm (∏ p ∈ s,p)^(-1:ℝ)+
    B^(2/3:ℝ)*b^(5/3:ℝ)*norm (∏ p ∈ s,p)^(-5/3:ℝ)+
    B^(1/3:ℝ)*b^2*norm (∏ p ∈ s,p)^(-2:ℝ)
  have hrow (s : Finset Eisenstein) (hs : s ∈ A) :
      (∑ v ∈ H, ‖∑ n ∈ (stoppedIntervalSupport ι X l b e).filter
        (fun n => (∏ p ∈ s,p) ∣ n),
        angularStoppedRowCoefficient ℓ X w z u W selected n*cubicSymbol n v‖^2) ≤ P*F s := by
    have hsub := Finset.mem_powerset.mp (Finset.mem_filter.mp hs).1
    have hsp := primary_finset_prod s (fun p => p) (fun p hp => (hU p (hsub hp)).1)
    exact hbound X w z l b u M B W selected e (∏ p ∈ s,p)
      hsp hb hB (Finset.mem_filter.mp hs).2.2 hcoeff H hH
  have h₁ : (∑ s ∈ A, norm (∏ p ∈ s,p)^(-1:ℝ)) ≤
      b^η*(∑' n : Eisenstein, norm n^(-(1+η))) :=
    primary_prime_subset_harmonic_on U hU A
      (fun _ hs => (Finset.mem_filter.mp hs).1) hb hη
      (fun _ hs => (Finset.mem_filter.mp hs).2.2)
  have h₂ : (∑ s ∈ A, norm (∏ p ∈ s,p)^(-5/3:ℝ)) ≤
      ∑' n : Eisenstein, norm n^(-(5/3:ℝ)) :=
    by simpa only [neg_div] using
      (primary_prime_subset_norm_sum (s := 5/3) U hU A
        (fun _ hs => (Finset.mem_filter.mp hs).1) (by norm_num))
  have h₃ : (∑ s ∈ A, norm (∏ p ∈ s,p)^(-2:ℝ)) ≤
      D^(-(1/2:ℝ))*(∑' n : Eisenstein, norm n^(-(3/2:ℝ))) :=
    primary_prime_subset_tail_on U hU A
      (fun _ hs => (Finset.mem_filter.mp hs).1) hD
      (fun _ hs => (Finset.mem_filter.mp hs).2.1)
  have hsum : (∑ s ∈ A, F s) ≤
      B*b*(b^η*(∑' n : Eisenstein, norm n^(-(1+η))))+
      B^(2/3:ℝ)*b^(5/3:ℝ)*(∑' n : Eisenstein, norm n^(-(5/3:ℝ)))+
      B^(1/3:ℝ)*b^2*(D^(-(1/2:ℝ))*(∑' n : Eisenstein, norm n^(-(3/2:ℝ)))) := by
    dsimp only [F]
    simp only [Finset.sum_add_distrib,←Finset.mul_sum]
    exact add_le_add (add_le_add (mul_le_mul_of_nonneg_left h₁ (by positivity))
      (mul_le_mul_of_nonneg_left h₂ (by positivity)))
      (mul_le_mul_of_nonneg_left h₃ (by positivity))
  calc
    _ ≤ ∑ s ∈ A, P*F s := Finset.sum_le_sum hrow
    _ = P*(∑ s ∈ A, F s) := (Finset.mul_sum _ _ _).symm
    _ ≤ P*(B*b*(b^η*(∑' n : Eisenstein, norm n^(-(1+η))))+
        B^(2/3:ℝ)*b^(5/3:ℝ)*(∑' n : Eisenstein, norm n^(-(5/3:ℝ)))+
        B^(1/3:ℝ)*b^2*(D^(-(1/2:ℝ))*(∑' n : Eisenstein, norm n^(-(3/2:ℝ))))) :=
      mul_le_mul_of_nonneg_left hsum (by dsimp [P]; positivity)
    _ = _ := by dsimp [P]; ring

end CubicFirstMoment

end

end OAI
