import OAI.NumberTheory.TwoPoint.Fourier.MajorArcRationalSharp
import OAI.NumberTheory.TwoPoint.Fourier.MajorArcReduction

namespace OAI

/-! Preserve the square-root modulus loss through partial summation.
The estimates for shorter intervals remain explicit. -/
namespace TwoPointCorrelations

open Finset

theorem major_arc_typical_perturbed_sharp {ι : Type*} (J : Finset ι)
    (P : ι → Finset ℕ) (hP : ∀ j ∈ J, ∀ p ∈ P j, p.Prime)
    (F : ℕ → ℂ) (hFm : ∀ a b, 0 < a → 0 < b → F (a*b)=F a*F b) (hF : OneBounded F)
    (q : ℕ) (hq : 0 < q) (r : ℤ) (X H : ℕ) (hH : 0 < H)
    (A : ℝ) (hA : 0 ≤ A) (β : ℝ)
    (havoid : ∀ d ∈ q.divisors, mrtPrimeAvoids (J.biUnion P) d)
    (hshort : ∀ h : ℕ, 1 ≤ h → h ≤ H →
      ∀ d : {d : ℕ // d ∈ q.divisors}, ∀ χ : DirichletCharacter ℂ (q/d.val),
        (d.val:ℝ)*shortExponentialIntegral (mrtTypicalCoefficient J P (twistByCharacter F χ))
          (X/d.val+1) (h/d.val+1) 0 ≤ A/(d.val:ℝ)) :
    shortExponentialIntegral (mrtTypicalCoefficient J P F) X H ((r:ℝ)/q+β) ≤
      (1+2*Real.pi*|β| *H)*Real.sqrt (q:ℝ)*((1+Real.log q)*A+(q:ℝ)*X) := by
  have hq1 : (1:ℝ) ≤ q := by exact_mod_cast hq
  have hK : 0 ≤ Real.sqrt (q:ℝ)*((1+Real.log q)*A+(q:ℝ)*X) := by
    have hl := Real.log_nonneg hq1
    positivity
  have hh := major_arc_integral_perturbation_uniform (mrtTypicalCoefficient J P F)
    X H hH ((r:ℝ)/q) β _ hK (fun h hh hhH =>
      major_arc_typical_rational_sharp J P hP F hFm hF q hq r X h A hA havoid (hshort h hh hhH))
  simpa only [mul_assoc] using hh

lemma major_arc_twist_complete {q : ℕ} (F : ℕ → ℂ)
    (hF : ∀ a b, 0 < a → 0 < b → F (a*b)=F a*F b)
    (χ : DirichletCharacter ℂ q) :
    ∀ a b, 0 < a → 0 < b → twistByCharacter F χ (a*b)=twistByCharacter F χ a*twistByCharacter F χ b := by
  intro a b ha hb
  simp only [twistByCharacter,hF a b ha hb,Nat.cast_mul,map_mul]
  ring

lemma major_arc_divisor_distance {F : ℕ → ℂ} {X H : ℕ} {M : ℝ}
    (hd : MRTDistanceLowerBound F X H M) (q : ℕ) (hq : 0 < q)
    (hqmax : (q:ℝ) ≤ mrtModulusCutoff X H)
    (d : {d : ℕ // d ∈ q.divisors}) (χ : DirichletCharacter ℂ (q/d.val))
    (t : ℝ) (ht : |t| ≤ X) :
    M ≤ squaredDistance (twistByCharacter F χ) (mrtArchimedeanTwist t) X := by
  apply hd.major_arc_character (q/d.val) (major_arc_divisor_quotient_pos hq d) _ χ t ht
  exact (show ((q/d.val:ℕ):ℝ) ≤ q by exact_mod_cast Nat.div_le_self q d.val).trans hqmax

end TwoPointCorrelations

end OAI
