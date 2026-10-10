import OAI.NumberTheory.CubicMoment.Estimates.SievedDispersion
import OAI.NumberTheory.CubicMoment.Estimates.SquarefreeModelMass

namespace OAI

/-! The compactly supported variance and model are exactly finite sums.
These identities transfer the analytic estimates into the corrected square. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma squarefreeModelMass_eq_sum (W : ℝ → ℂ) {A R F : ℝ}
    (hA : 0 < A) (hRF : R*A ≤ F) (hcut : ∀ x, R < x → W x = 0) :
    squarefreeModelMass W A = ∑ a ∈ primaryElementBall F,
      (idealMoebius a:ℂ)^2*W (norm a/A)*((norm a^(-1/3:ℝ):ℝ):ℂ) := by
  unfold squarefreeModelMass
  calc
    _ = ∑ a ∈ primaryElementBall F, if primary a then
        (idealMoebius a:ℂ)^2*W (norm a/A)*((norm a^(-1/3:ℝ):ℝ):ℂ) else 0 := by
      apply tsum_eq_sum
      intro a ha
      by_cases hp : primary a
      · have hn : R < norm a/A := (lt_div_iff₀ hA).mpr
          (hRF.trans_lt (lt_of_not_ge (fun hn => ha (mem_primaryElementBall.mpr ⟨hp,hn⟩))))
        simp only [hcut _ hn,mul_zero,zero_mul,ite_self]
      · simp only [hp,ite_false]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [ite_eq_left (mem_primaryElementBall.mp ha).1]

lemma sievedDispersionVariance_eq_sum (C B : Finset Eisenstein) (β : Eisenstein → ℂ)
    (u : ℝ) (W : ℝ → ℂ) {A R F : ℝ} (hA : 0 < A) (hRF : R*A ≤ F)
    (hcut : ∀ x, R < x → W x = 0) :
    sievedDispersionVariance C B β u W A =
      ∑ a ∈ primaryElementBall F, (((truncatedSquareDivisorSum C a)^2:ℝ):ℂ)*
        W (norm a/A)*((‖dispersionPolynomial B β u a‖^2:ℝ):ℂ) := by
  unfold sievedDispersionVariance
  calc
    _ = ∑ a ∈ primaryElementBall F, if primary a then
        (((truncatedSquareDivisorSum C a)^2:ℝ):ℂ)*W (norm a/A)*
          ((‖dispersionPolynomial B β u a‖^2:ℝ):ℂ) else 0 := by
      apply tsum_eq_sum
      intro a ha
      by_cases hp : primary a
      · have hn : R < norm a/A := (lt_div_iff₀ hA).mpr
          (hRF.trans_lt (lt_of_not_ge (fun hn => ha (mem_primaryElementBall.mpr ⟨hp,hn⟩))))
        simp only [hcut _ hn,mul_zero,zero_mul,ite_self]
      · simp only [hp,ite_false]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [ite_eq_left (mem_primaryElementBall.mp ha).1]

lemma squarefreeModelMass_ofReal (V : ℝ → ℝ) {A R F : ℝ}
    (hA : 0 < A) (hRF : R*A ≤ F) (hcut : ∀ x, R < x → V x = 0) :
    squarefreeModelMass (fun x => (V x:ℂ)) A =
      ((∑ a ∈ primaryElementBall F, (idealMoebius a:ℝ)^2*V (norm a/A)*
        norm a^(-1/3:ℝ):ℝ):ℂ) := by
  rw [squarefreeModelMass_eq_sum _ hA hRF (fun x hx => by rw [hcut x hx]; rfl),Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro a ha
  push_cast; rfl

lemma sievedDispersionVariance_ofReal (C B : Finset Eisenstein) (β : Eisenstein → ℂ)
    (u : ℝ) (V : ℝ → ℝ) {A R F : ℝ} (hA : 0 < A) (hRF : R*A ≤ F)
    (hcut : ∀ x, R < x → V x = 0) :
    sievedDispersionVariance C B β u (fun x => (V x:ℂ)) A =
      ((∑ a ∈ primaryElementBall F, (truncatedSquareDivisorSum C a)^2*V (norm a/A)*
        ‖dispersionPolynomial B β u a‖^2:ℝ):ℂ) := by
  rw [sievedDispersionVariance_eq_sum C B β u _ hA hRF (fun x hx => by rw [hcut x hx]; rfl),
    Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro a ha
  push_cast; rfl

end CubicFirstMoment

end

end OAI
