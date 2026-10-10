import OAI.NumberTheory.CubicMoment.Estimates.TypeILowNegligible
import OAI.NumberTheory.CubicMoment.Estimates.BilinearKernelIdentity

namespace OAI

/-! Identify the estimated Type-I row with the literal finite sum of the
corrected Gauss kernel. The squarefree model and every phase are retained. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma angularSmoothModel_finite (r : Eisenstein) (ℓ : ℤ) (W : ℝ → ℂ)
    {U B F : ℝ} (hU : 0 < U) (hBF : B*U ≤ F)
    (hW : ∀ x : ℝ, B < x → W x = 0) :
    angularSmoothModel r ℓ W U =
      ∑ u ∈ primaryElementBall F, theta ℓ (r*u)*(idealMoebius (r*u):ℂ)^2*
        ((cStar*norm (r*u)^(-1/6:ℝ):ℝ):ℂ)*W (norm u/U) := by
  unfold angularSmoothModel
  rw [tsum_eq_sum (s := primaryElementBall F)]
  · apply Finset.sum_congr rfl
    intro u hu
    rw [ite_eq_left (mem_primaryElementBall.mp hu).1]
  · intro u hu
    by_cases hp : primary u
    · have hn : F < norm u := lt_of_not_ge
        (fun hn => hu (mem_primaryElementBall.mpr ⟨hp,hn⟩))
      have hx : B < norm u/U := (lt_div_iff₀ hU).mpr (hBF.trans_lt hn)
      simp only [ite_eq_left hp,hW _ hx,mul_zero]
    · simp only [ite_eq_right hp]

theorem lowTwistedTypeIRow_finite (r : Eisenstein) (ℓ : ℤ) (W : ℝ → ℂ)
    {U B : ℝ} (hU : 0 < U) (hW : ∀ x : ℝ, B < x → W x = 0) (t : ℝ) :
    lowTwistedTypeIRow r ℓ W U t =
      ∑ u ∈ primaryElementBall (B*U),
        theta ℓ (r*u)*centeredGauss (r*u)*mellinPhase t (norm u)*W (norm u/U) := by
  rw [lowTwistedTypeIRow,metaplecticAngularSmoothSum_finite r ℓ W hU le_rfl hW,
    angularSmoothModel_finite r ℓ (fun x => W x*mellinPhase t x) hU le_rfl
      (fun x hx => by rw [hW x hx,zero_mul]),Finset.mul_sum,←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro u hu
  have hn := norm_pos_of_ne_zero (primary_ne_zero (mem_primaryElementBall.mp hu).1)
  have hp : mellinPhase t U*mellinPhase t (norm u/U) = mellinPhase t (norm u) := by
    rw [←mellinPhase_mul_pos t hU (div_pos hn hU),mul_div_cancel₀ _ hU.ne']
  dsimp only [centeredGauss]
  push_cast
  calc
    _ = theta ℓ (r*u)*gauss (r*u)*mellinPhase t (norm u)*W (norm u/U)-
        theta ℓ (r*u)*(cStar:ℂ)*(idealMoebius (r*u):ℂ)^2*
          ((norm (r*u)^(-1/6:ℝ):ℝ):ℂ)*
          (mellinPhase t U*mellinPhase t (norm u/U))*W (norm u/U) := by ring
    _ = _ := by rw [hp]; ring

end CubicFirstMoment

end

end OAI
