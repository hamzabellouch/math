import OAI.NumberTheory.CubicMoment.Estimates.TypeIMixedPrime

namespace OAI

/-! Finite, literal versions of the Type-I mixed term and its squarefree
product model. These identities do not remove common prime divisors. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma typeIMixedGauss_finite (r : Eisenstein) (W : ℝ → ℂ)
    {U B F : ℝ} (hU : 0 < U) (hBF : B*U ≤ F)
    (hW : ∀ x : ℝ, B < x → W x = 0) :
    typeIMixedGauss r W U = ∑ u ∈ primaryElementBall F,
      W (norm u/U)*((norm u^(-1/6:ℝ):ℝ):ℂ)*gauss (u*r) := by
  let S := (primaryElementBall F).subtype primary
  have he : typeIMixedGauss r W U = ∑ u ∈ S,
      gauss (r*u)*((norm u^(-1/6:ℝ):ℝ):ℂ)*W (norm u/U) := by
    apply tsum_eq_sum
    intro u hu
    have hnorm : F < norm u := by
      by_contra hn
      exact hu (Finset.mem_subtype.mpr (mem_primaryElementBall.mpr ⟨u.property,le_of_not_gt hn⟩))
    rw [hW _ ((lt_div_iff₀ hU).mpr (hBF.trans_lt hnorm)),mul_zero]
  rw [he]
  dsimp only [S]
  rw [Finset.sum_subtype_of_mem
    (fun u : Eisenstein => gauss (r*u)*((norm u^(-1/6:ℝ):ℝ):ℂ)*W (norm u/U))
    (fun _ hu => (mem_primaryElementBall.mp hu).1)]
  apply Finset.sum_congr rfl
  intro u _
  rw [mul_comm u r]
  ring

lemma typeIMixedModel_finite (r : Eisenstein) (W : ℝ → ℂ)
    {U B F : ℝ} (hU : 0 < U) (hBF : B*U ≤ F)
    (hW : ∀ x : ℝ, B < x → W x = 0) :
    typeIMixedModel r W U = ∑ u ∈ primaryElementBall F,
      (idealMoebius (r*u):ℂ)^2*
        ((cStar*norm (r*u)^(-1/6:ℝ)*norm u^(-1/6:ℝ):ℝ):ℂ)*W (norm u/U) := by
  unfold typeIMixedModel
  let f : Eisenstein → ℂ := fun u => if primary u then (idealMoebius (r*u):ℂ)^2*
    ((cStar*norm (r*u)^(-1/6:ℝ)*norm u^(-1/6:ℝ):ℝ):ℂ)*W (norm u/U) else 0
  change (∑' u, f u) = _
  have he : (∑' u, f u) = ∑ u ∈ primaryElementBall F, f u := by
    apply tsum_eq_sum
    intro u hu
    by_cases hp : primary u
    · have hnorm : F < norm u := by
        by_contra hn
        exact hu (mem_primaryElementBall.mpr ⟨hp,le_of_not_gt hn⟩)
      dsimp only [f]
      rw [ite_eq_left hp,hW _ ((lt_div_iff₀ hU).mpr (hBF.trans_lt hnorm)),mul_zero]
    · simp only [f,hp,ite_false]
  rw [he]
  apply Finset.sum_congr rfl
  intro u hu
  exact ite_eq_left (mem_primaryElementBall.mp hu).1

lemma typeIMixedModel_finite_factor (r : Eisenstein) (W : ℝ → ℂ)
    {U B F : ℝ} (hU : 0 < U) (hBF : B*U ≤ F)
    (hW : ∀ x : ℝ, B < x → W x = 0) :
    typeIMixedModel r W U = (cStar:ℂ)*((norm r^(-1/6:ℝ):ℝ):ℂ)*
      (∑ u ∈ primaryElementBall F, (idealMoebius (r*u):ℂ)^2*
        ((norm u^(-1/3:ℝ):ℝ):ℂ)*W (norm u/U)) := by
  rw [typeIMixedModel_finite r W hU hBF hW,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u hu
  have hn : 0 < norm u := norm_pos_of_ne_zero (primary_ne_zero (mem_primaryElementBall.mp hu).1)
  have hp : norm (r*u)^(-1/6:ℝ)*norm u^(-1/6:ℝ) =
      norm r^(-1/6:ℝ)*norm u^(-1/3:ℝ) := by
    rw [norm_mul_eq,Real.mul_rpow (norm_nonneg r) hn.le,mul_assoc,←Real.rpow_add hn]
    norm_num
  calc
    _ = (idealMoebius (r*u):ℂ)^2*
        ((cStar*(norm (r*u)^(-1/6:ℝ)*norm u^(-1/6:ℝ)):ℝ):ℂ)*W (norm u/U) := by push_cast; ring
    _ = _ := by rw [hp]; push_cast; ring

end CubicFirstMoment

end

end OAI
