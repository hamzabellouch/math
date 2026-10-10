import OAI.NumberTheory.CubicMoment.Estimates.SquarefreeCoprimeRemoval
import OAI.NumberTheory.CubicMoment.Angular.AngularLatticeModel

namespace OAI

/-! The literal mixed-term model with μ²(ra), and its quantitative
comparison with the unrestricted squarefree mass. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def coprimeSquarefreeModelMass (r : Eisenstein) (W : ℝ → ℂ) (A : ℝ) : ℂ :=
  ∑' a : Eisenstein, if primary a then (idealMoebius (r*a):ℂ)^2*
    W (norm a/A)*((norm a^(-1/3:ℝ):ℝ):ℂ) else 0

lemma coprimeSquarefreeModelMass_eq_radial {r : Eisenstein} (hr : Squarefree r)
    {A : ℝ} (hA : 0 < A) (W : ℝ → ℂ) :
    coprimeSquarefreeModelMass r W A = ((A^(-1/3:ℝ):ℝ):ℂ)*
      squarefreeCoprimeAngularLattice r 0 (fun x => ((x^(-1/3:ℝ):ℝ):ℂ)*W x) A := by
  rw [coprimeSquarefreeModelMass,squarefreeCoprimeAngularLattice,←tsum_mul_left]
  apply tsum_congr
  intro a
  rw [idealMoebius_sq_mul_of_squarefree hr]
  by_cases ha : primary a
  · by_cases hc : IsCoprime r a
    · have hp : norm a^(-1/3:ℝ) = A^(-1/3:ℝ)*(norm a/A)^(-1/3:ℝ) := by
        rw [←Real.mul_rpow hA.le (div_nonneg (norm_nonneg a) hA.le),
          mul_div_cancel₀ _ hA.ne']
      simp only [ha,hc,true_and,ite_true,theta_zero,hp]
      push_cast
      ring
    · simp only [ha,hc,true_and,ite_true,ite_false,zero_mul,mul_zero]
  · simp only [ha,false_and,ite_false,mul_zero]

theorem UniformLogWeights.coprimeSquarefreeModelMass_error
    {ι : Type*} {W : ι → ℝ → ℂ} (h : UniformLogWeights W) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ i (r : Eisenstein) (A D : ℝ),
      primary r → Squarefree r → 0 < A → 0 < D →
      (∀ p ∈ primaryPrimeFactors r, D ≤ norm p) →
      ‖coprimeSquarefreeModelMass r (W i) A-squarefreeModelMass (W i) A‖ ≤
        K*A^(2/3:ℝ)*(primaryPrimeFactors r).card/D := by
  obtain ⟨K,hK,hbound⟩ := (h.realPower (-1/3)).squarefreeCoprimeRadial_removal
  refine ⟨K,hK,?_⟩
  intro i r A D hr hsr hA hD hrough
  rw [coprimeSquarefreeModelMass_eq_radial hsr hA,squarefreeModelMass_eq_radial hA,
    ←mul_sub,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos (Real.rpow_pos_of_pos hA _)]
  apply (mul_le_mul_of_nonneg_left (hbound i r A D hr hsr hA hD hrough)
    (Real.rpow_nonneg hA.le _)).trans_eq
  have hp : A^(-1/3:ℝ)*A = A^(2/3:ℝ) := by
    calc
      _ = A^(-1/3:ℝ)*A^(1:ℝ) := by rw [Real.rpow_one]
      _ = _ := by rw [←Real.rpow_add hA]; norm_num
  calc
    _ = K*(A^(-1/3:ℝ)*A)*(primaryPrimeFactors r).card/D := by ring
    _ = _ := by rw [hp]

end CubicFirstMoment

end

end OAI
