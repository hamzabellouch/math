import OAI.NumberTheory.CubicMoment.Estimates.DispersionAlgebra
import OAI.NumberTheory.CubicGram.SieveImprovement

namespace OAI

/-! The actual bilinear Gauss kernel is controlled by the proved cubic
large sieve. This is the finite arithmetic step in the long Type-I tail. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma metaplectic_bilinear_factor (A B : Finset Eisenstein)
    (α β : Eisenstein → ℂ) (hA : ∀ r ∈ A, primary r) (hB : ∀ u ∈ B, primary u) :
    (∑ r ∈ A, ∑ u ∈ B, α r*β u*gauss (r*u)) =
      ∑ r ∈ A, (α r*gauss r)*
        ∑ u ∈ B, (β u*gauss u)*star (cubicSymbol u r) := by
  apply Finset.sum_congr rfl
  intro r hr
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u hu
  rw [gauss_mul (hA r hr) (hB u hu)]
  ring

lemma gauss_weight_energy (A : Finset Eisenstein) (α : Eisenstein → ℂ)
    (hA : ∀ r ∈ A, primary r) :
    (∑ r ∈ A, ‖α r*gauss r‖^2) ≤ ∑ r ∈ A, ‖α r‖^2 := by
  apply Finset.sum_le_sum
  intro r hr
  rw [norm_mul]
  exact pow_le_pow_left₀ (by positivity)
    (mul_le_of_le_one_right (_root_.norm_nonneg _) (norm_gauss_le_one (hA r hr))) 2

lemma metaplectic_bilinear_operator (A B : Finset Eisenstein)
    (α β : Eisenstein → ℂ) (hA : ∀ r ∈ A, primary r) (hB : ∀ u ∈ B, primary u) :
    ‖∑ r ∈ A, ∑ u ∈ B, α r*β u*gauss (r*u)‖^2 ≤
      finiteCubicBound B A*(∑ r ∈ A, ‖α r‖^2)*(∑ u ∈ B, ‖β u‖^2) := by
  have he (r : Eisenstein) :
      (∑ u ∈ B, (β u*gauss u)*star (cubicSymbol u r)) =
        star (∑ u ∈ B, star (β u*gauss u)*cubicSymbol u r) := by
    simp only [star_sum,star_mul,star_star,mul_comm]
  have hrows : (∑ r ∈ A, ‖∑ u ∈ B, (β u*gauss u)*star (cubicSymbol u r)‖^2) ≤
      finiteCubicBound B A*(∑ u ∈ B, ‖β u‖^2) := by
    simp_rw [he,norm_star]
    exact (finiteCubicBound_controls_mass B A (fun u => star (β u*gauss u))).trans
      (mul_le_mul_of_nonneg_left (by
        simpa only [norm_star] using gauss_weight_energy B β hB)
        (finiteCubicBound_nonneg _ _))
  rw [metaplectic_bilinear_factor A B α β hA hB]
  apply (complex_bilinear_rows_sq A (fun r => α r*gauss r)
    (fun r => ∑ u ∈ B, (β u*gauss u)*star (cubicSymbol u r))).trans
  have h := mul_le_mul (gauss_weight_energy A α hA) hrows
    (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
    (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  exact h.trans_eq (by ring)

theorem metaplectic_bilinear_sieve {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (A B : Finset Eisenstein) (R V : ℝ), 1 ≤ R → 1 ≤ V →
      (∀ r ∈ A, primary r ∧ Squarefree r ∧ norm r ≤ R) →
      (∀ u ∈ B, primary u ∧ Squarefree u ∧ norm u ≤ V) →
      ∀ α β : Eisenstein → ℂ,
      ‖∑ r ∈ A, ∑ u ∈ B, α r*β u*gauss (r*u)‖^2 ≤
        C*(R*V)^ε*(R+V+(R*V)^(2/3:ℝ))*
          (∑ r ∈ A, ‖α r‖^2)*(∑ u ∈ B, ‖β u‖^2) := by
  obtain ⟨C,hC,hbound⟩ := finiteCubicBound_sharp ε hε
  refine ⟨C,hC,?_⟩
  intro A B R V hR hV hA hB α β
  apply (metaplectic_bilinear_operator A B α β (fun r hr => (hA r hr).1)
    (fun u hu => (hB u hu).1)).trans
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (hbound B A R V hR hV hB hA)
      (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))
    (Finset.sum_nonneg (fun _ _ => sq_nonneg _))

end CubicFirstMoment

end

end OAI
