import Mathlib
import OAI.MeasureTheory.FalconerCompletion.Sphere.SpherePartsDerivativeBound2

namespace OAI

/-! Fourier kernels and oscillatory estimates. -/

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace Attempt4PrefixShell
open MeasureTheory Set Metric
open scoped ContDiff SchwartzMap RealInnerProductSpace
variable {n : ℕ}

noncomputable def sphereNorthSchwartzND (b : WithLp 2 (EuclideanSpace ℝ (Fin n) × ℝ) → ℂ)
    (hb : ContDiff ℝ ∞ b) : 𝓢(EuclideanSpace ℝ (Fin n),ℂ) :=
  sphereChartSchwartzND (sphereNorthPartND b) (Real.sqrt 3) (Real.sqrt_nonneg _)
    sqrt_three_lt_two (sphereNorthPartND_contDiff hb) (fun _ _ h => sphereNorthPartND_support h)

noncomputable def sphereSouthSchwartzND (b : WithLp 2 (EuclideanSpace ℝ (Fin n) × ℝ) → ℂ)
    (hb : ContDiff ℝ ∞ b) : 𝓢(EuclideanSpace ℝ (Fin n),ℂ) :=
  sphereChartSchwartzND (sphereReflectedSouthPartND b) (Real.sqrt 3) (Real.sqrt_nonneg _)
    sqrt_three_lt_two (sphereReflectedSouthPartND_contDiff hb)
    (fun _ _ h => sphereReflectedSouthPartND_support h)

theorem sphere_full_stationaryND_uniform (C : ℝ) (hC : 0 ≤ C) (J : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (b : WithLp 2 (EuclideanSpace ℝ (Fin n) × ℝ) → ℂ)
      (A Λ : ℝ) (hb : ContDiff ℝ ∞ b), 1 ≤ A → 0 < Λ →
      (∀ j ≤ 2*(J+1)+n+3, ∀ w, ‖w‖ = 1 → ‖iteratedFDeriv ℝ j b w‖ ≤ C*A^j) →
      ‖sphereOscillationND Λ b -
        (Complex.exp (Complex.I * Λ) *
          (fresnelCoefficientND (EuclideanSpace ℝ (Fin n)) (Λ/2) *
            quadraticExpansionND (sphereNorthSchwartzND b hb) J (Λ/2)) +
        star (Complex.exp (Complex.I * Λ) *
          (fresnelCoefficientND (EuclideanSpace ℝ (Fin n)) (Λ/2) *
            quadraticExpansionND (sphereSouthSchwartzND b hb) J (Λ/2))))‖ ≤
        D * Λ^(-(n:ℝ)/2-(J+1:ℕ)) * A^(2*(J+1)+n+3) := by
  obtain ⟨C',hC',hparts⟩ := sphere_parts_derivative_bound
    (V := EuclideanSpace ℝ (Fin n)) (2*(J+1)+n+3) C hC
  obtain ⟨D',hD',hlocal⟩ := sphere_stationaryND_uniform (n := n) (Real.sqrt 3)
    (Real.sqrt_nonneg _) sqrt_three_lt_two C' hC' J
  refine ⟨2*D',by positivity,?_⟩
  intro b A Λ hb hA hΛ hderiv
  have hN := hlocal (sphereNorthPartND b) A Λ (sphereNorthPartND_contDiff hb)
    (fun _ _ h => sphereNorthPartND_support h) hA hΛ
    (fun j hj w hw => (hparts b A hb hA hderiv j hj w hw).1)
  have hS := hlocal (sphereReflectedSouthPartND b) A Λ (sphereReflectedSouthPartND_contDiff hb)
    (fun _ _ h => sphereReflectedSouthPartND_support h) hA hΛ
    (fun j hj w hw => (hparts b A hb hA hderiv j hj w hw).2)
  change ‖sphereOscillationND Λ (sphereNorthPartND b) -
    Complex.exp (Complex.I*Λ)*(fresnelCoefficientND _ (Λ/2)*
      quadraticExpansionND (sphereNorthSchwartzND b hb) J (Λ/2))‖ ≤ _ at hN
  change ‖sphereOscillationND Λ (sphereReflectedSouthPartND b) -
    Complex.exp (Complex.I*Λ)*(fresnelCoefficientND _ (Λ/2)*
      quadraticExpansionND (sphereSouthSchwartzND b hb) J (Λ/2))‖ ≤ _ at hS
  rw [sphereOscillationND_split Λ hb.continuous]
  rw [add_sub_add_comm, ← star_sub]
  apply (norm_add_le _ _).trans
  rw [norm_star]
  linarith

end Attempt4PrefixShell
end GraphLiteralSupport
end
end

end OAI
