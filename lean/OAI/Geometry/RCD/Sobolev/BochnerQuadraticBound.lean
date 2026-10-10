import OAI.Geometry.RCD.Sobolev.BochnerRadonDensity

namespace OAI

/-! # The quadratic perturbation estimate for a positive Bochner form -/

noncomputable section
namespace RegularPointCoordinates

variable {m : ℕ}

theorem finite_positive_bilinear_cauchySchwarz
    (B : Euclidean m →ₗ[ℝ] Euclidean m →ₗ[ℝ] ℝ)
    (hsym : ∀ a b, B a b=B b a) (hpos : ∀ a, 0≤B a a) (a b : Euclidean m) :
    (B a b)^2 ≤ B a a*B b b := by
  have hquad (t : ℝ) : 0≤B b b*(t*t)+(2*B a b)*t+B a a := by
    have ht := hpos (a+t • b)
    simp only [map_add,map_smul,LinearMap.add_apply,LinearMap.smul_apply,smul_eq_mul] at ht
    rw [hsym b a] at ht
    nlinarith only [ht]
  have hd := discrim_le_zero hquad
  simp only [discrim] at hd
  nlinarith only [hd]

/-- Subtracting the linear part of a quadratic perturbation removes its
value at the point. Positivity then gives the sharp directional Hessian
bound; no positive-definiteness of the form is required. -/
theorem bochner_quadratic_perturbation_bound
    (B : Euclidean m →ₗ[ℝ] Euclidean m →ₗ[ℝ] ℝ)
    (hsym : ∀ a b, B a b=B b a) (hpos : ∀ a, 0≤B a a)
    (f g q : Euclidean m) (c s H k : ℝ)
    (hfg : B f q=2*c*B f g+2*H)
    (hgq : B g q=2*c*B g g+2*k)
    (hqq : B q q=4*c^2*B g g+8*c*k+4*s^2) :
    H^2≤B f f*s^2 := by
  let v := q-(2*c) • g
  have hfv : B f v=2*H := by
    dsimp only [v]
    rw [map_sub,map_smul]
    change B f q-(2*c)*B f g=2*H
    linarith only [hfg]
  have hvv : B v v=4*s^2 := by
    dsimp only [v]
    simp only [map_sub,map_smul,LinearMap.sub_apply,LinearMap.smul_apply,smul_eq_mul]
    rw [hsym q g,hgq,hqq]
    ring
  have h := finite_positive_bilinear_cauchySchwarz B hsym hpos f v
  rw [hfv,hvv] at h
  nlinarith only [h]

open MeasureTheory

variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [SigmaFinite μ]

/-- Cauchy–Schwarz holds outside one null set for every pair of real
coordinate directions of the full Bochner density. -/
theorem bochnerRadonDensity_cauchySchwarz (M : PositiveBilinearMeasure X (Euclidean m)) :
    ∀ᵐ x ∂μ, ∀ a b : Euclidean m, (bochnerRadonDensity μ M x a b)^2 ≤
      bochnerRadonDensity μ M x a a*bochnerRadonDensity μ M x b b := by
  filter_upwards [bochnerRadonDensity_nonneg μ M] with x hx
  intro a b
  exact finite_positive_bilinear_cauchySchwarz (bochnerRadonDensity μ M x)
    (bochnerRadonDensity_symmetric μ M x) hx a b

end RegularPointCoordinates

end

end OAI
