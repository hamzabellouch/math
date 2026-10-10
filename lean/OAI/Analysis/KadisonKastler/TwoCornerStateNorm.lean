import OAI.Analysis.KadisonKastler.ProjectionPinchedStateProperties

namespace OAI

/-! # Combining state comparisons on complementary corners

A functional centralizing a projection is the sum of its two compressed
functionals. Comparing normalized corner states and their scalar weights
therefore controls the norm distance of the original states.
-/

namespace KadisonKastler

noncomputable section

variable {A : Type*} [CStarAlgebra A]

def cornerFunctional (φ : A →L[ℂ] ℂ) (p : A) : A →L[ℂ] ℂ :=
  φ.comp (((ContinuousLinearMap.mul ℂ A).flip p).comp (ContinuousLinearMap.mul ℂ A p))

@[simp] theorem cornerFunctional_apply (φ : A →L[ℂ] ℂ) (p a : A) :
    cornerFunctional φ p a = φ (p*a*p) := rfl

theorem functional_eq_two_corners (φ : A →L[ℂ] ℂ) (p : A)
    (hp : IsStarProjection p) (hcentral : ∀ a : A, φ (p*a) = φ (a*p)) :
    φ = cornerFunctional φ p + cornerFunctional φ (1-p) := by
  ext a
  have hpp : φ (p*a*p) = φ (p*a) := by
    have h := hcentral (p*a)
    rw [← mul_assoc,hp.isIdempotentElem.eq] at h
    exact h.symm
  have he : (1-p)*a*(1-p) = a-p*a-a*p+p*a*p := by noncomm_ring
  change φ a = φ (p*a*p) + φ ((1-p)*a*(1-p))
  rw [he,map_add,map_sub,map_sub,hpp,hcentral]
  abel

theorem state_mixture_norm_sub_le
    (φ₀ φ₁ ψ₀ ψ₁ : A →L[ℂ] ℂ) (a b δ : ℝ)
    (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (hψ₀ : ‖ψ₀‖ ≤ 1) (hψ₁ : ‖ψ₁‖ ≤ 1)
    (h₀ : ‖φ₀-ψ₀‖ ≤ δ) (h₁ : ‖φ₁-ψ₁‖ ≤ δ) :
    ‖(a • φ₀ + (1-a) • φ₁) - (b • ψ₀ + (1-b) • ψ₁)‖ ≤
      δ + 2*|a-b| := by
  have he : (a • φ₀ + (1-a) • φ₁) - (b • ψ₀ + (1-b) • ψ₁) =
      (a • (φ₀-ψ₀) + (1-a) • (φ₁-ψ₁)) + (a-b) • (ψ₀-ψ₁) := by module
  have hψ : ‖ψ₀-ψ₁‖ ≤ 2 := (norm_sub_le _ _).trans (by linarith)
  rw [he]
  calc
    _ ≤ ‖a • (φ₀-ψ₀) + (1-a) • (φ₁-ψ₁)‖ + ‖(a-b) • (ψ₀-ψ₁)‖ := norm_add_le _ _
    _ ≤ (‖a • (φ₀-ψ₀)‖ + ‖(1-a) • (φ₁-ψ₁)‖) + ‖(a-b) • (ψ₀-ψ₁)‖ :=
      add_le_add (norm_add_le _ _) le_rfl
    _ = (a * ‖φ₀-ψ₀‖ + (1-a) * ‖φ₁-ψ₁‖) + |a-b| * ‖ψ₀-ψ₁‖ := by
      simp only [norm_smul,Real.norm_eq_abs,abs_of_nonneg ha,
        abs_of_nonneg (sub_nonneg.mpr ha1)]
    _ ≤ (a*δ+(1-a)*δ)+|a-b| * 2 := by
      exact add_le_add
        (add_le_add (mul_le_mul_of_nonneg_left h₀ ha)
          (mul_le_mul_of_nonneg_left h₁ (sub_nonneg.mpr ha1)))
        (mul_le_mul_of_nonneg_left hψ (abs_nonneg _))
    _ = _ := by ring

theorem twoCorner_state_norm_le
    (φ ψ φ₀ φ₁ ψ₀ ψ₁ : A →L[ℂ] ℂ) (p : A)
    (hp : IsStarProjection p)
    (hφ : ∀ x : A, φ (p*x) = φ (x*p))
    (hψ : ∀ x : A, ψ (p*x) = ψ (x*p))
    (a b δ : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (hφ₀ : cornerFunctional φ p = a • φ₀)
    (hφ₁ : cornerFunctional φ (1-p) = (1-a) • φ₁)
    (hψ₀ : cornerFunctional ψ p = b • ψ₀)
    (hψ₁ : cornerFunctional ψ (1-p) = (1-b) • ψ₁)
    (hψ₀norm : ‖ψ₀‖ ≤ 1) (hψ₁norm : ‖ψ₁‖ ≤ 1)
    (h₀ : ‖φ₀-ψ₀‖ ≤ δ) (h₁ : ‖φ₁-ψ₁‖ ≤ δ) :
    ‖φ-ψ‖ ≤ δ+2*|a-b| := by
  conv_lhs =>
    arg 1
    rw [functional_eq_two_corners φ p hp hφ,functional_eq_two_corners ψ p hp hψ]
  rw [hφ₀,hφ₁,hψ₀,hψ₁]
  exact state_mixture_norm_sub_le φ₀ φ₁ ψ₀ ψ₁ a b δ ha ha1 hψ₀norm hψ₁norm h₀ h₁

end

end KadisonKastler

end OAI
