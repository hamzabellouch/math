import OAI.NumberTheory.CubicMoment.Estimates.SquarefreeMassDensity
import OAI.NumberTheory.CubicMoment.Estimates.CubeModelOverlap

namespace OAI

/-! The exact cube constant identifies the variance model with the
ordinary squarefree mass, with an explicit quantitative error. -/
noncomputable section
open scoped BigOperators ContDiff
namespace CubicFirstMoment

lemma cubeModelTerm_density_identity (S : Finset Eisenstein) (β : Eisenstein → ℂ)
    (u : ℝ) (V : ℝ → ℂ) (hV : HasCompactSupport V) (hV' : ContDiff ℝ ∞ V)
    (A ρ : ℝ) :
    (ρ:ℂ)*cubeModelTerm S β u V A =
      ((cStar^2*‖dispersionModel S β u‖^2:ℝ):ℂ)*
        (((A^(2/3:ℝ)*(2*Real.pi/(9*Real.sqrt 3)):ℝ):ℂ)*mellin V (2/3)*(ρ:ℂ)) := by
  rw [cubeModelTerm,cubeProfileIntegral_eq_mellin V hV hV']
  push_cast
  ring

theorem UniformLogWeights.cubeModelTerm_mass_error
    {ι : Type*} {W : ι → ℝ → ℂ} (h : UniformLogWeights W) :
    ∃ K : ℝ, 0 < K ∧ ∀ i (S : Finset Eisenstein) (β : Eisenstein → ℂ) (u A D : ℝ),
      1 ≤ A → 1 ≤ D →
      ‖(finiteSieveDensity (squarefreeDivisorTruncation D):ℂ)*cubeModelTerm S β u (W i) A-
        ((cStar^2*‖dispersionModel S β u‖^2:ℝ):ℂ)*squarefreeModelMass (W i) A‖ ≤
        K*‖dispersionModel S β u‖^2*(A^(5/12:ℝ)+A^(2/3:ℝ)*D^(-(1/2:ℝ))) := by
  obtain ⟨K,hK,hbound⟩ := h.squarefreeModelMass_density_error
  refine ⟨cStar^2*K,by have := cStar_pos; positivity,?_⟩
  intro i S β u A D hA hD
  rw [cubeModelTerm_density_identity S β u (W i) (h.compact i) (h.smooth i),
    ←mul_sub,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)),norm_sub_rev]
  exact (mul_le_mul_of_nonneg_left (hbound i A D hA hD)
    (mul_nonneg (sq_nonneg _) (sq_nonneg _))).trans_eq (by ring)

end CubicFirstMoment

end

end OAI
