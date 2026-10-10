import OAI.Geometry.NodalSets.Elliptic.RealIntegralSquare

namespace OAI

namespace Yau.Geometry
open MeasureTheory Set
noncomputable section

theorem real_mean_square_decomposition {X : Type*} [MeasurableSpace X]
    (mu : Measure X) [IsFiniteMeasure mu] (hm : 0 < mu.real univ)
    (f : X → ℝ) (hf : Integrable f mu) (hf2 : Integrable (fun x ↦ f x^2) mu)
    (c : ℝ) :
    (∫ x, (f x-c)^2 ∂mu) =
      (∫ x, (f x-(∫ y, f y ∂mu)/mu.real univ)^2 ∂mu) +
        mu.real univ*((∫ y, f y ∂mu)/mu.real univ-c)^2 := by
  have hexpand (d : ℝ) : (∫ x, (f x-d)^2 ∂mu) =
      (∫ x, f x^2 ∂mu)-2*d*(∫ x, f x ∂mu)+mu.real univ*d^2 := by
    have he : (fun x ↦ (f x-d)^2) = fun x ↦ (f x^2-(2*d)*f x)+d^2 := by
      funext x; ring
    have hs : Integrable (fun x ↦ f x^2-(2*d)*f x) mu := hf2.sub (hf.const_mul _)
    rw [he,integral_add hs (integrable_const _),
      integral_sub hf2 (hf.const_mul (2*d)),integral_const_mul,integral_const]
    rfl
  rw [hexpand,hexpand]
  field_simp
  ring

theorem real_mean_square_contraction {X : Type*} [MeasurableSpace X]
    (mu : Measure X) [IsFiniteMeasure mu] (hm : 0 < mu.real univ)
    (f : X → ℝ) (hf : Integrable f mu) (hf2 : Integrable (fun x ↦ f x^2) mu) :
    mu.real univ*((∫ x, f x ∂mu)/mu.real univ)^2 ≤ ∫ x, f x^2 ∂mu := by
  have h := real_integral_square_le mu hm f hf hf2
  apply (mul_le_mul_iff_right₀ hm).mp
  calc
    _ = (∫ x, f x ∂mu)^2 := by field_simp
    _ ≤ _ := by simpa [mul_comm] using h

end
end Yau.Geometry

end OAI
