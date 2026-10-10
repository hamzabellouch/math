import Mathlib.MeasureTheory.VectorMeasure.WithDensity
import Mathlib.MeasureTheory.Integral.Prod

namespace OAI

/-! # Rectangle tests determine an integrable product function

This finite-measure bridge will identify the range of the boundary projection.
It uses uniqueness of vector measures on the rectangle pi-system, avoiding
any unproved tensor-product identification of L2 spaces.
-/

namespace KadisonKastler

noncomputable section

open MeasureTheory Set

variable {X Y E : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  {μ : Measure X} {ν : Measure Y}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem integrable_eq_zero_of_rectangle_integrals {f : X × Y → E}
    (hf : Integrable f (μ.prod ν))
    (hrect : ∀ A B, MeasurableSet A → MeasurableSet B →
      ∫ z in A ×ˢ B, f z ∂μ.prod ν = 0) : f =ᵐ[μ.prod ν] 0 := by
  have he : (μ.prod ν).withDensityᵥ f = 0 := by
    apply VectorMeasure.ext_of_generateFrom
      (image2 (· ×ˢ ·) {A : Set X | MeasurableSet A} {B : Set Y | MeasurableSet B})
    · rintro _ ⟨A, hA, B, hB, rfl⟩
      rw [withDensityᵥ_apply hf (hA.prod hB), hrect A B hA hB]
      rfl
    · exact generateFrom_prod.symm
    · exact isPiSystem_prod
    · rw [withDensityᵥ_apply hf MeasurableSet.univ]
      simpa using hrect univ univ MeasurableSet.univ MeasurableSet.univ
  apply hf.ae_eq_of_withDensityᵥ_eq (integrable_zero _ _ _)
  simpa using he

theorem integrable_eq_of_rectangle_integrals {f g : X × Y → E}
    (hf : Integrable f (μ.prod ν)) (hg : Integrable g (μ.prod ν))
    (hrect : ∀ A B, MeasurableSet A → MeasurableSet B →
      ∫ z in A ×ˢ B, f z ∂μ.prod ν = ∫ z in A ×ˢ B, g z ∂μ.prod ν) :
    f =ᵐ[μ.prod ν] g := by
  have hz := integrable_eq_zero_of_rectangle_integrals (hf.sub hg) (by
    intro A B hA hB
    simp only [Pi.sub_apply]
    rw [integral_sub hf.integrableOn hg.integrableOn, hrect A B hA hB, sub_self])
  filter_upwards [hz] with z hz
  exact sub_eq_zero.mp hz

end

end KadisonKastler

end OAI
