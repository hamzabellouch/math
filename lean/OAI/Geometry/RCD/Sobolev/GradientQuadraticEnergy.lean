import OAI.Geometry.RCD.Sobolev.EuclideanQuadraticEnergy
import Mathlib.Analysis.Calculus.Gradient.Basic

namespace OAI

/-! # Quadratic expansion for the actual almost-everywhere Euclidean derivatives -/

open Set Filter MeasureTheory InnerProductSpace
noncomputable section
namespace RegularPointCoordinates

theorem gradient_quadratic_energy {n : ℕ} (f ψ : Euclidean n → ℝ)
    (A : Set (Euclidean n))
    (hf : ∀ᵐ x ∂(volume : Measure (Euclidean n)).restrict A, DifferentiableAt ℝ f x)
    (hψ : ∀ᵐ x ∂(volume : Measure (Euclidean n)).restrict A, DifferentiableAt ℝ ψ x)
    (hi : IntegrableOn (fun x => ‖fderiv ℝ f x‖^2) A volume)
    (hψi : IntegrableOn (fun x => ‖fderiv ℝ ψ x‖^2) A volume) (t : ℝ) :
    IntegrableOn (fun x => inner ℝ (gradient f x) (gradient ψ x)) A volume ∧
    IntegrableOn (fun x => ‖fderiv ℝ (fun y => f y+t*ψ y) x‖^2) A volume ∧
    (∫ x in A, ‖fderiv ℝ (fun y => f y+t*ψ y) x‖^2)=
      (∫ x in A, ‖fderiv ℝ f x‖^2)+
        2*t*(∫ x in A, inner ℝ (gradient f x) (gradient ψ x))+
        t^2*(∫ x in A, ‖fderiv ℝ ψ x‖^2) := by
  have hn (g : Euclidean n → ℝ) (x : Euclidean n) : ‖gradient g x‖=‖fderiv ℝ g x‖ :=
    (toDual ℝ (Euclidean n)).symm.norm_map _
  have hm (g : Euclidean n → ℝ) : Measurable (gradient g) :=
    (toDual ℝ (Euclidean n)).symm.continuous.measurable.comp (measurable_fderiv ℝ g)
  obtain ⟨hcross,hint,he⟩ := euclidean_quadratic_energy
    ((volume : Measure (Euclidean n)).restrict A) (gradient f) (gradient ψ)
    (hm f).aestronglyMeasurable (hm ψ).aestronglyMeasurable
    (by simpa only [IntegrableOn,hn] using hi) (by simpa only [IntegrableOn,hn] using hψi) t
  have hgrad : (fun x => ‖fderiv ℝ (fun y => f y+t*ψ y) x‖^2)=ᵐ[volume.restrict A]
      fun x => ‖gradient f x+t • gradient ψ x‖^2 := by
    filter_upwards [hf,hψ] with x hx hψx
    have hd := (hx.hasFDerivAt.add (hψx.hasFDerivAt.const_smul t)).fderiv
    have hpoint : gradient (fun y => f y+t*ψ y) x=gradient f x+t • gradient ψ x := by
      dsimp only [gradient]
      rw [show fderiv ℝ (fun y => f y+t*ψ y) x=fderiv ℝ f x+t • fderiv ℝ ψ x from hd,
        map_add,map_smul]
    rw [← hn, hpoint]
  refine ⟨hcross,hint.congr hgrad.symm,?_⟩
  rw [integral_congr_ae hgrad]
  simpa only [hn] using he

end RegularPointCoordinates

end

end OAI
