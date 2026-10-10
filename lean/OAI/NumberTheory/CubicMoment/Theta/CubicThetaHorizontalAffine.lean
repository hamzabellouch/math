import OAI.NumberTheory.CubicMoment.Theta.CubicThetaHorizontalSection

namespace OAI

/-! Affine translates have the same cell integral after an integral
nonzero Eisenstein dilation. This is used for the character branches. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaHorizontal_multiply_periodic (f : ℂ → ℂ)
    (hf : ∀ (w : Eisenstein) z,f (z+3*(w:ℂ))=f z) (a : Eisenstein)
    (w : Eisenstein) (z : ℂ) :
    f ((a:ℂ)*(z+3*(w:ℂ)))=f ((a:ℂ)*z) := by
  have he : (a:ℂ)*(z+3*(w:ℂ))=(a:ℂ)*z+3*((a*w:Eisenstein):ℂ) := by
    push_cast
    ring
  rw [he,hf]

theorem cubicThetaHorizontal_affine_integral (f : ℂ → ℂ)
    (hf : ∀ (w : Eisenstein) z,f (z+3*(w:ℂ))=f z)
    {a : Eisenstein} (ha : a≠0) (b : ℂ) :
    (∫ z in cubicThetaHorizontalCell,f ((a:ℂ)*z+b))=
      ∫ z in cubicThetaHorizontalCell,f ((a:ℂ)*z) := by
  have haC : (a:ℂ)≠0 := fun he => ha (Subtype.ext he)
  have he (z : ℂ) : f ((a:ℂ)*z+b)=f ((a:ℂ)*(z+b/(a:ℂ))) := by
    congr 1
    field_simp [haC]
  simp_rw [he]
  exact cubicThetaHorizontal_translate_integral (fun z => f ((a:ℂ)*z))
    (cubicThetaHorizontal_multiply_periodic f hf a) (b/(a:ℂ))

lemma cubicThetaHorizontal_affine_integrable (f : C(ℂ,ℂ)) (a b : ℂ) :
    IntegrableOn (fun z => f (a*z+b)) cubicThetaHorizontalCell := by
  obtain ⟨K,hK,hsub⟩ := cubicThetaHorizontalCell_compact_container
  have hc : Continuous (fun z : ℂ => f (a*z+b)) := by fun_prop
  exact (hc.continuousOn.integrableOn_compact hK).mono_set hsub

end CubicFirstMoment

end

end OAI
