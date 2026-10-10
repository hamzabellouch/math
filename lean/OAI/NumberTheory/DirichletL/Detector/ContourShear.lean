import OAI.NumberTheory.DirichletL.Detector.InitialFubini

namespace OAI

noncomputable section
open MeasureTheory
namespace SevenEighths.ProbePhysical
open ProbeMellinBoundary

def sourceHeightShear : HeightSpace ≃ᵐ HeightSpace where
  toFun p := ((p.1.1+p.1.2,p.1.2),p.2)
  invFun p := ((p.1.1-p.1.2,p.1.2),p.2)
  left_inv p := by rcases p with ⟨⟨t,v⟩,w⟩;simp
  right_inv p := by rcases p with ⟨⟨t,v⟩,w⟩;simp
  measurable_toFun := by
    change Measurable (fun p : HeightSpace=>((p.1.1+p.1.2,p.1.2),p.2))
    fun_prop
  measurable_invFun := by
    change Measurable (fun p : HeightSpace=>((p.1.1-p.1.2,p.1.2),p.2))
    fun_prop

lemma sourceHeightShear_preserving : MeasurePreserving sourceHeightShear heightMeasure heightMeasure := by
  exact (measurePreserving_add_prod (volume:Measure ℝ) volume).prod (MeasurePreserving.id volume)

lemma sourceHeightShear_integral (F : HeightSpace→ℂ) :
    (∫p,F (sourceHeightShear p) ∂heightMeasure)=∫p,F p ∂heightMeasure :=
  sourceHeightShear_preserving.integral_comp' F

theorem source_contour_shear (F : ℂ→ℂ→ℂ→ℂ) (σ ξ υ : ℝ) :
    (∫p : HeightSpace,F (((σ:ℂ)+p.1.1*Complex.I)+((ξ:ℂ)+p.1.2*Complex.I)-1)
      ((υ:ℂ)+p.2*Complex.I) ((ξ:ℂ)+p.1.2*Complex.I) ∂heightMeasure)=
    ∫p : HeightSpace,F (((σ+ξ-1:ℝ):ℂ)+p.1.1*Complex.I)
      ((υ:ℂ)+p.2*Complex.I) ((ξ:ℂ)+p.1.2*Complex.I) ∂heightMeasure := by
  have hh := sourceHeightShear_integral (fun p : HeightSpace=>F
    (((σ+ξ-1:ℝ):ℂ)+p.1.1*Complex.I) ((υ:ℂ)+p.2*Complex.I) ((ξ:ℂ)+p.1.2*Complex.I))
  convert hh using 1
  congr 1
  funext p
  dsimp only [sourceHeightShear,MeasurableEquiv.coe_mk,Equiv.coe_fn_mk]
  congr 2 ; push_cast ; ring

lemma sourceMellinWeight_shear (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) (t w z : ℂ) :
    sourceMellinWeight W0 W1 X Y Z (t+1-z) w z=
      (X:ℂ)^(1/2-z)*(Z:ℂ)^t*(Y:ℂ)^(w-1)*Complex.exp (t^2)*
        mellin (EisensteinSchwartzPoisson.paperRadialFourier W0) z*mellin W1 w := by
  simp only [sourceMellinWeight,show t+1-z+z-1=t by ring]

end SevenEighths.ProbePhysical
end

end OAI
