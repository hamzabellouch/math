import OAI.Analysis.CircleDomains.Sobolev.HolomorphicInjOnDerivative

namespace OAI

/-! Lifting a holomorphic plane injection to the finite sphere charts. -/
open Set Function
noncomputable section
namespace CircleDomainRigidity

lemma conformalEquivalence_finiteLift {U V : Set ℂ} (hU : IsOpen U)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U) (hbij : BijOn f U V) :
    IsConformalEquivalence (extendAtInfinity f)
      (((↑) : ℂ → Sphere) '' U) (((↑) : ℂ → Sphere) '' V) := by
  have hconf : IsConformalOn (extendAtInfinity f) (((↑) : ℂ → Sphere) '' U) := by
    rintro _ ⟨z,hz,rfl⟩
    exact isConformalAt_extendAtInfinity_coe
      ((hf z hz).differentiableAt (hU.mem_nhds hz))
      (holomorphicInjOn_deriv_ne_zero hU hf hbij.injOn hz)
  have hi : InjOn (extendAtInfinity f) (((↑) : ℂ → Sphere) '' U) := by
    rintro _ ⟨x,hx,rfl⟩ _ ⟨y,hy,rfl⟩ he
    have hxy : f x=f y := OnePoint.coe_injective he
    exact congrArg ((↑) : ℂ → Sphere) (hbij.injOn hx hy hxy)
  have himage : extendAtInfinity f '' (((↑) : ℂ → Sphere) '' U) =
      ((↑) : ℂ → Sphere) '' V := by
    calc
      _ = ((↑) : ℂ → Sphere) '' (f '' U) := by
        rw [image_image,image_image]
        rfl
      _ = _ := by rw [hbij.image_eq]
  simpa only [himage] using isConformalEquivalence_of_injOn hconf
    (OnePoint.isOpen_image_coe.mpr hU) hi

end CircleDomainRigidity

end

end OAI
