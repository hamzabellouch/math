import Mathlib.RepresentationTheory.Rep.Basic

namespace OAI

/-! # Nonzero maps determine rank-one integral representations -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2100] Linear.homModule

theorem integralEnd_apply (f : ℤ →ₗ[ℤ] ℤ) (x : ℤ) : f x = x * f 1 := by
  simpa only [smul_eq_mul, mul_one] using f.map_smul x (1 : ℤ)

theorem integralEnd_comp_comm (f g : ℤ →ₗ[ℤ] ℤ) : f ∘ₗ g = g ∘ₗ f := by
  apply LinearMap.ext_ring
  change f (g 1) = g (f 1)
  calc
    f (g 1) = g 1 * f 1 := integralEnd_apply f _
    _ = f 1 * g 1 := mul_comm _ _
    _ = g (f 1) := (integralEnd_apply g _).symm

theorem rankOne_end_comp_comm {V : Type*} [AddCommGroup V] [Module ℤ V]
    (e : V ≃ₗ[ℤ] ℤ) (f g : V →ₗ[ℤ] V) : f ∘ₗ g = g ∘ₗ f := by
  apply e.conj.injective
  rw [LinearEquiv.conj_comp, LinearEquiv.conj_comp]
  exact integralEnd_comp_comm _ _

theorem rankOne_linear_injective {V W : Type*} [AddCommGroup V] [Module ℤ V]
    [AddCommGroup W] [Module ℤ W] (eV : V ≃ₗ[ℤ] ℤ) (eW : W ≃ₗ[ℤ] ℤ)
    (f : V →ₗ[ℤ] W) (hf : f ≠ 0) : Function.Injective f := by
  let F := eW.toLinearMap ∘ₗ f ∘ₗ eV.symm.toLinearMap
  have hF : F 1 ≠ 0 := by
    intro h
    apply hf
    ext x
    apply eW.injective
    have hx := integralEnd_apply F (eV x)
    simpa [F, h] using hx
  intro x y hxy
  apply eV.injective
  apply mul_right_cancel₀ hF
  rw [← integralEnd_apply F, ← integralEnd_apply F]
  simpa only [F, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply] using congrArg eW hxy

theorem rankOne_rep_iso_of_nonzero {G : Type} [Group G] (D E : Rep ℤ G)
    (eD : D.V ≃ₗ[ℤ] ℤ) (eE : E.V ≃ₗ[ℤ] ℤ)
    (f : D ⟶ E) (hf : f ≠ 0) : Nonempty (D ≅ E) := by
  let e := eD.trans eE.symm
  let a := e.symm.toLinearMap ∘ₗ f.hom.toLinearMap
  have hf' : f.hom.toLinearMap ≠ 0 := by
    intro h
    apply hf
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    exact h
  have ha : Function.Injective a := e.symm.injective.comp
    (rankOne_linear_injective eD eE f.hom.toLinearMap hf')
  refine ⟨Rep.mkIso (Representation.Equiv.mk e ?_)⟩
  intro g
  ext x
  apply e.symm.injective
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
  change D.ρ g x = (e.symm.toLinearMap ∘ₗ E.ρ g ∘ₗ e.toLinearMap) x
  apply ha
  let b := e.symm.toLinearMap ∘ₗ E.ρ g ∘ₗ e.toLinearMap
  have hb := rankOne_end_comp_comm eD b a
  have hc : a ∘ₗ D.ρ g = b ∘ₗ a := by
    ext y
    change e.symm (f.hom (D.ρ g y)) = e.symm (E.ρ g (e (e.symm (f.hom y))))
    rw [LinearEquiv.apply_symm_apply]
    exact congrArg e.symm (Rep.hom_comm_apply f g y)
  exact congrArg (fun u : D.V →ₗ[ℤ] D.V => u x) (hc.trans hb)

end PolycyclicRecognition

end

end OAI
