import OAI.GroupTheory.PolycyclicRecognition.Algebra.PolynomialModelHom
import OAI.GroupTheory.PolycyclicRecognition.Algebra.PolynomialModelWords
import OAI.GroupTheory.PolycyclicRecognition.Algebra.BasisPolynomialMaps

namespace OAI

/-! # Induction data for completing a nilpotent group with a real kernel

The integer grid is required only to lie in the embedded group. The kernel
may already contain real one-parameter groups, so discreteness is not assumed.
-/

noncomputable section
namespace PolycyclicRecognition
open scoped Manifold ContDiff
variable {K H : Type} [RealNormedLieAlgebra K] [FiniteDimensional ℝ K]
  [PK : PolynomialExponentialCoordinates K] [Group H]

structure NilpotentKernelCompletion (i : K →* H) where
  carrier : Type
  [normed : RealNormedLieAlgebra carrier]
  [finiteDimensional : FiniteDimensional ℝ carrier]
  [coordinates : PolynomialExponentialCoordinates carrier]
  [nilpotent : LieRing.IsNilpotent carrier]
  embed : H →* carrier
  injective : Function.Injective embed
  kernel_smooth : ContMDiff (𝓘(ℝ, K)) (𝓘(ℝ, carrier)) ∞ (embed.comp i)
  dimension : ℕ
  basis : Module.Basis (Fin dimension) ℝ carrier
  parameter : carrier ≃ carrier
  polynomial : IsPolynomialInBasis basis basis parameter
  polynomial_symm : IsPolynomialInBasis basis basis parameter.symm
  integer_grid : ∀ z : Fin dimension → ℤ, ∃ h : H,
    embed h = parameter (basis.equivFun.symm (fun j => (z j : ℝ)))
  extend : ∀ (M : Type) [RealNormedLieAlgebra M] [FiniteDimensional ℝ M]
    [PolynomialExponentialCoordinates M] [LieRing.IsNilpotent M]
    (f : H →* M), ContMDiff (𝓘(ℝ, K)) (𝓘(ℝ, M)) ∞ (f.comp i) →
    ∃ φ : carrier →* M, ContMDiff (𝓘(ℝ, carrier)) (𝓘(ℝ, M)) ∞ φ ∧
      ∀ h, φ (embed h) = f h

attribute [instance] NilpotentKernelCompletion.normed
  NilpotentKernelCompletion.finiteDimensional NilpotentKernelCompletion.coordinates
  NilpotentKernelCompletion.nilpotent

namespace NilpotentKernelCompletion

def of_polynomial_kernel [LieRing.IsNilpotent K] :
    NilpotentKernelCompletion (MonoidHom.id K) where
  carrier := K
  embed := MonoidHom.id K
  injective := Function.injective_id
  kernel_smooth := contMDiff_id
  dimension := Module.finrank ℝ K
  basis := Module.finBasis ℝ K
  parameter := Equiv.refl K
  polynomial := IsPolynomialInBasis.linear LinearMap.id
  polynomial_symm := IsPolynomialInBasis.linear LinearMap.id
  integer_grid z := ⟨(Module.finBasis ℝ K).equivFun.symm (fun j => (z j : ℝ)), rfl⟩
  extend _ _ _ _ _ f hf := ⟨f, hf, fun _ => rfl⟩

variable {i : K →* H} (C : NilpotentKernelCompletion i)

/-- The polynomial integer grid determines every smooth homomorphism. -/
theorem hom_ext (M : Type) [RealNormedLieAlgebra M] [FiniteDimensional ℝ M]
    [PM : PolynomialExponentialCoordinates M]
    (φ ψ : C.carrier →* M)
    (hφ : ContMDiff (𝓘(ℝ, C.carrier)) (𝓘(ℝ, M)) ∞ φ)
    (hψ : ContMDiff (𝓘(ℝ, C.carrier)) (𝓘(ℝ, M)) ∞ ψ)
    (h : ∀ a, φ (C.embed a) = ψ (C.embed a)) : φ = ψ := by
  let b := Module.finBasis ℝ M
  let f := polynomialModelLieHom φ hφ
  let g := polynomialModelLieHom ψ hψ
  have he : (f.toLinearMap ∘ C.parameter) = (g.toLinearMap ∘ C.parameter) := by
    apply ((IsPolynomialInBasis.linear (b := C.basis) (c := b) f.toLinearMap).comp
      C.polynomial).ext_integer_grid
      ((IsPolynomialInBasis.linear (b := C.basis) (c := b) g.toLinearMap).comp C.polynomial)
    intro z
    obtain ⟨a, ha⟩ := C.integer_grid z
    change f (C.parameter (C.basis.equivFun.symm (fun j => (z j : ℝ)))) =
      g (C.parameter (C.basis.equivFun.symm (fun j => (z j : ℝ))))
    rw [← ha]
    exact (polynomialModelLieHom_apply φ hφ _).trans
      ((h a).trans (polynomialModelLieHom_apply ψ hψ _).symm)
  apply MonoidHom.ext
  intro x
  have hh := congrFun he (C.parameter.symm x)
  change f (C.parameter (C.parameter.symm x)) = g (C.parameter (C.parameter.symm x)) at hh
  rw [C.parameter.apply_symm_apply] at hh
  exact (polynomialModelLieHom_apply φ hφ x).symm.trans
    (hh.trans (polynomialModelLieHom_apply ψ hψ x))

/-- Compatible automorphisms of the original group extend with their inverse. -/
theorem automorphism_extension (a : MulAut H)
    (ha : ContMDiff (𝓘(ℝ, K)) (𝓘(ℝ, C.carrier)) ∞
      ((C.embed.comp a.toMonoidHom).comp i))
    (hai : ContMDiff (𝓘(ℝ, K)) (𝓘(ℝ, C.carrier)) ∞
      ((C.embed.comp a.symm.toMonoidHom).comp i)) :
    ∃ A : MulAut C.carrier, ContMDiff (𝓘(ℝ, C.carrier)) (𝓘(ℝ, C.carrier)) ∞ A ∧
      ContMDiff (𝓘(ℝ, C.carrier)) (𝓘(ℝ, C.carrier)) ∞ A.symm ∧
      ∀ h, A (C.embed h) = C.embed (a h) := by
  obtain ⟨f, hf, hfe⟩ := C.extend C.carrier (C.embed.comp a.toMonoidHom) ha
  obtain ⟨g, hg, hge⟩ := C.extend C.carrier (C.embed.comp a.symm.toMonoidHom) hai
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom] at hfe hge
  have hgf : g.comp f = MonoidHom.id C.carrier := by
    apply C.hom_ext C.carrier (g.comp f) (MonoidHom.id C.carrier) (hg.comp hf) contMDiff_id
    intro h
    change g (f (C.embed h)) = C.embed h
    rw [hfe, hge]
    exact congrArg C.embed (a.symm_apply_apply h)
  have hfg : f.comp g = MonoidHom.id C.carrier := by
    apply C.hom_ext C.carrier (f.comp g) (MonoidHom.id C.carrier) (hf.comp hg) contMDiff_id
    intro h
    change f (g (C.embed h)) = C.embed h
    rw [hge, hfe]
    exact congrArg C.embed (a.apply_symm_apply h)
  let A : MulAut C.carrier :=
    { toFun := f
      invFun := g
      left_inv := fun x => DFunLike.congr_fun hgf x
      right_inv := fun x => DFunLike.congr_fun hfg x
      map_mul' := f.map_mul }
  exact ⟨A, hf, hg, hfe⟩

end NilpotentKernelCompletion
end PolycyclicRecognition

end

end OAI
