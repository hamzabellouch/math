import OAI.GroupTheory.PolycyclicRecognition.Lattices.KernelCompletionCyclicHom
import OAI.GroupTheory.PolycyclicRecognition.Algebra.CyclicParameterBasis
import OAI.GroupTheory.PolycyclicRecognition.Geometry.SemidirectExponentialCoordinates

namespace OAI

/-! # A cyclic step in completing a nilpotent extension with a real kernel

This constructs the next polynomial model, its faithful embedding, its integer
grid and its homomorphism extension property. No lattice in the kernel is
required.
-/

noncomputable section
namespace PolycyclicRecognition
open scoped Manifold ContDiff
variable {K H : Type} [RealNormedLieAlgebra K] [FiniteDimensional ℝ K]
  [PK : PolynomialExponentialCoordinates K] [Group H]
  {i : K →* H} (C : NilpotentKernelCompletion i)

namespace NilpotentKernelCompletion

theorem cyclic_step_with_dimension (a : MulAut H) (A : C.carrier ≃ₗ⁅ℝ⁆ C.carrier)
    (hA : IsNilpotent (A.toLinearMap - 1))
    (hAe : ∀ h, A (C.embed h) = C.embed (a h)) :
    ∃ C' : NilpotentKernelCompletion
      ((SemidirectProduct.inl : H →* H ⋊[integerPowerAction a] Multiplicative ℤ).comp i),
      C'.dimension = C.dimension + 1 := by
  let L := C.carrier
  let D := unipotentLieLogarithm A hA
  let hD := unipotentLieLogarithm_nilpotent A hA
  let φ := PolynomialExponentialCoordinates.derivationAction D hD
  have hstep (h : H) : C.embed (a h) = φ (Multiplicative.ofAdd 1) (C.embed h) := by
    change C.embed (a h) = unipotentLieFlow A hA 1 (C.embed h)
    rw [unipotentLieFlow_one, hAe]
  let I := realIntegerSemidirectMap φ a C.embed hstep
  have hI : Function.Injective I := realIntegerSemidirectMap_injective φ a C.embed hstep C.injective
  let := derivationSemidirectGroup D hD
  let : Mul (L × ℝ) := (derivationSemidirectGroup D hD).toMul
  let : MulOneClass (L × ℝ) := (derivationSemidirectGroup D hD).toMulOneClass
  let e : (L × ℝ) ≃* (L ⋊[φ] Multiplicative ℝ) :=
    { derivationSemidirectEquiv D hD with map_mul' := fun _ _ => rfl }
  let jR := e.symm.toMonoidHom.comp I
  have hjR (z : H ⋊[integerPowerAction a] Multiplicative ℤ) :
      jR z = (C.embed z.left, (z.right.toAdd : ℝ)) := rfl
  obtain ⟨Q, E, hE⟩ := exists_semidirect_polynomial_exponential_coordinates D hD
  let := Q
  let T := DerivationLieSpace D hD
  let : Group T := Q.group
  let : Mul T := Q.group.toMul
  let j := E.symm.toMonoidHom.comp jR
  have hj (z : H ⋊[integerPowerAction a] Multiplicative ℤ) :
      E (j z) = (C.embed z.left, (z.right.toAdd : ℝ)) := by
    change E (E.symm (jR z)) = _
    rw [E.apply_symm_apply, hjR]
  let s := derivationLieSpaceSplit D hD
  let b := cyclicParameterBasis C.basis s
  let c := Module.finBasis ℝ (L × ℝ)
  let p := transportedProductParameter C.parameter s E.toEquiv
  have hp := polynomial_transported_product_parameter C.basis c b
    C.parameter s E.toEquiv C.polynomial C.polynomial_symm (hE b c).1 (hE b c).2
  have hEinv : ContMDiff (𝓘(ℝ, L × ℝ)) (𝓘(ℝ, T)) ∞ E.symm :=
    ((hE b c).2.contDiff.of_le le_top).contMDiff
  have hEfor : ContMDiff (𝓘(ℝ, T)) (𝓘(ℝ, L × ℝ)) ∞ E :=
    ((hE b c).1.contDiff.of_le le_top).contMDiff
  refine ⟨{
    carrier := T
    nilpotent := derivationLieSpace_nilpotent D hD
    embed := j
    injective := E.symm.injective.comp (e.symm.injective.comp hI)
    kernel_smooth := ?_
    dimension := C.dimension + 1
    basis := b
    parameter := p
    polynomial := hp.1
    polynomial_symm := hp.2
    integer_grid := ?_
    extend := ?_ }, rfl⟩
  · have heq : (j.comp ((SemidirectProduct.inl : H →*
        H ⋊[integerPowerAction a] Multiplicative ℤ).comp i) : K → T) =
        fun x => E.symm (C.embed (i x), 0) := by
      funext x
      apply E.injective
      rw [E.apply_symm_apply]
      change E (j (SemidirectProduct.inl (i x))) = (C.embed (i x), 0)
      rw [hj]
      simp
    rw [heq]
    exact hEinv.comp (C.kernel_smooth.prodMk_space contMDiff_const)
  · intro z
    obtain ⟨h, hh⟩ := C.integer_grid (fun k => z k.castSucc)
    refine ⟨⟨h, Multiplicative.ofAdd (z (Fin.last C.dimension))⟩, ?_⟩
    apply E.injective
    rw [hj]
    have hparam := transportedProductParameter_integer C.basis C.parameter s E.toEquiv z
    change E (p (b.equivFun.symm (fun k => (z k : ℝ)))) =
      (C.parameter (C.basis.equivFun.symm (fun k => (z k.castSucc : ℝ))),
        (z (Fin.last C.dimension) : ℝ)) at hparam
    rw [hparam, hh]
    rfl
  · intro M _ _ PM hnil F hF
    obtain ⟨r, hr, hre⟩ := kernelCompletion_cyclic_hom C a A hA hAe F hF
    let f := r.comp E.toMonoidHom
    refine ⟨f, hr.comp hEfor, ?_⟩
    intro z
    change r (E (j z)) = F z
    rw [hj]
    exact hre z.left z.right.toAdd

theorem cyclic_step (a : MulAut H) (A : C.carrier ≃ₗ⁅ℝ⁆ C.carrier)
    (hA : IsNilpotent (A.toLinearMap - 1))
    (hAe : ∀ h, A (C.embed h) = C.embed (a h)) :
    Nonempty (NilpotentKernelCompletion
      ((SemidirectProduct.inl : H →* H ⋊[integerPowerAction a] Multiplicative ℤ).comp i)) := by
  obtain ⟨C', _⟩ := C.cyclic_step_with_dimension a A hA hAe
  exact ⟨C'⟩

end NilpotentKernelCompletion
end PolycyclicRecognition

end

end OAI
