import OAI.GroupTheory.PolycyclicRecognition.Lattices.NilpotentKernelCompletion

namespace OAI

/-! # Transporting a constructed completion across an exact group isomorphism -/

noncomputable section
namespace PolycyclicRecognition
open scoped Manifold ContDiff
variable {K H J : Type} [RealNormedLieAlgebra K] [FiniteDimensional ℝ K]
  [PK : PolynomialExponentialCoordinates K] [Group H] [Group J]
  {i : K →* H}

namespace NilpotentKernelCompletion

def of_equiv (C : NilpotentKernelCompletion i) (e : H ≃* J) :
    NilpotentKernelCompletion (e.toMonoidHom.comp i) where
  carrier := C.carrier
  embed := C.embed.comp e.symm.toMonoidHom
  injective := C.injective.comp e.symm.injective
  kernel_smooth := by
    convert C.kernel_smooth using 1
    ext x
    exact congrArg C.embed (e.symm_apply_apply (i x))
  dimension := C.dimension
  basis := C.basis
  parameter := C.parameter
  polynomial := C.polynomial
  polynomial_symm := C.polynomial_symm
  integer_grid z := by
    obtain ⟨h, hh⟩ := C.integer_grid z
    refine ⟨e h, ?_⟩
    simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, e.symm_apply_apply] using hh
  extend M _ _ _ _ f hf := by
    obtain ⟨φ, hφ, he⟩ := C.extend M (f.comp e.toMonoidHom) hf
    refine ⟨φ, hφ, ?_⟩
    intro j
    exact (he (e.symm j)).trans (congrArg f (e.apply_symm_apply j))

theorem exists_of_bijective_kernel_with_dimension [LieRing.IsNilpotent K]
    (i : K →* H) (hi : Function.Bijective i) :
    ∃ C : NilpotentKernelCompletion i, C.dimension = Module.finrank ℝ K := by
  let e := MulEquiv.ofBijective i hi
  have he : e.toMonoidHom.comp (MonoidHom.id K) = i := by ext x; rfl
  rw [← he]
  exact ⟨of_equiv of_polynomial_kernel e, rfl⟩

theorem exists_of_bijective_kernel [LieRing.IsNilpotent K]
    (i : K →* H) (hi : Function.Bijective i) : Nonempty (NilpotentKernelCompletion i) := by
  obtain ⟨C, _⟩ := exists_of_bijective_kernel_with_dimension i hi
  exact ⟨C⟩

end NilpotentKernelCompletion
end PolycyclicRecognition

end

end OAI
