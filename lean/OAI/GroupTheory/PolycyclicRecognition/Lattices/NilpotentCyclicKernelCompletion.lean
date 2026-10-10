import OAI.GroupTheory.PolycyclicRecognition.Lattices.KernelCompletionCyclicStep
import OAI.GroupTheory.PolycyclicRecognition.Lattices.KernelCompletionUnipotentLift
import OAI.GroupTheory.PolycyclicRecognition.Lattices.KernelCompletionTransport
import OAI.GroupTheory.PolycyclicRecognition.Algebra.CyclicKernelSplitting

namespace OAI

/-! # Completing a nilpotent group across an actual cyclic quotient -/

noncomputable section
namespace PolycyclicRecognition
open scoped Manifold ContDiff
variable {K G : Type} [RealNormedLieAlgebra K] [FiniteDimensional ℝ K]
  [PK : PolynomialExponentialCoordinates K] [Group G] [Group.IsNilpotent G]

theorem nilpotent_cyclic_kernel_completion_with_dimension (q : G →* Multiplicative ℤ)
    (t : G) (ht : q t = Multiplicative.ofAdd 1)
    (i : K →* q.ker) (C : NilpotentKernelCompletion i)
    (ha : ContMDiff (𝓘(ℝ, K)) (𝓘(ℝ, C.carrier)) ∞
      ((C.embed.comp (MulAut.conjNormal (H := q.ker) t).toMonoidHom).comp i))
    (hai : ContMDiff (𝓘(ℝ, K)) (𝓘(ℝ, C.carrier)) ∞
      ((C.embed.comp (MulAut.conjNormal (H := q.ker) t).symm.toMonoidHom).comp i)) :
    ∃ D : NilpotentKernelCompletion (q.ker.subtype.comp i),
      D.dimension = C.dimension + 1 := by
  let a := MulAut.conjNormal (H := q.ker) t
  obtain ⟨A, hA, hAe⟩ := C.unipotent_conjugation_extension q.ker.subtype
    Subtype.val_injective a t (fun _ => rfl) ha hai
  obtain ⟨D, hD⟩ := C.cyclic_step_with_dimension a A hA hAe
  let e := cyclicKernelEquiv q t ht
  have he : e.toMonoidHom.comp ((SemidirectProduct.inl : q.ker →*
        q.ker ⋊[integerPowerAction a] Multiplicative ℤ).comp i) = q.ker.subtype.comp i := by
    ext x
    change (i x : G) * t ^ (1 : Multiplicative ℤ).toAdd = (i x : G)
    simp
  rw [← he]
  exact ⟨D.of_equiv e, hD⟩

theorem nilpotent_cyclic_kernel_completion (q : G →* Multiplicative ℤ)
    (t : G) (ht : q t = Multiplicative.ofAdd 1)
    (i : K →* q.ker) (C : NilpotentKernelCompletion i)
    (ha : ContMDiff (𝓘(ℝ, K)) (𝓘(ℝ, C.carrier)) ∞
      ((C.embed.comp (MulAut.conjNormal (H := q.ker) t).toMonoidHom).comp i))
    (hai : ContMDiff (𝓘(ℝ, K)) (𝓘(ℝ, C.carrier)) ∞
      ((C.embed.comp (MulAut.conjNormal (H := q.ker) t).symm.toMonoidHom).comp i)) :
    Nonempty (NilpotentKernelCompletion (q.ker.subtype.comp i)) := by
  obtain ⟨D, _⟩ := nilpotent_cyclic_kernel_completion_with_dimension q t ht i C ha hai
  exact ⟨D⟩

end PolycyclicRecognition

end

end OAI
