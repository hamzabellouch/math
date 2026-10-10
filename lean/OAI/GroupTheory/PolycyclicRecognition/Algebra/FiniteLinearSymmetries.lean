import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.LinearAlgebra.Span.Basic

namespace OAI

/-!
# Finiteness of linear height symmetries

The finite-symmetry step used in Lemma `support-symmetries` reduces to
permuting a finite spanning collection of covectors. The elementary linear
algebra fact proved here applies equally to vectors in the dual height space.
It does not assume that the permutation of covectors determines a symmetry:
it proves uniqueness from the spanning hypothesis.
-/

namespace PolycyclicRecognition

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- There are only finitely many invertible continuous linear maps preserving
a fixed finite spanning collection of vectors. -/
theorem finite_linear_symmetries (s : Finset W)
    (hspan : Submodule.span ℝ (s : Set W) = ⊤) :
    Set.Finite {A : W ≃L[ℝ] W | ∀ w ∈ s, A w ∈ s} := by
  classical
  let Sym := {A : W ≃L[ℝ] W // ∀ w ∈ s, A w ∈ s}
  let restrict : Sym → (s → s) := fun A w => ⟨A.val w, A.property w w.property⟩
  have hinj : Function.Injective restrict := by
    intro A B hab
    apply Subtype.ext
    have heq : A.val.toLinearMap = B.val.toLinearMap := by
      apply LinearMap.ext_on hspan
      intro w hw
      exact congrArg Subtype.val (congrFun hab ⟨w, hw⟩)
    ext w
    exact congrArg (fun L : W →ₗ[ℝ] W => L w) heq
  have hfinite : Finite Sym := Finite.of_injective restrict hinj
  exact Set.finite_coe_iff.mp hfinite

/-- A family preserving the same finite spanning set has finitely many linear
parts, supplying the finiteness hypothesis of the height homomorphism theorem. -/
theorem finite_range_of_preserves_spanning_finset {H : Type*}
    (A : H → W ≃L[ℝ] W) (s : Finset W)
    (hspan : Submodule.span ℝ (s : Set W) = ⊤)
    (hpreserve : ∀ h w, w ∈ s → A h w ∈ s) :
    Set.Finite (Set.range A) := by
  apply (finite_linear_symmetries s hspan).subset
  rintro _ ⟨h, rfl⟩
  exact hpreserve h

end PolycyclicRecognition

end OAI
