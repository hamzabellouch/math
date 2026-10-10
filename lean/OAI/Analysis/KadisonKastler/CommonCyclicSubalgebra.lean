import OAI.Analysis.KadisonKastler.FaithfulCyclicConstruction
import OAI.Analysis.KadisonKastler.NormalRepresentationRange

namespace OAI

/-! # The common subalgebra in the faithful cyclic representation -/

namespace KadisonKastler

noncomputable section

open Generator Generator.Tracial Filter

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [Nontrivial H] [TopologicalSpace.SeparableSpace H]
  (M R : VonNeumannAlgebra H) (hRM : R ≤ M)

def cyclicCommonHom : Algebra R →⋆ₐ[ℂ]
    (faithfulCyclicSpace M →L[ℂ] faithfulCyclicSpace M) :=
  (faithfulCyclicHom M).comp (coordinateInclusion hRM)

def cyclicCommonAlgebra : VonNeumannAlgebra (faithfulCyclicSpace M) :=
  generatedVonNeumannAlgebra (cyclicCommonHom M R hRM).range

theorem cyclicCommonHom_injective : Function.Injective (cyclicCommonHom M R hRM) := by
  intro a b hab
  have h := faithfulCyclicHom_injective M hab
  exact Subtype.ext (congrArg (fun x : Algebra M => x.val) h)

omit [Nontrivial H] in
theorem cyclicCommonHom_normal : BoundedWeakNormal R (cyclicCommonHom M R hRM) := by
  intro ι l a b C hn hw x y
  exact faithfulCyclicHom_tendsto_weak M
    (fun i => coordinateInclusion hRM (a i)) (coordinateInclusion hRM b) C hn hw x y

def cyclicCommonEquiv : Algebra R ≃⋆ₐ[ℂ] Algebra (cyclicCommonAlgebra M R hRM) :=
  boundedWeakNormalEquiv R (cyclicCommonHom M R hRM)
    (cyclicCommonHom_injective M R hRM) (cyclicCommonHom_normal M R hRM)

omit [Nontrivial H] in
theorem cyclicCommon_le : cyclicCommonAlgebra M R hRM ≤ faithfulCyclicAlgebra M := by
  apply generatedVonNeumannAlgebra_le_of_le
  rintro T ⟨r, rfl⟩
  exact subset_generatedVonNeumannAlgebra _ ⟨coordinateInclusion hRM r, rfl⟩

theorem cyclicCommon_restrict (r : Algebra R) :
    faithfulCyclicEquiv M (coordinateInclusion hRM r) =
      coordinateInclusion (cyclicCommon_le M R hRM) (cyclicCommonEquiv M R hRM r) := rfl

omit [Nontrivial H] in
theorem cyclicCommon_le_neighbor (P : VonNeumannAlgebra (faithfulCyclicSpace M))
    (e : Algebra R →⋆ₐ[ℂ] Algebra P)
    (he : ∀ r, (e r).val = faithfulCyclicHom M (coordinateInclusion hRM r)) :
    cyclicCommonAlgebra M R hRM ≤ P := by
  apply generatedVonNeumannAlgebra_le_of_le
  rintro T ⟨r, rfl⟩
  change faithfulCyclicHom M (coordinateInclusion hRM r) ∈ P
  rw [← he r]
  exact (e r).property

theorem cyclicCommon_neighbor_restrict (P : VonNeumannAlgebra (faithfulCyclicSpace M))
    (e : Algebra R →⋆ₐ[ℂ] Algebra P)
    (he : ∀ r, (e r).val = faithfulCyclicHom M (coordinateInclusion hRM r))
    (r : Algebra R) :
    e r = coordinateInclusion (cyclicCommon_le_neighbor M R hRM P e he)
      (cyclicCommonEquiv M R hRM r) := by
  apply Subtype.ext
  exact he r

end

end KadisonKastler

end OAI
