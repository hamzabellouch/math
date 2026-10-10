import Mathlib.Algebra.Module.Submodule.Union
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
import Mathlib.Analysis.Normed.Module.Basic

namespace OAI

/-!
# One global label from finite pointwise linear choices

The profile affinity criterion shows that a linear derivative
agrees at each vector with one of finitely many linear symmetry maps. The label
cannot depend on the vector: otherwise finitely many proper linear kernels
would cover the real vector space.
-/

namespace PolycyclicRecognition

universe u v

/-- A real linear map which agrees pointwise with a finite family of real linear
maps agrees with one member of the family everywhere. -/
theorem exists_eq_of_pointwise_linear_selection
    {ι : Type u} [Finite ι] {W : Type v} [AddCommGroup W] [Module ℝ W]
    (B : W →ₗ[ℝ] W) (A : ι → W →ₗ[ℝ] W)
    (hpointwise : ∀ w, ∃ i, B w = A i w) :
    ∃ i, B = A i := by
  classical
  by_contra hnone
  have hne (i : ι) : B ≠ A i := fun hi => hnone ⟨i, hi⟩
  have hproper (i : ι) : LinearMap.ker (B - A i) ≠ ⊤ := by
    intro hker
    apply hne i
    apply LinearMap.ext
    intro w
    have hmem : w ∈ LinearMap.ker (B - A i) := by
      rw [hker]
      trivial
    exact sub_eq_zero.mp (LinearMap.mem_ker.mp hmem)
  obtain ⟨w, hw⟩ :=
    Submodule.exists_forall_notMem_of_forall_ne_top (fun i => LinearMap.ker (B - A i)) hproper
  obtain ⟨i, hi⟩ := hpointwise w
  apply hw i
  exact LinearMap.mem_ker.mpr (sub_eq_zero.mpr hi)

/-- In particular, pointwise choices from finitely many continuous linear
symmetries give one continuous linear symmetry on the entire space. -/
theorem exists_eq_of_pointwise_continuous_symmetry
    {ι : Type u} [Finite ι] {W : Type v} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (B : W →L[ℝ] W) (A : ι → W ≃L[ℝ] W)
    (hpointwise : ∀ w, ∃ i, B w = A i w) :
    ∃ i, B = (A i).toContinuousLinearMap := by
  obtain ⟨i, hi⟩ := exists_eq_of_pointwise_linear_selection B.toLinearMap
    (fun i => (A i).toLinearEquiv.toLinearMap) hpointwise
  refine ⟨i, ?_⟩
  apply ContinuousLinearMap.ext
  intro w
  exact congrArg (fun L : W →ₗ[ℝ] W => L w) hi

end PolycyclicRecognition

end OAI
