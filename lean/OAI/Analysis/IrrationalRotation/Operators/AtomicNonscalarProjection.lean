import OAI.Analysis.IrrationalRotation.Model.ConcreteSpectral
import OAI.Analysis.IrrationalRotation.Operators.JointEigenprojection

namespace OAI

noncomputable section
namespace Invariant233

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

theorem exists_nontrivial_projection_of_atomic_nonscalar
    (M : VonNeumannAlgebra H) (B : H →L[ℂ] H)
    (hB : B ∈ M) (hatomic : HasCountablyAtomicSpectralType B)
    (hnonscalar : ¬ ∃ c : ℂ, B = c • (1 : H →L[ℂ] H)) :
    ∃ q : H →L[ℂ] H, q ∈ M ∧ IsStarProjection q ∧ q ≠ 0 ∧ q ≠ 1 := by
  obtain ⟨S, _, hdense⟩ := hatomic
  let D : Unit → H →L[ℂ] H := fun _ => B
  let ev : S → Unit → ℂ := fun z _ => z.val
  have hdense' : (⨆ z : S, jointEigenspace D (ev z)).topologicalClosure = ⊤ := by
    simpa only [jointEigenspace, D, ev, iInf_const] using hdense
  have hB0 : B ≠ 0 := by
    intro hz
    exact hnonscalar ⟨0, by simpa using hz⟩
  obtain ⟨z, hz⟩ := exists_mul_jointEigenprojection_ne_zero D ev hdense' B hB0
  let q := jointEigenprojection D (ev z)
  have hqmem : q ∈ M := by
    apply vonNeumannGenerated_le (Set.range D) M _ (jointEigenprojection_mem_generated D (ev z))
    rintro A ⟨i, rfl⟩
    exact hB
  refine ⟨q, hqmem, isStarProjection_jointEigenprojection D (ev z), ?_, ?_⟩
  · intro hq0
    apply hz
    change B * q = 0
    rw [hq0, mul_zero]
  · intro hq1
    apply hnonscalar
    refine ⟨z.val, ?_⟩
    ext x
    have hx : x ∈ jointEigenspace D (ev z) := by
      apply Submodule.starProjection_eq_self_iff.mp
      change q x = x
      rw [hq1]
      rfl
    exact (mem_jointEigenspace.mp hx) ()

end Invariant233

end

end OAI
