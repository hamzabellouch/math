import OAI.Analysis.IrrationalRotation.Operators.JointEigenprojection
import OAI.Analysis.IrrationalRotation.Operators.JointEigenspaceAlgebra
import Mathlib.Analysis.InnerProductSpace.Spectrum

namespace OAI

noncomputable section
open scoped Pointwise

namespace Invariant233

variable {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

theorem coe_generated_range_selfAdjoint (D : ι → H →L[ℂ] H)
    (hD : ∀ i, IsSelfAdjoint (D i)) :
    (vonNeumannGenerated (Set.range D) : Set (H →L[ℂ] H)) =
      Set.centralizer (Set.centralizer (Set.range D)) := by
  rw [coe_vonNeumannGenerated]
  have hstar : star (Set.range D) ⊆ Set.range D := by
    intro T hT
    change star T ∈ Set.range D at hT
    obtain ⟨i, hi⟩ := hT
    refine ⟨i, ?_⟩
    calc
      D i = star (D i) := (hD i).star_eq.symm
      _ = T := by rw [hi, star_star]
  rw [Set.union_eq_left.mpr hstar]

theorem jointEigenprojection_isProjectionAtom (D : ι → H →L[ℂ] H)
    (hD : ∀ i, IsSelfAdjoint (D i)) (ev : ι → ℂ)
    (hp0 : jointEigenprojection D ev ≠ 0) :
    IsProjectionAtom (vonNeumannGenerated (Set.range D)) (jointEigenprojection D ev) := by
  have hK0 : jointEigenspace D ev ≠ ⊥ := by
    intro hK
    apply hp0
    ext x
    have hx := (jointEigenspace D ev).starProjection_apply_mem x
    change (jointEigenspace D ev).starProjection x = 0
    exact (le_of_eq hK) hx
  obtain ⟨x, hxK, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hK0
  have hreal : ∀ i, ((ev i).re : ℂ) = ev i := by
    intro i
    apply Complex.conj_eq_iff_re.mp
    apply (hD i).isSymmetric.conj_eigenvalue_eq_self
    apply Module.End.hasEigenvalue_of_hasEigenvector
    exact ⟨Module.End.mem_eigenspace_iff.mpr ((mem_jointEigenspace.mp hxK) i), hx0⟩
  refine ⟨jointEigenprojection_mem_generated D ev,
    isStarProjection_jointEigenprojection D ev, hp0, ?_⟩
  intro q hqm hqp hle
  apply JointEigenspaceAlgebra.eq_zero_or_eq_joint_projection_of_le
    D hD (fun i => (ev i).re) (jointEigenspace D ev)
  · intro i y hy
    rw [hreal i]
    exact (mem_jointEigenspace.mp hy) i
  · exact hqp
  · change q ∈ (vonNeumannGenerated (Set.range D) : Set (H →L[ℂ] H)) at hqm
    rwa [coe_generated_range_selfAdjoint D hD] at hqm
  · exact (hqp.le_iff_mul_eq_left (isStarProjection_jointEigenprojection D ev)).mpr hle

theorem atomic_generated_of_dense_jointEigenspaces {A : Type*}
    (D : ι → H →L[ℂ] H) (ev : A → ι → ℂ)
    (hD : ∀ i, IsSelfAdjoint (D i))
    (hdense : (⨆ a, jointEigenspace D (ev a)).topologicalClosure = ⊤) :
    IsAtomicVonNeumannAlgebra (vonNeumannGenerated (Set.range D)) := by
  apply atomic_generated_of_jointEigenprojection_atoms D ev hD hdense
  intro a
  exact jointEigenprojection_isProjectionAtom D hD (ev a)

end Invariant233

end

end OAI
