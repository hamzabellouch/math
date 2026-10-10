import Mathlib.Analysis.Normed.Field.Dense
import Mathlib.Analysis.Normed.Field.Instances
import Mathlib.Analysis.Normed.Module.Completion
import Mathlib.Analysis.Normed.Algebra.Ultra
import Mathlib.Topology.Baire.CompleteMetrizable

namespace OAI

/-! # Complete algebraically closed extensions of nonarchimedean fields -/

noncomputable section
universe u
namespace PolycyclicRecognition

theorem uncountable_complete_normedField
    (K : Type*) [NontriviallyNormedField K] [CompleteSpace K] : Uncountable K := by
  rw [← not_countable_iff]
  intro h
  let : Countable K := h
  obtain ⟨x, hx⟩ := nonempty_interior_of_iUnion_of_closed
    (f := fun x : K => ({x} : Set K)) (fun _ => isClosed_singleton) (by
      ext y
      exact ⟨fun _ => Set.mem_univ y, fun _ => Set.mem_iUnion.mpr ⟨y, rfl⟩⟩)
  simp only [interior_singleton, Set.not_nonempty_empty] at hx

theorem exists_complete_algebraicallyClosed_normed_extension
    (K : Type u) [NontriviallyNormedField K] [CompleteSpace K]
    [CharZero K] [IsUltrametricDist K] :
    ∃ (L : Type u) (_ : NontriviallyNormedField L) (_ : CompleteSpace L)
      (_ : IsAlgClosed L) (f : K →+* L), ∀ x, ‖f x‖ = ‖x‖ := by
  let E := AlgebraicClosure K
  let : NontriviallyNormedField E := spectralNorm.nontriviallyNormedField K E
  let : NormedAlgebra K E := spectralNorm.normedAlgebra K E
  let : IsUltrametricDist E := IsUltrametricDist.of_normedAlgebra K
  let L := UniformSpace.Completion E
  let : NontriviallyNormedField L := NontriviallyNormedField.ofNormNeOne (by
    obtain ⟨x, hx⟩ := NormedField.exists_one_lt_norm E
    refine ⟨(x : L), ?_, ?_⟩
    · exact (map_ne_zero (algebraMap E L)).mpr ((norm_pos_iff).mp (zero_lt_one.trans hx))
    · have hh : ‖(x : L)‖ = ‖x‖ := UniformSpace.Completion.norm_coe x
      rw [hh]
      exact ne_of_gt hx)
  let : CharZero L :=
    (RingHom.charZero_iff (algebraMap E L).injective).mp inferInstance
  let : IsUltrametricDist L := IsUltrametricDist.of_normedAlgebra K
  let : IsAlgClosed L :=
    IsAlgClosed.of_denseRange (K := E) UniformSpace.Completion.denseRange_coe
  refine ⟨L, inferInstance, inferInstance, inferInstance,
    (algebraMap E L).comp (algebraMap K E), ?_⟩
  intro x
  change ‖((algebraMap K E x : E) : L)‖ = ‖x‖
  rw [UniformSpace.Completion.norm_coe]
  exact spectralNorm_extends x

end PolycyclicRecognition

end

end OAI
