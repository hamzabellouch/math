import OAI.Analysis.Laughlin.Exterior.SpinUnitary
import OAI.Analysis.Laughlin.Spin.ParticleSpinAction

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators Matrix
open Rotation

noncomputable def tensorExterior (N Q : ℕ) (ψ : State N Q) : Space Q :=
  ∑ a, ψ a • ExteriorAlgebra.ιMulti ℂ N (fun k => mode (a k))

theorem orbitalRotation_mode (Q : ℕ) (g : SourceSU2) (i : Fin (Q+1)) :
    orbitalRotation Q g (mode i) = ∑ j, sourceSpinRepresentation Q g j i • mode j := by
  rw [orbital_sum_modes Q (orbitalRotation Q g (mode i))]
  apply Finset.sum_congr rfl
  intro j hj
  congr 1
  simp [orbitalRotation,mode,Matrix.mulVec,dotProduct,Pi.single_apply]

theorem exteriorRotation_basis_wedge (N Q : ℕ) (g : SourceSU2) (a : Configuration N Q) :
    exteriorRotation Q g (ExteriorAlgebra.ιMulti ℂ N (fun k => mode (a k))) =
      ∑ b : Configuration N Q, (∏ k, sourceSpinRepresentation Q g (b k) (a k)) •
        ExteriorAlgebra.ιMulti ℂ N (fun k => mode (b k)) := by
  unfold exteriorRotation
  rw [ExteriorAlgebra.map_apply_ιMulti]
  change ExteriorAlgebra.ιMulti ℂ N (fun k => orbitalRotation Q g (mode (a k))) = _
  simp_rw [orbitalRotation_mode]
  change (ExteriorAlgebra.ιMulti ℂ N).toMultilinearMap
    (fun k => ∑ j, sourceSpinRepresentation Q g j (a k) • mode j) = _
  rw [MultilinearMap.map_sum]
  apply Finset.sum_congr rfl
  intro b hb
  exact (ExteriorAlgebra.ιMulti ℂ N).map_smul_univ _ _

theorem tensorExterior_rotation (N Q : ℕ) (g : SourceSU2) (ψ : State N Q) :
    exteriorRotation Q g (tensorExterior N Q ψ) =
      tensorExterior N Q (sourceParticleRepresentation N Q g *ᵥ ψ) := by
  simp only [tensorExterior,map_sum,map_smul,exteriorRotation_basis_wedge,Finset.smul_sum,smul_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b hb
  rw [← Finset.sum_smul]
  congr 1
  change (∑ a, ψ a * ∏ k, sourceSpinRepresentation Q g (b k) (a k)) =
    ∑ a, (∏ k, sourceSpinRepresentation Q g (b k) (a k))*ψ a
  simp only [mul_comm]

end Laughlin.Fock

end OAI
