import OAI.Analysis.Laughlin.Exterior.SpinAction
import OAI.Analysis.Laughlin.Operators.PositiveFockLift

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators Matrix
open Rotation

noncomputable def orbitalDual (Q : ℕ) (v : Orbital Q) : Module.Dual ℂ (Orbital Q) :=
  ∑ i, star (v i) • LinearMap.proj i

noncomputable def vectorAnnihilate (Q : ℕ) (v : Orbital Q) : Module.End ℂ (Space Q) :=
  CliffordAlgebra.contractLeft (orbitalDual Q v)

theorem vectorAnnihilate_sum (Q : ℕ) (v : Orbital Q) (x : Space Q) :
    vectorAnnihilate Q v x = ∑ i, star (v i) • annihilate i x := by
  simp only [vectorAnnihilate,orbitalDual,map_sum,map_smul,LinearMap.sum_apply,LinearMap.smul_apply,annihilate]

theorem vectorCreate_sum (Q : ℕ) (v : Orbital Q) (x : Space Q) :
    ExteriorAlgebra.ι ℂ v*x = ∑ i, v i • create i x := by
  conv_lhs => rw [orbital_sum_modes Q v]
  simp only [map_sum,map_smul,Finset.sum_mul,smul_mul_assoc]
  rfl

theorem vectorCreate_adjoint (Q : ℕ) (v : Orbital Q) (x y : Space Q) :
    occupationInner Q (ExteriorAlgebra.ι ℂ v*x) y =
      occupationInner Q x (vectorAnnihilate Q v y) := by
  rw [vectorCreate_sum,vectorAnnihilate_sum]
  simp only [occupationInner_sum_left,occupationInner_sum_right,occupationInner_smul_left,
    occupationInner_smul_right,create_annihilate_adjoint]

theorem orbitalDual_rotation (Q : ℕ) (g : SourceSU2) (v : Orbital Q) :
    (orbitalDual Q (orbitalRotation Q g v)).comp (orbitalRotation Q g) = orbitalDual Q v := by
  apply LinearMap.ext
  intro w
  simp only [orbitalDual,LinearMap.comp_apply,LinearMap.sum_apply,LinearMap.smul_apply]
  change star (sourceSpinRepresentation Q g *ᵥ v) ⬝ᵥ (sourceSpinRepresentation Q g *ᵥ w) = star v ⬝ᵥ w
  rw [Matrix.star_mulVec,Matrix.dotProduct_mulVec,Matrix.vecMul_vecMul]
  have hu := Matrix.mem_unitaryGroup_iff'.mp (sourceSpinRepresentation_unitary Q g)
  rw [Matrix.star_eq_conjTranspose] at hu
  rw [hu,Matrix.vecMul_one]

theorem vectorAnnihilate_rotation (Q : ℕ) (g : SourceSU2) (v : Orbital Q) (x : Space Q) :
    vectorAnnihilate Q (orbitalRotation Q g v) (exteriorRotation Q g x) =
      exteriorRotation Q g (vectorAnnihilate Q v x) := by
  unfold vectorAnnihilate exteriorRotation
  rw [contraction_map,orbitalDual_rotation]

end Laughlin.Fock

end OAI
