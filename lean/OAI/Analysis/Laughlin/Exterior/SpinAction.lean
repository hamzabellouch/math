import OAI.Analysis.Laughlin.Exterior.Scaling
import OAI.Analysis.Laughlin.Spin.Disjoint

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators Matrix
open Rotation

noncomputable def orbitalRotation (Q : ℕ) (g : SourceSU2) : Orbital Q →ₗ[ℂ] Orbital Q where
  toFun v := sourceSpinRepresentation Q g *ᵥ v
  map_add' v w := Matrix.mulVec_add _ v w
  map_smul' c v := Matrix.mulVec_smul _ c v

noncomputable def exteriorRotation (Q : ℕ) (g : SourceSU2) : Space Q →ₐ[ℂ] Space Q :=
  ExteriorAlgebra.map (orbitalRotation Q g)

theorem orbitalRotation_mul (Q : ℕ) (g h : SourceSU2) :
    (orbitalRotation Q g).comp (orbitalRotation Q h) = orbitalRotation Q (g*h) := by
  apply LinearMap.ext
  intro v
  funext i
  change (sourceSpinRepresentation Q g *ᵥ (sourceSpinRepresentation Q h *ᵥ v)) i = _
  rw [Matrix.mulVec_mulVec,← map_mul]
  rfl

theorem orbitalRotation_one (Q : ℕ) : orbitalRotation Q 1 = LinearMap.id := by
  apply LinearMap.ext
  intro v
  funext i
  simp [orbitalRotation]

theorem exteriorRotation_mul (Q : ℕ) (g h : SourceSU2) (x : Space Q) :
    exteriorRotation Q g (exteriorRotation Q h x) = exteriorRotation Q (g*h) x := by
  change ((ExteriorAlgebra.map (orbitalRotation Q g)).comp
    (ExteriorAlgebra.map (orbitalRotation Q h))) x = _
  rw [ExteriorAlgebra.map_comp_map,orbitalRotation_mul]
  rfl

theorem exteriorRotation_one (Q : ℕ) (x : Space Q) : exteriorRotation Q 1 x = x := by
  unfold exteriorRotation
  rw [orbitalRotation_one,ExteriorAlgebra.map_id]
  rfl

theorem exteriorRotation_inverse (Q : ℕ) (g : SourceSU2) (x : Space Q) :
    exteriorRotation Q g⁻¹ (exteriorRotation Q g x) = x := by
  rw [exteriorRotation_mul,inv_mul_cancel,exteriorRotation_one]

theorem orbital_sum_modes (Q : ℕ) (v : Orbital Q) : v = ∑ i, v i • mode i := by
  funext j
  simp [mode,Pi.single_apply]

theorem projection_orbitalRotation (Q : ℕ) (g : SourceSU2) (i : Fin (Q+1)) :
    (LinearMap.proj i).comp (orbitalRotation Q g) =
      ∑ j, sourceSpinRepresentation Q g i j • LinearMap.proj j := by
  ext v
  simp [orbitalRotation,Matrix.mulVec,dotProduct,LinearMap.proj]

theorem annihilate_exteriorRotation (Q : ℕ) (g : SourceSU2) (i : Fin (Q+1)) (x : Space Q) :
    annihilate i (exteriorRotation Q g x) =
      ∑ j, sourceSpinRepresentation Q g i j • exteriorRotation Q g (annihilate j x) := by
  unfold annihilate exteriorRotation
  rw [contraction_map,projection_orbitalRotation]
  simp only [map_sum,map_smul,LinearMap.sum_apply,LinearMap.smul_apply]

theorem create_exteriorRotation (Q : ℕ) (g : SourceSU2) (i : Fin (Q+1)) (x : Space Q) :
    exteriorRotation Q g (create i x) =
      ∑ j, sourceSpinRepresentation Q g j i • create j (exteriorRotation Q g x) := by
  change ExteriorAlgebra.map (orbitalRotation Q g) (ExteriorAlgebra.ι ℂ (mode i)*x) = _
  rw [map_mul,ExteriorAlgebra.map_apply_ι,orbital_sum_modes Q (orbitalRotation Q g (mode i))]
  simp only [map_sum,map_smul,Finset.sum_mul,smul_mul_assoc]
  apply Finset.sum_congr rfl
  intro j hj
  have he : orbitalRotation Q g (mode i) j = sourceSpinRepresentation Q g j i := by
    simp [orbitalRotation,mode,Matrix.mulVec,dotProduct,Pi.single_apply]
  rw [he]
  rfl

end Laughlin.Fock

end OAI
