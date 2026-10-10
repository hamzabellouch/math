import OAI.Analysis.Laughlin.Polynomial.SymmetricTensorRange
import OAI.Analysis.Laughlin.Spin.Haar

namespace OAI

namespace Laughlin.Rotation
open scoped BigOperators Matrix

noncomputable def sourceSpinMatrix (Q : ℕ) (g : SourceSU2) : Matrix (Fin (Q+1)) (Fin (Q+1)) ℂ :=
  (symmetricTensorInclusion Q)ᴴ * sourceTensorRepresentation Q g * symmetricTensorInclusion Q

 theorem tensor_spin_intertwining (Q : ℕ) (g : SourceSU2) :
    symmetricTensorInclusion Q*sourceSpinMatrix Q g = sourceTensorRepresentation Q g*symmetricTensorInclusion Q := by
  ext a p
  let v : (Fin Q → Fin 2) → ℂ := fun b => symmetricTensorInclusion Q b p
  have hv : ∀ b c, tensorWeight Q b=tensorWeight Q c → v b=v c := by
    intro b c h
    simp only [v,symmetricTensorInclusion,Matrix.map_apply,symmetricTensorInclusionReal,h]
  have hf := tensorMatrix_preserves_symmetric Q g.val v hv
  have he := congrFun (symmetricTensor_projector_fixed Q (sourceTensorRepresentation Q g *ᵥ v) hf) a
  change (symmetricTensorInclusion Q*((symmetricTensorInclusion Q)ᴴ*sourceTensorRepresentation Q g*symmetricTensorInclusion Q)) a p = _
  calc
    _ = ((symmetricTensorInclusion Q*(symmetricTensorInclusion Q)ᴴ)*
      (sourceTensorRepresentation Q g*symmetricTensorInclusion Q)) a p := by simp only [Matrix.mul_assoc]
    _ = _ := he

 theorem sourceSpinMatrix_mul (Q : ℕ) (g h : SourceSU2) :
    sourceSpinMatrix Q (g*h)=sourceSpinMatrix Q g*sourceSpinMatrix Q h := by
  unfold sourceSpinMatrix
  rw [map_mul]
  have he := tensor_spin_intertwining Q h
  unfold sourceSpinMatrix at he
  calc
    _ = (symmetricTensorInclusion Q)ᴴ*sourceTensorRepresentation Q g*
        (sourceTensorRepresentation Q h*symmetricTensorInclusion Q) := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [← he]; simp only [Matrix.mul_assoc]

 theorem sourceSpinMatrix_one (Q : ℕ) : sourceSpinMatrix Q 1=1 := by
  simp only [sourceSpinMatrix,map_one,Matrix.mul_one,symmetricTensorInclusion_isometry]

noncomputable def sourceSpinRepresentation (Q : ℕ) : SourceSU2 →* Matrix (Fin (Q+1)) (Fin (Q+1)) ℂ where
  toFun := sourceSpinMatrix Q
  map_one' := sourceSpinMatrix_one Q
  map_mul' := sourceSpinMatrix_mul Q

 theorem sourceSpinRepresentation_unitary (Q : ℕ) (g : SourceSU2) :
    sourceSpinRepresentation Q g ∈ Matrix.unitaryGroup (Fin (Q+1)) ℂ := by
  have he := congrArg (fun M => Mᴴ*M) (tensor_spin_intertwining Q g)
  have hu := Matrix.mem_unitaryGroup_iff'.mp (sourceTensorRepresentation_unitary Q g)
  rw [Matrix.star_eq_conjTranspose] at hu
  simp only [Matrix.conjTranspose_mul] at he
  have hleft : (sourceSpinMatrix Q g)ᴴ*(symmetricTensorInclusion Q)ᴴ*
      (symmetricTensorInclusion Q*sourceSpinMatrix Q g) = (sourceSpinMatrix Q g)ᴴ*sourceSpinMatrix Q g := by
    rw [Matrix.mul_assoc,← Matrix.mul_assoc (symmetricTensorInclusion Q)ᴴ,
      symmetricTensorInclusion_isometry,Matrix.one_mul]
  have hright : (symmetricTensorInclusion Q)ᴴ*(sourceTensorRepresentation Q g)ᴴ*
      (sourceTensorRepresentation Q g*symmetricTensorInclusion Q) = 1 := by
    rw [Matrix.mul_assoc,← Matrix.mul_assoc (sourceTensorRepresentation Q g)ᴴ,hu,
      Matrix.one_mul,symmetricTensorInclusion_isometry]
  rw [hleft,hright] at he
  exact Matrix.mem_unitaryGroup_iff'.mpr he

 theorem sourceSpinRepresentation_continuous (Q : ℕ) (p q : Fin (Q+1)) :
    Continuous (fun g => sourceSpinRepresentation Q g p q) := by
  change Continuous (fun g : SourceSU2 =>
    ((symmetricTensorInclusion Q)ᴴ*sourceTensorRepresentation Q g*symmetricTensorInclusion Q) p q)
  simp only [Matrix.mul_apply]
  have h := sourceTensorRepresentation_continuous Q
  fun_prop

 theorem source_spin_haar_average_commutes (Q : ℕ) (M : Matrix (Fin (Q+1)) (Fin (Q+1)) ℂ) (g : SourceSU2) :
    sourceSpinRepresentation Q g * matrixIntegral sourceHaar (conjugateOrbit (sourceSpinRepresentation Q) M) =
      matrixIntegral sourceHaar (conjugateOrbit (sourceSpinRepresentation Q) M) * sourceSpinRepresentation Q g := by
  exact compact_haar_average_commutes sourceHaar (sourceSpinRepresentation Q)
    (sourceSpinRepresentation_continuous Q) M g

end Laughlin.Rotation

end OAI
