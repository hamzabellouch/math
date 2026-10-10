import Mathlib
import OAI.Analysis.BoundedHochschild.CocycleNormalParts
import OAI.Analysis.BoundedHochschild.FactorFinitePaths
import OAI.Analysis.BoundedHochschild.FreeWords
import OAI.Analysis.BoundedHochschild.MatrixDisplacement
import OAI.Analysis.BoundedHochschild.UnitaryLifts
import OAI.Analysis.BoundedHochschild.FactorPrimitive
import OAI.Analysis.BoundedHochschild.TypeIICorners
import OAI.Analysis.BoundedHochschild.CenterPowers

namespace OAI

/-! Right module identities from subalgebra unitary invariance. -/

noncomputable section

open Filter Topology
namespace BoundedHochschild
variable {M : Type*} [CStarAlgebra M]

def unitaryInclusion (A : StarSubalgebra ℂ M) : unitary A →* unitary M where
  toFun u := ⟨(u:A),Unitary.map_mem A.subtype u.property⟩
  map_one' := Subtype.ext rfl
  map_mul' _ _ := Subtype.ext rfl

@[simp] lemma coe_unitaryInclusion (A : StarSubalgebra ℂ M) (u : unitary A) :
    (unitaryInclusion A u : M)=(u:A) := rfl

lemma continuous_unitaryInclusion (A : StarSubalgebra ℂ M) :
    Continuous (unitaryInclusion A) := by
  change Continuous (fun u : unitary A =>
    (⟨((u:A):M),Unitary.map_mem A.subtype u.property⟩ : unitary M))
  exact (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _

lemma right_module_subalgebra (A : StarSubalgebra ℂ M) [IsClosed (A : Set M)]
    {n : ℕ} (F : Cochain M (n+1))
    (hfix : ∀ u : unitary A, translateLast F (unitaryInclusion A u)=F) :
    ∀ (a : Fin n → M) (x : M) (b : A),
      F (Fin.snoc a (x*(b:M)))=F (Fin.snoc a x)*(b:M) := by
  intro a x b
  let L := F.curryRight a
  have hu (u : unitary A) : L (x*(u:A))=L x*(u:A) := by
    have h := congrArg (fun H : Cochain M (n+1) => H (Fin.snoc a x)) (hfix u)
    simp only [translateLast_apply,Fin.snoc_last,Fin.snoc_castSucc,coe_unitaryInclusion] at h
    have hh := congrArg (fun y : M => y*(u:A)) h
    have hun : star ((u:A):M)*((u:A):M)=1 :=
      Unitary.star_mul_self_of_mem (unitaryInclusion A u).property
    simpa only [L,ContinuousMultilinearMap.curryRight_apply,mul_assoc,hun,mul_one] using hh
  have hb : b ∈ Submodule.span ℂ (unitary A : Set A) := by
    rw [CStarAlgebra.span_unitary]
    trivial
  change L (x*(b:M))=L x*(b:M)
  induction hb using Submodule.span_induction with
  | mem y hy => exact hu ⟨y,hy⟩
  | zero => simp
  | add y z hy hz ihy ihz =>
      change L (x*((y:M)+(z:M)))=L x*((y:M)+(z:M))
      rw [mul_add,map_add,ihy,ihz,mul_add]
  | smul c y hy ih =>
      change L (x*(c • (y:M)))=L x*(c • (y:M))
      rw [mul_smul_comm,map_smul,ih,mul_smul_comm]

end BoundedHochschild

end

end OAI
