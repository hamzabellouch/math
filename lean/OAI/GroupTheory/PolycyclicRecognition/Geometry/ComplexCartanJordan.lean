import OAI.GroupTheory.PolycyclicRecognition.Geometry.ComplexRotationDerivation
import Mathlib.LinearAlgebra.JordanChevalley
import Mathlib.LinearAlgebra.Eigenspace.Semisimple

namespace OAI

/-! # The semisimple Cartan operator preserves the original triangular flag -/

noncomputable section
namespace PolycyclicRecognition.ComplexCartan
open LieAlgebra LieModule Module

variable {L : Type*} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L]
  (H : LieSubalgebra ℂ L) [H.IsCartanSubalgebra]

/-- The full semisimple part, before its imaginary part is removed. -/
def semisimpleOperator (h : H) : Module.End ℂ L := weightOperator H (fun χ => χ h)

theorem semisimpleOperator_apply (h : H) (χ : Weight ℂ H L) {x : L}
    (hx : x ∈ genWeightSpace L χ) : semisimpleOperator H h x = χ h • x :=
  weightOperator_apply H _ χ hx

/-- The root-space scalar operator is precisely the Jordan semisimple part. -/
theorem semisimpleOperator_jordan (h : H) :
    semisimpleOperator H h ∈ Algebra.adjoin ℂ {ad ℂ L (h : L)} ∧
      IsNilpotent (ad ℂ L (h : L) - semisimpleOperator H h) := by
  obtain ⟨N,hN,S,hS,hnil,hss,hsum⟩ := (ad ℂ L (h : L)).exists_isNilpotent_isSemisimple
  have hc : Commute (ad ℂ L (h : L)) S :=
    Algebra.commute_of_mem_adjoin_singleton_of_commute hS (Commute.refl _)
  have hd : IsNilpotent (ad ℂ L (h : L) - S) := by
    simpa only [hsum,add_sub_cancel_right] using hnil
  have he : S = semisimpleOperator H h := by
    ext x
    apply root_induction H (x := x)
    · intro χ v hv
      rw [semisimpleOperator_apply H h χ hv]
      have hv' : v ∈ (ad ℂ L (h : L)).maxGenEigenspace (χ h) :=
        genWeightSpace_le_genWeightSpaceOf L h χ hv
      exact End.apply_eq_of_mem_of_comm_of_isFinitelySemisimple_of_isNil
        hv' hc hss.isFinitelySemisimple hd
    · simp
    · intro u v hu hv
      simp only [map_add,hu,hv]
  exact ⟨he ▸ hS,he ▸ hd⟩

/-- The semisimple part preserves every upper triangular flag for the
original adjoint operator. -/
theorem semisimpleOperator_upper {n : ℕ} (b : Basis (Fin n) ℂ L) (h : H)
    (hh : (LinearMap.toMatrix b b (ad ℂ L (h : L))).IsUpperTriangular) :
    (LinearMap.toMatrix b b (semisimpleOperator H h)).IsUpperTriangular := by
  let F := LinearMap.toMatrixAlgEquiv b
  let A := Matrix.blockTriangularSubalgebra ℂ ℂ (id : Fin n → Fin n)
  have hle : Algebra.adjoin ℂ {ad ℂ L (h : L)} ≤ A.comap F.toAlgHom := by
    apply Algebra.adjoin_le
    intro f hf
    obtain rfl := Set.mem_singleton_iff.mp hf
    exact hh
  exact hle (semisimpleOperator_jordan H h).1

end PolycyclicRecognition.ComplexCartan

end

end OAI
