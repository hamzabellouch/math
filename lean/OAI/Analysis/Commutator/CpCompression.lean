import Mathlib
import OAI.Analysis.Commutator.CyclicMatrix
import OAI.Analysis.Commutator.CyclicSpatialImplementation
import OAI.Analysis.Commutator.FaithfulPositive

namespace OAI

noncomputable section

section

noncomputable section

open scoped BigOperators InnerProductSpace ComplexOrder CStarAlgebra

namespace Kadison.CpCompression

variable {A H K : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

def compression (ρ : A →⋆ₐ[ℂ] (K →L[ℂ] K)) (V : H →L[ℂ] K) : A →CP (H →L[ℂ] H) where
  toLinearMap :=
    { toFun a := V.adjoint.comp ((ρ a).comp V)
      map_add' a b := by simp [ContinuousLinearMap.add_comp,ContinuousLinearMap.comp_add]
      map_smul' c a := by simp [ContinuousLinearMap.smul_comp] }
  map_cstarMatrix_nonneg' n M hM := by
    classical
    let : DecidableEq (Fin n) := Classical.decEq (Fin n)
    let Vn : PiLp 2 (fun _ : Fin n => H) →L[ℂ] PiLp 2 (fun _ : Fin n => K) :=
      CyclicColumns.matrixAction (fun i j => if i=j then V else 0)
    have hVn (x : PiLp 2 (fun _ : Fin n => H)) (i : Fin n) : Vn x i=V (x i) := by
      rw [CyclicColumns.matrixAction_apply]
      calc
        _ = ∑ j,if i=j then V (x j) else 0 := by
          apply Finset.sum_congr rfl
          intro j _
          by_cases h : i=j <;> simp [h]
        _ = V (x i) := by simp
    let R := CyclicColumns.matrixRepresentation (ι:=Fin n) (StarAlgHom.id ℂ (H →L[ℂ] H))
    have hR : Function.Injective R :=
      CyclicSpatial.matrixRepresentation_injective (ι:=Fin n)
        (StarAlgHom.id ℂ (H →L[ℂ] H)) Function.injective_id
    have hiff := @faithfulStar_nonneg_iff
      (CStarMatrix (Fin n) (Fin n) (H →L[ℂ] H))
      (PiLp 2 (fun _ : Fin n => H) →L[ℂ] PiLp 2 (fun _ : Fin n => H))
      inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance R hR
    apply (hiff _).mp
    have hp : 0 ≤ CyclicColumns.matrixRepresentation (ι:=Fin n) ρ M :=
      map_nonneg (CyclicColumns.matrixRepresentation (ι:=Fin n) ρ) hM
    apply ContinuousLinearMap.nonneg_iff_isPositive.mpr
    apply (ContinuousLinearMap.isPositive_iff_complex _).mpr
    intro x
    suffices hx : 0 ≤ ⟪R (M.map _ ) x,x⟫_ℂ by
      exact ⟨Complex.ext (by simp) (by simpa using hx.2),hx.1⟩
    have hi := ContinuousLinearMap.nonneg_iff_isPositive.mp hp
    convert hi.inner_nonneg_left (Vn x) using 1
    dsimp only [R]
    simp [CyclicColumns.matrixRepresentation,CyclicColumns.matrixAction_apply,
      PiLp.inner_apply,hVn,sum_inner,ContinuousLinearMap.adjoint_inner_left]

@[simp] lemma compression_apply (ρ : A →⋆ₐ[ℂ] (K →L[ℂ] K)) (V : H →L[ℂ] K) (a : A) :
    compression ρ V a=V.adjoint.comp ((ρ a).comp V) := rfl

end Kadison.CpCompression

end

end
end

end OAI
