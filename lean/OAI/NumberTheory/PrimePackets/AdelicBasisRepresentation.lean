import Mathlib
import OAI.NumberTheory.PrimePackets.AdelicGeneralPacketDefinitions

namespace OAI

noncomputable section
open scoped TensorProduct Topology MatrixGroups
open Matrix Module Set MeasureTheory
namespace PrimeDegreePackets.Adelic

lemma rowRegular_changeBasis {R S ι : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Fintype ι] [DecidableEq ι] (b m : Basis ι R S) (x : S) :
    rowRegular m x * (b.toMatrix m)ᵀ = (b.toMatrix m)ᵀ * rowRegular b x := by
  have h₁ := LinearMap.toMatrix_comp m m b (LinearMap.id : S →ₗ[R] S) (Algebra.lmul R S x)
  have h₂ := LinearMap.toMatrix_comp m b b (Algebra.lmul R S x) (LinearMap.id : S →ₗ[R] S)
  simp only [LinearMap.id_comp,LinearMap.comp_id,LinearMap.toMatrix_id_eq_basis_toMatrix,
    ← Algebra.leftMulMatrix_apply] at h₁ h₂
  have he := h₁.symm.trans h₂
  change (Algebra.leftMulMatrix m x)ᵀ * (b.toMatrix m)ᵀ =
    (b.toMatrix m)ᵀ * (Algebra.leftMulMatrix b x)ᵀ
  simpa only [Matrix.transpose_mul] using congrArg Matrix.transpose he

lemma baseChange_toMatrix {n : ℕ} {K A : Type*} [Field K] [NumberField K]
    [CommRing A] [Algebra ℚ A] (b m : Basis (Fin n) ℚ K) :
    (b.baseChange A).toMatrix (m.baseChange A) = (b.toMatrix m).map (algebraMap ℚ A) := by
  ext i j
  simp [Basis.toMatrix_apply,Basis.baseChange_apply,Basis.baseChange_repr_tmul,Algebra.smul_def]

lemma rowRegularUnits_basisChange {n : ℕ} {K A : Type*} [Field K] [NumberField K]
    [CommRing A] [Algebra ℚ A] (b m : Basis (Fin n) ℚ K) (t : (A ⊗[ℚ] K)ˣ) :
    rowRegularUnits (m.baseChange A) t * GeneralLinearGroup.map (algebraMap ℚ A) (rowBasisChange m b) =
      GeneralLinearGroup.map (algebraMap ℚ A) (rowBasisChange m b) * rowRegularUnits (b.baseChange A) t := by
  apply Units.ext
  have he := rowRegular_changeBasis (b.baseChange A) (m.baseChange A) t.val
  rw [baseChange_toMatrix] at he
  exact he

lemma adelicRegular_basisChange {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (b m : Basis (Fin n) ℚ K) (t : (TensorAdeles K)ˣ) :
    adelicRegular m t * rationalProjectiveEmbedding n (ProjGenLinGroup.mk (rowBasisChange m b)) =
      rationalProjectiveEmbedding n (ProjGenLinGroup.mk (rowBasisChange m b)) * adelicRegular b t := by
  have he := rowRegularUnits_basisChange (A := RationalAdeles) b m t
  let r : GL (Fin n) RationalAdeles →* AdelicPGL n :=
    (ProjGenLinGroup.mk.comp (GeneralLinearGroup.map (RingHom.fst ℝ RationalFiniteAdeles))).prod
      (ProjGenLinGroup.mk.comp (GeneralLinearGroup.map (RingHom.snd ℝ RationalFiniteAdeles)))
  have hr : r (GeneralLinearGroup.map (algebraMap ℚ RationalAdeles) (rowBasisChange m b)) =
      rationalProjectiveEmbedding n (ProjGenLinGroup.mk (rowBasisChange m b)) := by
    apply Prod.ext <;> apply congrArg ProjGenLinGroup.mk <;> apply Units.ext <;> rfl
  have H := congrArg r he
  simp only [map_mul,hr] at H
  exact H

end PrimeDegreePackets.Adelic

end

end OAI
