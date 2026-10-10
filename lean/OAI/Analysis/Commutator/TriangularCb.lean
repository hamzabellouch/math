import Mathlib
import OAI.Analysis.Commutator.CyclicSpatialImplementation
import OAI.Analysis.Commutator.RectangularColumn
import OAI.Analysis.Commutator.HilbertPair
import OAI.Analysis.Commutator.AmplificationIsometry

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace BigOperators

namespace Kadison.RectangularColumn

open CyclicColumns HilbertPair HilbertPadding

variable {A K F : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

local instance triangularCbNormedAddCommGroup : NormedAddCommGroup (K →L[ℂ] F) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance triangularCbNormedSpace : NormedSpace ℂ (K →L[ℂ] F) :=
  ContinuousLinearMap.toNormedSpace

def diagonalRepresentation (σ : A →⋆ₐ[ℂ] (K →L[ℂ] K))
    (lam : A →⋆ₐ[ℂ] (F →L[ℂ] F)) : A →⋆ₐ[ℂ] (SumHilbert F K →L[ℂ] SumHilbert F K) where
  toAlgHom := triangularHom σ lam 0 (by intros; simp)
  map_star' a := by
    change triangularMap σ lam 0 (star a)=star (triangularMap σ lam 0 a)
    rw [ContinuousLinearMap.star_eq_adjoint]
    apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
    intro x y
    simp [WithLp.prod_inner_apply,map_star,ContinuousLinearMap.star_eq_adjoint,
      ContinuousLinearMap.adjoint_inner_left]

omit [PartialOrder A] [StarOrderedRing A] in
@[simp] lemma diagonalRepresentation_apply (σ : A →⋆ₐ[ℂ] (K →L[ℂ] K))
    (lam : A →⋆ₐ[ℂ] (F →L[ℂ] F)) (a : A) (x : SumHilbert F K) :
    diagonalRepresentation σ lam a x=WithLp.toLp 2 (lam a x.fst,σ a x.snd) := by
  simp [diagonalRepresentation]

omit [PartialOrder A] [StarOrderedRing A] in
lemma triangular_split (σ : A →⋆ₐ[ℂ] (K →L[ℂ] K))
    (lam : A →⋆ₐ[ℂ] (F →L[ℂ] F)) (D : A →L[ℂ] (K →L[ℂ] F)) (a : A) :
    triangularMap σ lam D a=diagonalRepresentation σ lam a+
      (left F K).toContinuousLinearMap.comp ((D a).comp (right F K).toContinuousLinearMap.adjoint) := by
  ext x
  apply (WithLp.equiv 2 (F × K)).injective
  simp [right_adjoint]

variable {ι : Type*} [Fintype ι]

local instance : DecidableEq ι := Classical.decEq ι

lemma offDiagonal_matrixAction (D : ι → ι → K →L[ℂ] F) :
    matrixAction (fun i j => (left F K).toContinuousLinearMap.comp
      ((D i j).comp (right F K).toContinuousLinearMap.adjoint))=
    (amplifyIsometry ι (left F K)).toContinuousLinearMap.comp
      ((matrixAction D).comp (amplifyIsometry ι (right F K)).toContinuousLinearMap.adjoint) := by
  ext x i
  simp only [matrixAction_apply,ContinuousLinearMap.comp_apply,
    LinearIsometry.coe_toContinuousLinearMap,amplifyIsometry_apply,amplifyIsometry_adjoint]
  rw [map_sum]

lemma offDiagonal_matrix_norm_le (D : ι → ι → K →L[ℂ] F) :
    ‖matrixAction (fun i j => (left F K).toContinuousLinearMap.comp
      ((D i j).comp (right F K).toContinuousLinearMap.adjoint))‖≤‖matrixAction D‖ := by
  rw [offDiagonal_matrixAction]
  have hL := (amplifyIsometry ι (left F K)).norm_toContinuousLinearMap_le
  have hR := (amplifyIsometry ι (right F K)).norm_toContinuousLinearMap_le
  calc
    _ ≤ ‖(amplifyIsometry ι (left F K)).toContinuousLinearMap‖*
        ‖(matrixAction D).comp (amplifyIsometry ι (right F K)).toContinuousLinearMap.adjoint‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1*(‖matrixAction D‖*1) := by
      apply mul_le_mul hL _ (ContinuousLinearMap.opNorm_nonneg _) (by norm_num)
      exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_left (by simpa using hR) (ContinuousLinearMap.opNorm_nonneg _))
    _ = ‖matrixAction D‖ := by ring

lemma triangular_matrix_norm_le (σ : A →⋆ₐ[ℂ] (K →L[ℂ] K))
    (lam : A →⋆ₐ[ℂ] (F →L[ℂ] F)) (D : A →L[ℂ] (K →L[ℂ] F))
    (hD : ∀ a b, D (a*b)=(D a).comp (σ b)+(lam a).comp (D b))
    {c : ℝ} (_hc : 0≤c)
    (hcb : ∀ (X : CStarMatrix ι ι A),‖matrixAction (fun i j => D (X i j))‖≤c*‖X‖)
    (X : CStarMatrix ι ι A) :
    ‖CStarMatrix.mapₗ (triangularHom σ lam D hD).toLinearMap X‖≤(1+c)*‖X‖ := by
  rw [←CyclicSpatial.matrixRepresentation_norm_eq
    (StarAlgHom.id ℂ (SumHilbert F K →L[ℂ] SumHilbert F K)) Function.injective_id]
  have he : matrixRepresentation (StarAlgHom.id ℂ (SumHilbert F K →L[ℂ] SumHilbert F K))
      (CStarMatrix.mapₗ (triangularHom σ lam D hD).toLinearMap X)=
      matrixRepresentation (diagonalRepresentation σ lam) X+
        matrixAction (fun i j => (left F K).toContinuousLinearMap.comp
          ((D (X i j)).comp (right F K).toContinuousLinearMap.adjoint)) := by
    ext x i
    simp only [CyclicSpatial.represented_matrix_apply,matrixAction_apply,_root_.add_apply,PiLp.add_apply]
    change (∑ j,triangularMap σ lam D (X i j) (x j))=_
    simp only [triangular_split,_root_.add_apply,Finset.sum_add_distrib]
  rw [he]
  exact (norm_add_le _ _).trans ((add_le_add
    (matrixRepresentation_norm_le (diagonalRepresentation σ lam) X)
    ((offDiagonal_matrix_norm_le _).trans (hcb X))).trans_eq (by ring))

end Kadison.RectangularColumn

end

end
end

end OAI
