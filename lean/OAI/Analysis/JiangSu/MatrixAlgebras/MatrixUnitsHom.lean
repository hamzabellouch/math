import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.Model

namespace OAI

noncomputable section
namespace ConcreteMatrixUnits
open scoped ComplexOrder

variable {ι D : Type*} [Fintype ι] [DecidableEq ι] [CStarAlgebra D]

namespace System
variable (e : System ι D)

def linearMap : CStarMatrix ι ι ℂ →ₗ[ℂ] D where
  toFun a := ∑ i,∑ j,(a i j) • e.entry i j
  map_add' a b := by simp only [CStarMatrix.add_apply,add_smul,Finset.sum_add_distrib]
  map_smul' z a := by
    simp only [CStarMatrix.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum,
      RingHom.id_apply]

lemma linearMap_one : e.linearMap 1=1 := by
  change (∑ i,∑ j,((1:CStarMatrix ι ι ℂ) i j) • e.entry i j)=1
  simpa only [CStarMatrix.one_apply, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true] using e.sum_diag

lemma linearMap_mul (a b : CStarMatrix ι ι ℂ) : e.linearMap (a*b)=e.linearMap a*e.linearMap b := by
  classical
  change (∑ i,∑ l,(∑ j,a i j*b j l) • e.entry i l)=
    (∑ i,∑ j,(a i j) • e.entry i j)*(∑ k,∑ l,(b k l) • e.entry k l)
  have hmul (i j k l : ι) :
      ((a i j) • e.entry i j)*((b k l) • e.entry k l)=
        if j=k then (a i j*b k l) • e.entry i l else 0 := by
    rw [smul_mul_assoc,mul_smul_comm,smul_smul,e.mul_entry]
    simp only [smul_ite,smul_zero]
  calc
    _ = ∑ i,∑ j,∑ l,(a i j*b j l) • e.entry i l := by
      simp only [Finset.sum_smul]
      exact Finset.sum_congr rfl (fun i _ => Finset.sum_comm)
    _ = ∑ i,∑ j,∑ k,∑ l,((a i j) • e.entry i j)*((b k l) • e.entry k l) := by
      simp only [hmul]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.sum_comm]
      simp
    _ = _ := by
      symm
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      rw [Finset.mul_sum]

lemma linearMap_star (a : CStarMatrix ι ι ℂ) : e.linearMap (star a)=star (e.linearMap a) := by
  change (∑ i,∑ j,star (a j i) • e.entry i j)=star (∑ i,∑ j,(a i j) • e.entry i j)
  simp only [star_sum,star_smul,e.star_entry]
  rw [Finset.sum_comm]

def hom : CStarMatrix ι ι ℂ →⋆ₐ[ℂ] D :=
  { e.linearMap with
    map_zero' := e.linearMap.map_zero
    map_one' := e.linearMap_one
    map_mul' := e.linearMap_mul
    commutes' := fun z => by
      change e.linearMap (algebraMap ℂ (CStarMatrix ι ι ℂ) z)=algebraMap ℂ D z
      rw [Algebra.algebraMap_eq_smul_one,map_smul,e.linearMap_one,Algebra.algebraMap_eq_smul_one]
    map_star' := e.linearMap_star }

lemma hom_commute {a : D} (h : ∀ i j,Commute (e.entry i j) a) (M : CStarMatrix ι ι ℂ) :
    Commute (e.hom M) a := by
  change Commute (∑ i,∑ j,(M i j) • e.entry i j) a
  apply Commute.sum_left
  intro i _
  apply Commute.sum_left
  intro j _
  exact (h i j).smul_left _

end System
end ConcreteMatrixUnits

end

noncomputable section
open scoped CStarAlgebra ComplexOrder

namespace ConcreteMatrixUnits
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def unit (i j : ι) : CStarMatrix ι ι ℂ := CStarMatrix.ofMatrix (Matrix.single i j 1)

lemma unit_mul (i j k l : ι) : unit i j*unit k l=if j=k then unit i l else 0 := by
  ext a b
  by_cases hjk : j=k <;> by_cases hia : i=a <;> by_cases hlb : l=b <;>
    simp [unit,CStarMatrix.mul_apply,Matrix.single_apply,hjk,hia,hlb]

omit [Fintype ι] in
lemma unit_star (i j : ι) : star (unit i j)=unit j i := by
  change CStarMatrix.ofMatrix (Matrix.single i j (1:ℂ)).conjTranspose=_
  simp [unit,Matrix.conjTranspose_single]

lemma unit_sum_diag : (∑ i : ι,unit i i)=1 := by
  ext a b
  change CStarMatrix.ofMatrix (∑ i : ι,Matrix.single i i (1:ℂ)) a b=_
  rw [Matrix.sum_single_one]
  rfl

def standard : System ι (CStarMatrix ι ι ℂ) := ⟨unit,unit_mul,unit_star,unit_sum_diag⟩

lemma unit_norm_le_one (i j : ι) : ‖unit i j‖≤1 := by
  have hp : ‖unit j j‖*‖unit j j‖=‖unit j j‖ := by
    rw [←CStarRing.norm_star_mul_self,unit_star,unit_mul,ite_eq_left rfl]
  have hn : ‖unit j j‖≤1 := by nlinarith [norm_nonneg (unit j j)]
  have hsq : ‖unit i j‖*‖unit i j‖≤1 := by
    rw [←CStarRing.norm_star_mul_self,unit_star,unit_mul,ite_eq_left rfl]
    exact hn
  nlinarith [norm_nonneg (unit i j)]

end ConcreteMatrixUnits

end

noncomputable section
namespace CurrentMain.ProjectionRow
open Pureness
open scoped ComplexOrder

variable {D I J : Type*} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]
variable [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
variable {p q : D} (V : ProjectionRow J p) (U : ProjectionRow I q)

def matrixHom : CStarMatrix J J ℂ →⋆ₙₐ[ℂ] D where
  toFun a := V.matrix p (CStarMatrix.ofMatrixStarAlgEquiv.symm a)
  map_zero' := by simp [matrix,coeff]
  map_add' a b := by simp [matrix,coeff,add_smul,Finset.sum_add_distrib]
  map_mul' a b := by
    rw [map_mul,V.matrix_mul p p V.projection.isIdempotentElem.eq,V.projection.isIdempotentElem.eq]
  map_smul' z a := by simp [matrix,coeff,mul_smul,Finset.smul_sum]
  map_star' a := by
    rw [map_star,V.matrix_star,V.projection.isSelfAdjoint.star_eq]

omit [PartialOrder D] [StarOrderedRing D] in
lemma matrixHom_one : V.matrixHom 1=V.sample p := by
  change V.matrix p (CStarMatrix.ofMatrixStarAlgEquiv.symm 1) = _
  rw [map_one, V.matrix_one]

omit [PartialOrder D] [StarOrderedRing D] in
lemma matrixHom_left (M : CStarMatrix J J ℂ) : V.sample p*V.matrixHom M=V.matrixHom M := by
  change V.sample p*V.matrix p (CStarMatrix.ofMatrixStarAlgEquiv.symm M)=V.matrix p (CStarMatrix.ofMatrixStarAlgEquiv.symm M)
  rw [V.sample_matrix p p V.projection.isIdempotentElem.eq,V.projection.isIdempotentElem.eq]

omit [PartialOrder D] [StarOrderedRing D] in
lemma matrixHom_right (M : CStarMatrix J J ℂ) : V.matrixHom M*V.sample p=V.matrixHom M := by
  change V.matrix p (CStarMatrix.ofMatrixStarAlgEquiv.symm M)*V.sample p=V.matrix p (CStarMatrix.ofMatrixStarAlgEquiv.symm M)
  rw [V.matrix_sample p p V.projection.isIdempotentElem.eq,V.projection.isIdempotentElem.eq]

lemma matrixHom_supported (hq : IsStarProjection q) {e : D} (he : V.sample p=e) (heq : e≤q) (M : CStarMatrix J J ℂ) :
    q*V.matrixHom M=V.matrixHom M ∧ V.matrixHom M*q=V.matrixHom M := by
  have hp : IsStarProjection e := he ▸ V.range_projection
  have hqe := (hp.le_iff_mul_eq_right hq).mp heq
  have heq' := (hp.le_iff_mul_eq_left hq).mp heq
  have hl := V.matrixHom_left M
  have hr := V.matrixHom_right M
  rw [he] at hl hr
  constructor
  · calc
      q*V.matrixHom M=q*(e*V.matrixHom M) := by rw [hl]
      _ = V.matrixHom M := by rw [←mul_assoc,hqe,hl]
  · calc
      V.matrixHom M*q=(V.matrixHom M*e)*q := by rw [hr]
      _ = V.matrixHom M := by rw [mul_assoc,heq',hr]

def amplifiedMatrixHom {e : D} (he : V.sample p=e) (heq : e≤q) :
    CStarMatrix J J ℂ →⋆ₙₐ[ℂ] D where
  toFun M := U.sample (V.matrixHom M)
  map_zero' := by simp [sample,coeff]
  map_add' a b := by simp [sample,coeff,mul_add,add_mul,Finset.sum_add_distrib]
  map_mul' a b := by rw [map_mul,U.sample_mul _ _ (V.matrixHom_supported U.projection he heq b).1]
  map_smul' z a := by simp [sample,coeff,Finset.smul_sum]
  map_star' a := by rw [map_star,U.sample_star]

omit [DecidableEq I] in
lemma amplifiedMatrixHom_one {e : D} (he : V.sample p=e) (heq : e≤q) :
    V.amplifiedMatrixHom U he heq 1=U.sample e := by
  change U.sample (V.matrixHom 1)=U.sample e
  rw [V.matrixHom_one,he]

omit [DecidableEq I] in
lemma amplifiedMatrixHom_commute {e : D} (he : V.sample p=e) (heq : e≤q)
    (M : CStarMatrix J J ℂ) (H : Matrix I I ℂ) :
    Commute (U.matrix q H) (V.amplifiedMatrixHom U he heq M) :=
  U.matrix_sample_commute (V.matrixHom_supported U.projection he heq M).1
    (V.matrixHom_supported U.projection he heq M).2 H

end CurrentMain.ProjectionRow

end

end OAI
