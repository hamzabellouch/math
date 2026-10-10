import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.DimensionDrop.DimensionDropFibres

namespace OAI

noncomputable section


section
open scoped CStarAlgebra ComplexOrder

namespace ConcreteMatrixUnits.System
variable {I B : Type*} [Fintype I] [DecidableEq I] [CStarAlgebra B]
lemma hom_unit (e : System I B) (i j : I) : e.hom (ConcreteMatrixUnits.unit i j)=e.entry i j := by
  change (∑ k : I,∑ l : I,(ConcreteMatrixUnits.unit i j k l) • e.entry k l)=_
  simp [ConcreteMatrixUnits.unit,CStarMatrix.ofMatrix_apply,Matrix.single_apply,ite_and]
end ConcreteMatrixUnits.System
namespace DimensionDropRelations.Witness
open CompletelyPositiveOperations CurrentMain ConcreteMatrixUnits

variable {I : Type*} [Fintype I] [DecidableEq I]
variable {B : Type*} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
variable {p : I} (w : Witness (B := B) p)
variable {t : ℝ} (hc : w.parameter=t • (1:B))
include hc

lemma phi_fibre_split (ht0 : 0<t) (ht : t<1) (i j : I) :
    w.φ (matrixUnit i j)=t • w.fibreInner t i j+
      (∑ k : I,(w.fibreRow hc ht).coeff (w.fibreInner t k k) (some i) (some j)) := by
  have hh : (∑ k : I,(w.fibreRow hc ht).coeff (w.fibreInner t k k) (some i) (some j))=
      (1-t)⁻¹ • (w.φ (matrixUnit i j)*w.rangeMass) := by
    change (∑ k : I,(w.fibreRow hc ht).entry (some i)*w.fibreInner t k k*star ((w.fibreRow hc ht).entry (some j)))=_
    rw [←Finset.sum_mul,←Finset.mul_sum,w.fibreInner_sum hc ht0,(w.fibreRow hc ht).right_support]
    change w.fibreColumn t i*star (w.fibreColumn t j)=_
    have he : (Real.sqrt (1-t))⁻¹*(Real.sqrt (1-t))⁻¹=(1-t)⁻¹ := by
      rw [←mul_inv,←sq,Real.sq_sqrt (le_of_lt (sub_pos.mpr ht))]
    rw [fibreColumn,fibreColumn,star_smul,star_trivial,smul_mul_assoc,mul_smul_comm,smul_smul,he,w.matrix_mass]
  rw [hh,fibreInner,smul_smul,mul_inv_cancel₀ (ne_of_gt ht0),one_smul,fibreAnchor,mul_smul_comm,
    ←smul_add,←mul_add]
  have he : (1-w.φ 1)+w.rangeMass=(1-t) • (1:B) := by
    have h := hc
    change w.φ 1-w.rangeMass=t • (1:B) at h
    calc
      (1-w.φ 1)+w.rangeMass=1-(w.φ 1-w.rangeMass) := by noncomm_ring
      _=(1-t) • (1:B) := by rw [h,sub_smul,one_smul]
  rw [he,mul_smul_comm,mul_one,smul_smul,inv_mul_cancel₀ (ne_of_gt (sub_pos.mpr ht)),one_smul]

lemma s_fibre_split (ht0 : 0<t) (ht : t<1) :
    w.s=Real.sqrt (1-t) •
      (∑ k : I,(w.fibreRow hc ht).coeff (w.fibreInner t k k) (some p) none) := by
  change w.s=Real.sqrt (1-t) •
    (∑ k : I,(w.fibreRow hc ht).entry (some p)*w.fibreInner t k k*star ((w.fibreRow hc ht).entry none))
  rw [←Finset.sum_mul,←Finset.mul_sum,w.fibreInner_sum hc ht0,(w.fibreRow hc ht).right_support]
  change w.s=Real.sqrt (1-t) • ((w.fibreRow hc ht).entry (some p)*star (w.fibreAnchor t))
  rw [w.fibreAnchor_star,(w.fibreRow hc ht).right_support]
  change w.s=Real.sqrt (1-t) • w.fibreColumn t p
  rw [fibreColumn,smul_smul,mul_inv_cancel₀ (ne_of_gt (Real.sqrt_pos.mpr (sub_pos.mpr ht))),one_smul,column,w.support]

end DimensionDropRelations.Witness

end

namespace DimensionDropRelations.Witness

open CompletelyPositiveOperations CurrentMain ConcreteMatrixUnits
open scoped ComplexOrder CStarAlgebra

variable {I : Type*} [Fintype I] [DecidableEq I]
variable {B : Type*} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
variable {p : I} (w : Witness (B := B) p)

lemma h_eq_one_of_parameter_one (hc : w.parameter=1) : w.φ 1=1 := by
  apply le_antisymm w.h_le_one
  rw [←hc]
  exact sub_le_self _ w.mass_nonneg

lemma s_eq_zero_of_parameter_one (hc : w.parameter=1) : w.s=0 := by
  apply (CStarRing.star_mul_self_eq_zero_iff _).mp
  rw [w.small,w.h_eq_one_of_parameter_one hc,sub_self]

 def upperEndpointHom (hc : w.parameter=1) : CStarMatrix I I ℂ →⋆ₐ[ℂ] B where
  toFun := w.φ
  map_zero' := map_zero w.φ
  map_one' := w.h_eq_one_of_parameter_one hc
  map_add' := map_add w.φ
  map_mul' M N := by rw [w.orderZero,w.h_eq_one_of_parameter_one hc,mul_one]
  commutes' z := by rw [Algebra.algebraMap_eq_smul_one,map_smul,w.h_eq_one_of_parameter_one hc,Algebra.algebraMap_eq_smul_one]
  map_star' M := cp_map_star w.φ M

lemma zero_fibre_phi_matrix (hc : w.parameter=0) (i j : I) :
    w.φ (matrixUnit i j)=w.column i*star (w.column j) := by
  have hkh : w.rangeMass=w.φ 1 := sub_eq_zero.mp hc |>.symm
  have hEsq : (1-w.φ 1)*(1-w.φ 1)=1-w.φ 1 := by
    simpa only [zero_smul,sub_zero,one_smul] using w.fibre_E_sq (t := 0) (by simpa using hc)
  have hhsq : w.φ 1*w.φ 1=w.φ 1 := by
    calc
      w.φ 1*w.φ 1=(1-w.φ 1)*(1-w.φ 1)-1+w.φ 1+w.φ 1 := by noncomm_ring
      _=w.φ 1 := by rw [hEsq]; noncomm_ring
  have hφM (M : CStarMatrix I I ℂ) : w.φ M*w.φ 1=w.φ M := by
    have hz : ‖w.φ M*(1-w.φ 1)‖=0 := by
      have he : star (w.φ M*(1-w.φ 1))*(w.φ M*(1-w.φ 1))=0 := by
        simp only [star_mul,star_sub,star_one,w.h_nonneg.star_eq,←cp_map_star]
        rw [mul_assoc,←mul_assoc (w.φ (star M)) (w.φ M),w.orderZero,
          mul_assoc (w.φ (star M*M)),mul_sub,mul_one,hhsq,sub_self,mul_zero,mul_zero]
      exact norm_eq_zero.mpr ((CStarRing.star_mul_self_eq_zero_iff _).mp he)
    have he := norm_eq_zero.mp hz
    rw [mul_sub,mul_one,sub_eq_zero] at he
    exact he.symm
  rw [←w.matrix_mass,hkh,hφM]

 def lowerEndpointHom (hc : w.parameter=0) : CStarMatrix (Option I) (Option I) ℂ →⋆ₐ[ℂ] B where
  toFun := (w.fibreRow (t := 0) (by simpa using hc) (by norm_num)).matrixHom
  map_zero' := map_zero _
  map_one' := by rw [ProjectionRow.matrixHom_one,w.fibreRow_range]
  map_add' := map_add _
  map_mul' := map_mul _
  commutes' z := by
    rw [Algebra.algebraMap_eq_smul_one,map_smul,ProjectionRow.matrixHom_one,w.fibreRow_range,
      Algebra.algebraMap_eq_smul_one]
  map_star' := map_star _

end DimensionDropRelations.Witness


namespace DimensionDropModel
open ConcreteMatrixUnits CompletelyPositiveOperations
open scoped Kronecker ComplexOrder CStarAlgebra

variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
 def amplify : CStarMatrix I I ℂ →⋆ₐ[ℂ] CStarMatrix (I×J) (I×J) ℂ where
  toFun a := CStarMatrix.ofMatrix (CStarMatrix.ofMatrix.symm a ⊗ₖ (1 : Matrix J J ℂ))
  map_zero' := Matrix.zero_kronecker _
  map_one' := Matrix.one_kronecker_one
  map_add' a b := Matrix.add_kronecker _ _ _
  map_mul' a b := by
    change (CStarMatrix.ofMatrix.symm a * CStarMatrix.ofMatrix.symm b) ⊗ₖ (1 : Matrix J J ℂ)=
      (CStarMatrix.ofMatrix.symm a ⊗ₖ (1 : Matrix J J ℂ))*(CStarMatrix.ofMatrix.symm b ⊗ₖ (1 : Matrix J J ℂ))
    simpa only [Matrix.one_mul] using Matrix.mul_kronecker_mul
      (CStarMatrix.ofMatrix.symm a) (CStarMatrix.ofMatrix.symm b) (1 : Matrix J J ℂ) 1
  commutes' z := by
    ext ⟨i,j⟩ ⟨k,l⟩
    by_cases hi : i=k <;> by_cases hj : j=l <;>
      simp [CStarMatrix.algebraMap_apply,Matrix.kroneckerMap_apply,hi,hj]
  map_star' a := by
    change (CStarMatrix.ofMatrix.symm a).conjTranspose ⊗ₖ (1 : Matrix J J ℂ)=
      ((CStarMatrix.ofMatrix.symm a) ⊗ₖ (1 : Matrix J J ℂ)).conjTranspose
    simp [Matrix.conjTranspose_kronecker]
lemma amplify_apply (a : CStarMatrix I I ℂ) (i k : I) (j l : J) :
    amplify a (i,j) (k,l)=a i k*(if j=l then 1 else 0) := rfl
lemma amplify_injective [Nonempty J] : Function.Injective (amplify (I := I) (J := J)) := by
  intro a b hab
  let j : J := Classical.choice inferInstance
  ext i k
  have h := congrArg (fun M : CStarMatrix (I×J) (I×J) ℂ => M (i,j) (k,j)) hab
  simpa [amplify_apply] using h
lemma amplify_norm [Nonempty J] (a : CStarMatrix I I ℂ) : ‖amplify (J := J) a‖=‖a‖ :=
  (NonUnitalStarAlgHom.isometry (amplify (I := I) (J := J)) amplify_injective).norm_map_of_map_zero (map_zero _) a

 def flipInner : Option I×I ≃ Option I×I where
  toFun x := match x with | (none,i) => (none,i) | (some i,j) => (some j,i)
  invFun x := match x with | (none,i) => (none,i) | (some i,j) => (some j,i)
  left_inv x := by rcases x with ⟨_|i,j⟩ <;> rfl
  right_inv x := by rcases x with ⟨_|i,j⟩ <;> rfl
 def upperEmbed : CStarMatrix I I ℂ →⋆ₐ[ℂ] CStarMatrix (Option I×I) (Option I×I) ℂ :=
  ((CStarMatrix.reindexₐ ℂ ℂ (flipInner (I := I))).toStarAlgHom).comp
    (((CStarMatrix.reindexₐ ℂ ℂ (Equiv.prodComm I (Option I))).toStarAlgHom).comp amplify)
lemma upperEmbed_apply (a : CStarMatrix I I ℂ) (x y : Option I×I) :
    upperEmbed a x y=a (flipInner.symm x).2 (flipInner.symm y).2*
      (if (flipInner.symm x).1=(flipInner.symm y).1 then 1 else 0) := rfl
lemma upperEmbed_norm (a : CStarMatrix I I ℂ) : ‖upperEmbed a‖=‖a‖ := by
  apply (NonUnitalStarAlgHom.isometry (upperEmbed (I := I)) ?_).norm_map_of_map_zero (map_zero _) a
  intro a b hab
  ext i j
  have h := congrArg (fun M : CStarMatrix (Option I×I) (Option I×I) ℂ => M (none,i) (none,j)) hab
  simpa [upperEmbed_apply,flipInner] using h

abbrev Mat (I : Type*) := CStarMatrix (Option I×I) (Option I×I) ℂ
 def phi (t : ℝ) (i j : I) : Mat I :=
  t • unit (none,i) (none,j)+∑ k : I,unit (some i,k) (some j,k)
 def s (p : I) (t : ℝ) : Mat I :=
  Real.sqrt (1-t) • ∑ k : I,unit (some p,k) (none,k)
lemma amplify_unit (i j : I) : amplify (J := J) (unit i j)=∑ k : J,unit (i,k) (j,k) := by
  ext ⟨a,b⟩ ⟨c,d⟩
  simp [amplify_apply,matrix_sum_apply,unit,CStarMatrix.ofMatrix_apply,Matrix.single_apply,ite_and]
  split_ifs <;> simp_all
lemma phi_zero (i j : I) : phi 0 i j=amplify (J := I) (unit (some i) (some j)) := by
  simp only [phi,zero_smul,zero_add,amplify_unit]
lemma s_zero (p : I) : s p 0=amplify (J := I) (unit (some p) none) := by
  simp only [s,sub_zero,Real.sqrt_one,one_smul,amplify_unit]
lemma phi_one (i j : I) : phi 1 i j=upperEmbed (unit i j) := by
  ext ⟨a,b⟩ ⟨c,d⟩
  rw [upperEmbed_apply]
  cases a <;> cases c <;>
    simp [phi,flipInner,matrix_sum_apply,unit,CStarMatrix.ofMatrix_apply,Matrix.single_apply,ite_and]
  split_ifs <;> simp_all

lemma s_one (p : I) : s p 1=0 := by simp [s]

end DimensionDropModel

namespace DimensionDropRelations.Witness
open ConcreteMatrixUnits DimensionDropModel CompletelyPositiveOperations CurrentMain
open scoped ComplexOrder CStarAlgebra

variable {I : Type*} [Fintype I] [DecidableEq I]
variable {B : Type*} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
variable {p : I} (w : Witness (B := B) p)
variable {t : ℝ} (hc : w.parameter=t • (1:B))
include hc
lemma interiorHom_phi (ht0 : 0<t) (ht1 : t<1) (i j : I) :
    w.interiorHom hc ht0 ht1 (phi t i j)=w.φ (matrixUnit i j) := by
  have hsm (r : ℝ) (X : Mat I) : (w.interiorHom hc ht0 ht1) (r • X)=r • (w.interiorHom hc ht0 ht1) X :=
    (w.interiorHom hc ht0 ht1).toAlgHom.map_smul_of_tower r X
  rw [phi,map_add,hsm,map_sum]
  simp only [interiorHom,ConcreteMatrixUnits.System.hom_unit,interiorUnits]
  have hleft : (w.fibreRow hc ht1).coeff (w.fibreInner t i j) none none=w.fibreInner t i j := by
    change w.fibreAnchor t*w.fibreInner t i j*star (w.fibreAnchor t)=_
    rw [w.fibreAnchor_star,w.fibreInner_left hc ht1]
    rw [fibreInner,smul_mul_assoc,mul_assoc,
      (w.fibreAnchor_projection hc ht1).isIdempotentElem.eq]
  rw [hleft]
  exact (w.phi_fibre_split hc ht0 ht1 i j).symm
lemma interiorHom_s (ht0 : 0<t) (ht1 : t<1) :
    w.interiorHom hc ht0 ht1 (DimensionDropModel.s p t)=w.s := by
  have hsm (r : ℝ) (X : Mat I) : (w.interiorHom hc ht0 ht1) (r • X)=r • (w.interiorHom hc ht0 ht1) X :=
    (w.interiorHom hc ht0 ht1).toAlgHom.map_smul_of_tower r X
  rw [DimensionDropModel.s,hsm,map_sum]
  simp only [interiorHom,ConcreteMatrixUnits.System.hom_unit,interiorUnits]
  exact (w.s_fibre_split hc ht0 ht1).symm

end DimensionDropRelations.Witness

end

end OAI
