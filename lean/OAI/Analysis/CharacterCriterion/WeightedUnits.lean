import OAI.Analysis.CharacterCriterion.OrderZero

namespace OAI

noncomputable section
open scoped TensorProduct
open scoped InnerProductSpace
open scoped BigOperators
open Set Module
open Topology
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace
open scoped InnerProductSpace
open NormedSpace
open scoped TensorProduct InnerProductSpace
open UniformSpace
variable [KirchbergRordam.GenericRW.Size]
local notation "rankNum" => KirchbergRordam.GenericRW.Size.n


namespace KirchbergRordam.GenericRW.OrderZero.WeightedUnits
open scoped BigOperators
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable (W : WeightedUnits (Fin rankNum) A) {v : A}
variable (hv : star v*v=1-W.h) (h0 : W.x 0 0*v=v)

omit [StarOrderedRing A] in
include h0 in
lemma total_mul_v : W.h*v=v := by
  calc
    W.h*v=W.h*(W.x 0 0*v) := by rw [h0]
    _=(W.x 0 0*W.x 0 0)*v := by rw [W.mul_x]; simp only [ite_true,mul_assoc]
    _=v := by rw [mul_assoc,h0,h0]

omit [StarOrderedRing A] in
include h0 in
lemma defect_mul_v : (1-W.h)*v=0 := by rw [sub_mul,one_mul,W.total_mul_v h0,sub_self]

omit [StarOrderedRing A] in
lemma commute_defect (i j : Fin rankNum) : Commute (W.x i j) (1-W.h) :=
  (Commute.one_right _).sub_right (W.commute_h i j)

include hv in
lemma defect_nonneg : 0≤1-W.h := hv ▸ star_mul_self_nonneg v

lemma defect_selfAdjoint : IsSelfAdjoint (1-W.h) :=
  (IsSelfAdjoint.one A).sub (IsSelfAdjoint.of_nonneg W.nonneg)


def polarVectors (v : A) (i : Fin rankNum) : A := W.x i 0*v*CFC.sqrt (1-W.h)

omit [StarOrderedRing A] in
include hv h0 in
lemma column_inner (i j : Fin rankNum) :
    star (W.x i 0*v)*(W.x j 0*v)=if i=j then 1-W.h else 0 := by
  rw [star_mul,W.star_x]
  calc
    _=star v*(W.x 0 i*W.x j 0)*v := by noncomm_ring
    _=if i=j then 1-W.h else 0 := by
      rw [W.mul_x]
      split_ifs with hij
      · rw [mul_assoc,mul_assoc,h0,W.total_mul_v h0,hv]
      · simp

include hv h0 in
lemma polarVectors_inner (i j : Fin rankNum) :
    star (W.polarVectors v i)*W.polarVectors v j=
      if i=j then star (1-W.h)*(1-W.h) else 0 := by
  have hr : star (CFC.sqrt (1-W.h))=CFC.sqrt (1-W.h) :=
    (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg (1-W.h))).star_eq
  change star ((W.x i 0*v)*CFC.sqrt (1-W.h))*((W.x j 0*v)*CFC.sqrt (1-W.h))=_
  rw [star_mul,hr]
  calc
    _=CFC.sqrt (1-W.h)*(star (W.x i 0*v)*(W.x j 0*v))*CFC.sqrt (1-W.h) := by noncomm_ring
    _=if i=j then star (1-W.h)*(1-W.h) else 0 := by
      rw [W.column_inner hv h0]
      split_ifs
      · rw [W.defect_selfAdjoint.star_eq]
        have hs := CFC.sqrt_mul_sqrt_self (1-W.h) (W.defect_nonneg hv)
        calc
          _=CFC.sqrt (1-W.h)*(CFC.sqrt (1-W.h)*CFC.sqrt (1-W.h))*CFC.sqrt (1-W.h) := by rw [hs]
          _=(CFC.sqrt (1-W.h)*CFC.sqrt (1-W.h))*(CFC.sqrt (1-W.h)*CFC.sqrt (1-W.h)) := by noncomm_ring
          _=_ := by rw [hs]
      · simp

include h0 in
lemma polarVectors_annihilate (i : Fin rankNum) : (1-W.h)*W.polarVectors v i=0 := by
  unfold polarVectors
  calc
    _=(W.x i 0*(1-W.h)*v)*CFC.sqrt (1-W.h) := by rw [← mul_assoc,← mul_assoc,← (W.commute_defect i 0).eq]
    _=0 := by rw [mul_assoc _ (1-W.h),W.defect_mul_v h0,mul_zero,zero_mul]

include h0 in
lemma units_polarVectors (j k i : Fin rankNum) :
    W.x j k*W.polarVectors v i=if k=i then W.polarVectors v j else 0 := by
  unfold polarVectors
  calc
    _=(W.x j k*W.x i 0)*v*CFC.sqrt (1-W.h) := by noncomm_ring
    _=_ := by
      rw [W.mul_x]
      split_ifs
      · rw [← (W.commute_h j 0).eq,mul_assoc _ W.h,W.total_mul_v h0]
      · simp


def defectCopies : HereditaryTransport.corner (1-W.h) W.defect_selfAdjoint →⋆ₙₐ[ℂ] A :=
  HereditaryTransport.copies W.defect_selfAdjoint (W.polarVectors v) (W.polarVectors_inner hv h0)

lemma defectCopies_orthogonal (x y : HereditaryTransport.corner (1-W.h) W.defect_selfAdjoint) :
    (x:A)*W.defectCopies hv h0 y=0 :=
  HereditaryTransport.copies_orthogonal W.defect_selfAdjoint (W.polarVectors v)
    (W.polarVectors_inner hv h0) (W.polarVectors_annihilate h0) x y

lemma defectCopies_commute (j k : Fin rankNum)
    (x : HereditaryTransport.corner (1-W.h) W.defect_selfAdjoint) :
    Commute (W.x j k) (W.defectCopies hv h0 x) :=
  HereditaryTransport.copies_commute W.defect_selfAdjoint (W.polarVectors v)
    (W.polarVectors_inner hv h0) W.x W.star_x (W.units_polarVectors h0) j k x

end KirchbergRordam.GenericRW.OrderZero.WeightedUnits

namespace KirchbergRordam.GenericRW.OrderZero.WeightedUnits
open scoped CStarAlgebra BigOperators
open ConeModel FlipPath HereditaryTransport
variable {A : Type*} [CStarAlgebra A] [Nontrivial A] [PartialOrder A] [StarOrderedRing A]
variable (W : WeightedUnits (Fin rankNum) A)

abbrev lambda : Defect →⋆ₙₐ[ℂ] HereditaryTransport.corner (1-W.h) W.defect_selfAdjoint :=
  W.toWeightedMatrix.defectHom

def rwK : Matrix (Fin rankNum) (Fin rankNum) (HereditaryTransport.corner (1-W.h) W.defect_selfAdjoint) :=
  fun i j => W.lambda (weightedK i j)
def rwH := W.lambda scalarG
def rwQ := W.lambda scalarQ

lemma rwQ_star : star W.rwQ=W.rwQ := by
  change star (W.lambda scalarQ)=W.lambda scalarQ
  rw [← map_star,scalarQ_star]
lemma rwQ_sq : W.rwQ*W.rwQ=W.rwH := by
  change W.lambda scalarQ*W.lambda scalarQ=W.lambda scalarG
  rw [← map_mul,scalarQ_sq]

lemma rwK_star_mul : star W.rwK*W.rwK=Matrix.diagonal (fun _ => W.rwH) := by
  apply Matrix.ext; intro i j
  have he := congrArg (fun matrix : Matrix (Fin rankNum) (Fin rankNum) Defect =>
    W.lambda (matrix i j)) weightedK_star_mul
  simp only [Matrix.mul_apply,Matrix.star_apply,map_sum,map_mul,map_star,
    Matrix.diagonal_apply] at he ⊢
  split_ifs at he ⊢ <;> simpa only [map_zero,rwK,rwH] using he
lemma rwK_mul_star : W.rwK*star W.rwK=Matrix.diagonal (fun _ => W.rwH) := by
  apply Matrix.ext; intro i j
  have he := congrArg (fun matrix : Matrix (Fin rankNum) (Fin rankNum) Defect =>
    W.lambda (matrix i j)) weightedK_mul_star
  simp only [Matrix.mul_apply,Matrix.star_apply,map_sum,map_mul,map_star,
    Matrix.diagonal_apply] at he ⊢
  split_ifs at he ⊢ <;> simpa only [map_zero,rwK,rwH] using he

lemma rwH_norm : ‖(W.rwH:A)‖≤1 := by
  have h₁ := NonUnitalStarAlgHom.norm_apply_le W.lambda scalarG
  have h₂ := NonUnitalStarAlgHom.norm_apply_le ConeModel.scalar RWFunctions.g
  exact h₁.trans (h₂.trans RWFunctions.g_norm)

def rwAlpha {v : A} (hv : star v*v=1-W.h) (h0 : W.x 0 0*v=v) : WeightedUnits (Fin (rankNum+1)) A :=
  tripleUnits W.defect_selfAdjoint (W.polarVectors v) (W.polarVectors_inner hv h0)
    (W.polarVectors_annihilate h0) W.rwK W.rwH W.rwQ W.rwQ_star W.rwQ_sq
      W.rwK_star_mul W.rwK_mul_star W.rwH_norm

lemma rwAlpha_total {v : A} (hv : star v*v=1-W.h) (h0 : W.x 0 0*v=v) :
    (W.rwAlpha hv h0).h=W.defectCopies hv h0 W.rwH+(W.rwH:A) :=
  triple_total W.defect_selfAdjoint (W.polarVectors v) (W.polarVectors_inner hv h0)
    W.rwK W.rwH W.rwQ W.rwQ_star W.rwQ_sq W.rwK_mul_star

end KirchbergRordam.GenericRW.OrderZero.WeightedUnits

namespace KirchbergRordam.GenericRW.OrderZero.WeightedUnits
open scoped BigOperators
variable {A : Type*} [CStarAlgebra A] [PartialOrder A]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def rescale (W : WeightedUnits ι A) (r l : A) (hr : IsSelfAdjoint r)
    (hc : ∀ i j,Commute r (W.x i j)) (he : r*W.h=l)
    (hp : 0≤l) (hn : ‖l‖≤1) : WeightedUnits ι A where
  h := l
  x i j := r*W.x i j
  nonneg := hp
  norm_le := hn
  star_x i j := by rw [star_mul,W.star_x,hr.star_eq,(hc j i).eq]
  mul_x i j k n := by
    calc
      _=r*r*(W.x i j*W.x k n) := by rw [mul_assoc,← mul_assoc (W.x i j),← (hc i j).eq]; noncomm_ring
      _=if j=k then l*(r*W.x i n) else 0 := by
        rw [W.mul_x]
        split_ifs
        · have ch : Commute r W.h := by
            rw [← W.diagonal]; exact Commute.sum_right Finset.univ (fun t => W.x t t) r fun t _ => hc t t
          rw [← he]
          calc
            _=r*(r*W.h)*W.x i n := by noncomm_ring
            _=r*(W.h*r)*W.x i n := by rw [ch.eq]
            _=_ := by noncomm_ring
        · simp
  diagonal := by rw [← Finset.mul_sum,W.diagonal,he]

end KirchbergRordam.GenericRW.OrderZero.WeightedUnits

namespace KirchbergRordam.GenericRW.ConeModel

def scalarRemainder (f : C(unitInterval,ℂ)) : Defect :=
  scalarDefect (f-ContinuousMap.const _ (f 1)) (by simp)
end KirchbergRordam.GenericRW.ConeModel

namespace KirchbergRordam.GenericRW.OrderZero.WeightedUnits
open scoped CStarAlgebra BigOperators
open ConeModel FlipPath HereditaryTransport
variable {A : Type*} [CStarAlgebra A] [Nontrivial A] [PartialOrder A] [StarOrderedRing A]
variable (W : WeightedUnits (Fin rankNum) A)

lemma lambda_remainder (f : C(unitInterval,ℂ)) :
    (W.lambda (scalarRemainder f):A)=W.toWeightedMatrix.eval f-algebraMap ℂ A (f 1) := by
  rw [show (W.lambda (scalarRemainder f):A)=
    W.toWeightedMatrix.eval (f-ContinuousMap.const _ (f 1)) from
      W.toWeightedMatrix.defectHom_scalar _ _,map_sub]
  congr 1
  exact AlgHomClass.commutes W.toWeightedMatrix.eval (f 1)

lemma scalar_mul_left {v : A} (hv : star v*v=1-W.h) (h0 : W.x 0 0*v=v)
    (f : C(unitInterval,ℂ)) (i : Fin rankNum) (x : HereditaryTransport.corner (1-W.h) W.defect_selfAdjoint) :
    W.toWeightedMatrix.eval f*left (v := W.polarVectors v i) W.defect_selfAdjoint x=
      (f 1) • left (v := W.polarVectors v i) W.defect_selfAdjoint x := by
  have h := corner_mul_left W.defect_selfAdjoint (W.polarVectors v) (W.polarVectors_inner hv h0)
    (W.polarVectors_annihilate h0) i (W.lambda (scalarRemainder f)) x
  rw [W.lambda_remainder,sub_mul,Algebra.algebraMap_eq_smul_one,smul_mul_assoc,one_mul] at h
  exact sub_eq_zero.mp h

lemma scalar_mul_copies {v : A} (hv : star v*v=1-W.h) (h0 : W.x 0 0*v=v)
    (f : C(unitInterval,ℂ)) (x : HereditaryTransport.corner (1-W.h) W.defect_selfAdjoint) :
    W.toWeightedMatrix.eval f*W.defectCopies hv h0 x=(f 1) • W.defectCopies hv h0 x := by
  have h := W.defectCopies_orthogonal hv h0 (W.lambda (scalarRemainder f)) x
  rw [W.lambda_remainder,sub_mul,Algebra.algebraMap_eq_smul_one,smul_mul_assoc,one_mul] at h
  exact sub_eq_zero.mp h

lemma copies_mul_scalar {v : A} (hv : star v*v=1-W.h) (h0 : W.x 0 0*v=v)
    (f : C(unitInterval,ℂ)) (x : HereditaryTransport.corner (1-W.h) W.defect_selfAdjoint) :
    W.defectCopies hv h0 x*W.toWeightedMatrix.eval f=(f 1) • W.defectCopies hv h0 x := by
  have h := congrArg star (W.scalar_mul_copies hv h0 (star f) (star x))
  simpa only [map_star,star_mul,star_star,star_smul,ContinuousMap.star_apply] using h

end KirchbergRordam.GenericRW.OrderZero.WeightedUnits

namespace KirchbergRordam.GenericRW.OrderZero.WeightedUnits
open scoped CStarAlgebra BigOperators
open ConeModel FlipPath HereditaryTransport RWFunctions
variable {A : Type*} [CStarAlgebra A] [Nontrivial A] [PartialOrder A] [StarOrderedRing A]
variable (W : WeightedUnits (Fin rankNum) A)
variable {v : A} (hv : star v*v=1-W.h) (h0 : W.x 0 0*v=v)

lemma rwH_val : (W.rwH:A)=W.toWeightedMatrix.eval g := W.toWeightedMatrix.defectHom_scalar _ _

lemma rwH_selfAdjoint : IsSelfAdjoint W.rwH := by
  rw [← W.rwQ_sq]
  change star (W.rwQ*W.rwQ)=W.rwQ*W.rwQ
  rw [star_mul,W.rwQ_star]

def rwL : A := 1-(W.rwAlpha hv h0).h

lemma rwL_eq : W.rwL hv h0=(1-(W.rwH:A))-W.defectCopies hv h0 W.rwH := by
  unfold rwL
  rw [W.rwAlpha_total hv h0]
  noncomm_ring

lemma rwL_nonneg : 0≤W.rwL hv h0 :=
  sub_nonneg.mpr ((CStarAlgebra.norm_le_one_iff_of_nonneg _ (W.rwAlpha hv h0).nonneg).mp
    (W.rwAlpha hv h0).norm_le)

lemma rwL_norm : ‖W.rwL hv h0‖≤1 := by
  rw [CStarAlgebra.norm_le_one_iff_of_nonneg _ (W.rwL_nonneg hv h0)]
  exact sub_le_self _ (W.rwAlpha hv h0).nonneg

lemma rwL_commute (i j : Fin rankNum) : Commute (W.rwL hv h0) (W.x i j) := by
  rw [W.rwL_eq hv h0,W.rwH_val]
  exact ((Commute.one_left _).sub_left (W.toWeightedMatrix.commute_eval i j g).symm).sub_left
    (W.defectCopies_commute hv h0 i j W.rwH).symm

lemma rwL_commute_scalar (f : C(unitInterval,ℂ)) :
    Commute (W.rwL hv h0) (W.toWeightedMatrix.eval f) := by
  rw [W.rwL_eq hv h0]
  apply Commute.sub_left
  · rw [W.rwH_val]
    exact (Commute.one_left _).sub_left ((Commute.all g f).map W.toWeightedMatrix.eval)
  · change W.defectCopies hv h0 W.rwH*W.toWeightedMatrix.eval f=
      W.toWeightedMatrix.eval f*W.defectCopies hv h0 W.rwH
    rw [W.copies_mul_scalar hv h0,W.scalar_mul_copies hv h0]

def rwR : A := W.rwL hv h0*W.toWeightedMatrix.eval j

lemma rwR_selfAdjoint : IsSelfAdjoint (W.rwR hv h0) := by
  change star (W.rwL hv h0*W.toWeightedMatrix.eval j)=_
  rw [star_mul,← map_star,j_star,(IsSelfAdjoint.of_nonneg (W.rwL_nonneg hv h0)).star_eq,
    (W.rwL_commute_scalar hv h0 j).symm.eq]
  rfl

lemma rwR_commute (i k : Fin rankNum) : Commute (W.rwR hv h0) (W.x i k) :=
  (W.rwL_commute hv h0 i k).mul_left (W.toWeightedMatrix.commute_eval i k j).symm

lemma rwR_total : W.rwR hv h0*W.h=W.rwL hv h0 := by
  have hr : (1-g)*j*IntervalCalculus.coord=1-g := by
    ext t; exact residual_inverse t
  have he : (1-W.toWeightedMatrix.eval g)*W.toWeightedMatrix.eval j*W.h=
      1-W.toWeightedMatrix.eval g := by
    have ht := congrArg W.toWeightedMatrix.eval hr
    simpa only [map_mul,map_sub,map_one,IntervalCalculus.hom_coord,toWeightedMatrix] using ht
  have hc : W.defectCopies hv h0 W.rwH*(W.toWeightedMatrix.eval j*W.h)=
      W.defectCopies hv h0 W.rwH := by
    have ht := W.copies_mul_scalar hv h0 (j*IntervalCalculus.coord) W.rwH
    have h₁ : (j*IntervalCalculus.coord) 1=1 := by
      change j 1*(((1:unitInterval):ℝ):ℂ)=1
      rw [j_one]
      norm_num
    rw [h₁,one_smul,map_mul,IntervalCalculus.hom_coord] at ht
    exact ht

  rw [rwR,W.rwL_eq hv h0,W.rwH_val,sub_mul,sub_mul,he,mul_assoc,hc]

def rwBeta : WeightedUnits (Fin rankNum) A :=
  W.rescale (W.rwR hv h0) (W.rwL hv h0) (W.rwR_selfAdjoint hv h0)
    (W.rwR_commute hv h0) (W.rwR_total hv h0) (W.rwL_nonneg hv h0) (W.rwL_norm hv h0)

lemma rw_complementary : (W.rwAlpha hv h0).h+(W.rwBeta hv h0).h=1 := by
  change (W.rwAlpha hv h0).h+(1-(W.rwAlpha hv h0).h)=1
  noncomm_ring

end KirchbergRordam.GenericRW.OrderZero.WeightedUnits
namespace KirchbergRordam.GenericRW.ConeModel

def defectMul (x : Defect) (y : Cone) : Defect :=
  ⟨(x:Cone)*y,by
    change (x:C(unitInterval,M2)) 1*(y:C(unitInterval,M2)) 1=0
    rw [x.property,zero_mul]⟩
end KirchbergRordam.GenericRW.ConeModel

namespace KirchbergRordam.GenericRW.FlipPath
open ConeModel RWFunctions
open scoped BigOperators

def weightedC (r i : Fin rankNum) : Defect := weightedK r i*scalarQ

lemma weightedC_val (r i : Fin rankNum) : (weightedC r i:Cone)=scalar g*star (conePath i r) := by
  change (scalar q*star (conePath i r))*scalar q=scalar g*star (conePath i r)
  rw [mul_assoc,← (scalar_commute q (star (conePath i r))).eq,← mul_assoc,← map_mul,q_sq]

lemma conePath_top {t : unitInterval} (ht : (2/3:ℝ)≤t) (i r : Fin rankNum) :
    (conePath i r:C(unitInterval,ConeModel.M2)) t=
      CStarMatrix.ofMatrix (Matrix.single r i 1) := by
  ext a b
  change path t (a,i) (b,r)=(Matrix.single r i 1) a b
  rw [path_top ht]
  simp [flip,Matrix.single,eq_comm,ite_and]

def e (i j : Fin rankNum) : ConeModel.M2 := CStarMatrix.ofMatrix (Matrix.single i j 1)

lemma e_star (i j : Fin rankNum) : star (e i j)=e j i := by
  ext a b
  simp [e,CStarMatrix.star_apply,Matrix.single,and_comm]

lemma e_mul (i r j k : Fin rankNum) : e i r*e j k=if r=j then e i k else 0 := by
  change CStarMatrix.ofMatrix (Matrix.single i r 1 * Matrix.single j k 1)=_
  by_cases hrj : r=j
  · subst j; simp [Matrix.single_mul_single_same,e]
  · rw [Matrix.single_mul_single_of_ne 1 i r j hrj 1,ite_eq_right hrj]; rfl

lemma scalar_weight (z : ℂ) (x : ConeModel.M2) :
    algebraMap ℂ ConeModel.M2 z*x-algebraMap ℂ ConeModel.M2 z*(algebraMap ℂ ConeModel.M2 z*x)=
      (z-z*z) • x := by
  simp only [Algebra.algebraMap_eq_smul_one,smul_mul_assoc,one_mul,smul_smul,sub_smul]

lemma weightedC_apply (r i : Fin rankNum) (t : unitInterval) :
    (weightedC r i:C(unitInterval,ConeModel.M2)) t=
      algebraMap ℂ ConeModel.M2 (g t)*star ((conePath i r:C(unitInterval,ConeModel.M2)) t) :=
  congrArg (fun x : Cone => (x:C(unitInterval,ConeModel.M2)) t) (weightedC_val r i)

lemma weightedC_residual_apply (r i : Fin rankNum) (t : unitInterval) :
    (((weightedC r i-scalarG*weightedC r i:Defect):Cone):C(unitInterval,ConeModel.M2)) t=
      (g t-g t*g t) • star ((conePath i r:C(unitInterval,ConeModel.M2)) t) := by
  change (weightedC r i:C(unitInterval,ConeModel.M2)) t-
    algebraMap ℂ ConeModel.M2 (g t)*(weightedC r i:C(unitInterval,ConeModel.M2)) t=_
  rw [weightedC_apply,scalar_weight]

lemma weightedC_flip_pointwise (r i j k : Fin rankNum) (t : unitInterval) :
    ((g t-g t*g t) • star ((conePath i r:C(unitInterval,ConeModel.M2)) t))*
      (algebraMap ℂ ConeModel.M2 (RWFunctions.j t)*(((t:ℝ):ℂ) • e j k))=
    if r=j then (g t-g t*g t) • star ((conePath i k:C(unitInterval,ConeModel.M2)) t) else 0 := by
  by_cases ht : (2/3:ℝ)≤t
  · rw [conePath_top ht,conePath_top ht]
    change ((g t-g t*g t) • star (e r i))*(algebraMap ℂ ConeModel.M2 (RWFunctions.j t)*((t:ℝ):ℂ) • e j k)=_
    rw [Algebra.algebraMap_eq_smul_one,e_star]
    simp only [smul_mul_assoc,mul_smul_comm,one_mul,smul_smul]
    rw [e_mul]
    have hgg : ((t:ℝ):ℂ)*RWFunctions.j t*(g t-g t*g t)=g t-g t*g t := by
      calc
        _=g t*((1-g t)*RWFunctions.j t*((t:ℝ):ℂ)) := by ring
        _=_ := by rw [residual_inverse]; ring
    by_cases hrj : r=j
    · rw [ite_eq_left hrj,ite_eq_left hrj,hgg]
      change _=(g t-g t*g t) • star (e k i)
      rw [e_star]
    · rw [ite_eq_right hrj,ite_eq_right hrj,smul_zero]
  · have hg := g_low (le_of_lt (lt_of_not_ge ht))
    rw [hg,one_mul,sub_self,zero_smul,zero_mul,zero_smul,ite_self]


lemma weightedC_flip (r i j k : Fin rankNum) :
    defectMul (weightedC r i-scalarG*weightedC r i)
      (scalar RWFunctions.j*ConeModel.corner j k)=
      if r=j then weightedC k i-scalarG*weightedC k i else 0 := by
  apply Subtype.ext
  apply Subtype.ext
  apply ContinuousMap.ext
  intro t
  have hz : ((0:Defect):C(unitInterval,ConeModel.M2)) t=0 := rfl
  change ((((weightedC r i-scalarG*weightedC r i:Defect):Cone):C(unitInterval,ConeModel.M2)) t*
    (algebraMap ℂ ConeModel.M2 (RWFunctions.j t)*(ConeModel.corner j k:C(unitInterval,ConeModel.M2)) t))=_
  rw [weightedC_residual_apply,corner_apply]
  change ((g t-g t*g t) • star ((conePath i r:C(unitInterval,ConeModel.M2)) t))*
      (algebraMap ℂ ConeModel.M2 (RWFunctions.j t)*(((t:ℝ):ℂ) • e j k))=_
  rw [weightedC_flip_pointwise]
  by_cases hrj : r=j
  · rw [ite_eq_left hrj,ite_eq_left hrj,weightedC_residual_apply]
  · rw [ite_eq_right hrj,ite_eq_right hrj]; exact hz.symm
end KirchbergRordam.GenericRW.FlipPath
namespace KirchbergRordam.GenericRW.OrderZero.WeightedUnits
open scoped CStarAlgebra BigOperators
open ConeModel FlipPath HereditaryTransport RWFunctions
local instance : SMul ℂ Defect := (NonUnitalStarSubalgebra.instModule Defect).toSMul
variable {A : Type*} [CStarAlgebra A] [Nontrivial A] [PartialOrder A] [StarOrderedRing A]
variable (W : WeightedUnits (Fin rankNum) A)
variable {v : A} (hv : star v*v=1-W.h) (h0 : W.x 0 0*v=v)

def rwLeft (i : Fin rankNum) : Defect →ₗ[ℂ] A where
  toFun x := leftLinear W.defect_selfAdjoint (W.polarVectors v) i (W.lambda x)
  map_add' x y := by rw [map_add,map_add]
  map_smul' c x := by rw [map_smul,map_smul]; rfl

lemma rwLeft_sub (r : Fin rankNum) (x y : Defect) :
    W.rwLeft (v := v) r (x-y)=W.rwLeft (v := v) r x-W.rwLeft (v := v) r y :=
  map_sub (W.rwLeft (v := v) r) x y

include hv h0

lemma rwLeft_mul (r : Fin rankNum) (x : Defect) (y : Cone) :
    W.rwLeft (v := v) r (defectMul x y)=W.rwLeft (v := v) r x*W.coneHom y := by
  apply left_mul_of_eq W.defect_selfAdjoint (copy_norm _ (W.polarVectors_inner hv h0) r)
  change W.coneHom ((x:Cone)*y)=W.coneHom (x:Cone)*W.coneHom y
  exact map_mul _ _ _

lemma rw_spoke (i : Fin rankNum) : (W.rwAlpha hv h0).x (Fin.castSucc i) (Fin.last rankNum)=
    ∑ r,W.rwLeft (v := v) r (weightedC r i) := by
  have he (r : Fin rankNum) := W.rwLeft_mul hv h0 r (weightedK r i) (scalar q)
  rw [W.toWeightedMatrix.coneHom_scalar,← W.toWeightedMatrix.defectHom_scalar q q_one] at he
  have h (r : Fin rankNum) : W.rwLeft (v := v) r (weightedC r i)=
      left (v := W.polarVectors v r) W.defect_selfAdjoint (W.rwK r i)*(W.rwQ:A) := he r
  change star (triple W.defect_selfAdjoint (W.polarVectors v) W.rwK W.rwQ i.castSucc) *
    triple W.defect_selfAdjoint (W.polarVectors v) W.rwK W.rwQ (Fin.last rankNum) = _
  rw [triple_castSucc,triple_last,star_star]
  simp only [frame,Finset.sum_mul]
  exact Finset.sum_congr rfl fun r _ => (h r).symm

lemma rwLeft_scalar (r : Fin rankNum) (f : C(unitInterval,ℂ)) (x : Defect) :
    W.toWeightedMatrix.eval f*W.rwLeft (v := v) r x=(f 1) • W.rwLeft (v := v) r x :=
  W.scalar_mul_left hv h0 f r (W.lambda x)

lemma rwLeft_units (j k r : Fin rankNum) (x : Defect) :
    W.x j k*W.rwLeft (v := v) r x=if k=r then W.rwLeft (v := v) j x else 0 :=
  units_mul_left W.defect_selfAdjoint (W.polarVectors v) (W.polarVectors_inner hv h0)
    W.x (W.units_polarVectors h0) j k r (W.lambda x)

lemma rwL_mul_left (r : Fin rankNum) (x : Defect) :
    W.rwL hv h0*W.rwLeft (v := v) r x=W.rwLeft (v := v) r (x-scalarG*x) := by
  have hH : (W.rwH:A)*W.rwLeft (v := v) r x=0 :=
    corner_mul_left W.defect_selfAdjoint (W.polarVectors v) (W.polarVectors_inner hv h0)
      (W.polarVectors_annihilate h0) r W.rwH (W.lambda x)
  have hP : W.defectCopies hv h0 W.rwH*W.rwLeft (v := v) r x=
      W.rwLeft (v := v) r (scalarG*x) := by
    change copies W.defect_selfAdjoint (W.polarVectors v) _ _*left W.defect_selfAdjoint _=_
    rw [copies_mul_left]
    change left W.defect_selfAdjoint (W.lambda scalarG*W.lambda x)=left W.defect_selfAdjoint (W.lambda (scalarG*x))
    rw [map_mul]
  calc
    _=W.rwLeft (v := v) r x-(W.rwH:A)*W.rwLeft (v := v) r x-
        W.defectCopies hv h0 W.rwH*W.rwLeft (v := v) r x := by
      rw [W.rwL_eq hv h0]
      noncomm_ring
    _=W.rwLeft (v := v) r x-W.rwLeft (v := v) r (scalarG*x) :=
      (congrArg₂ (fun y z : A => W.rwLeft (v := v) r x-y-z) hH hP).trans
        (by simp only [sub_zero])
    _=_ := (W.rwLeft_sub r x (scalarG*x)).symm

lemma rwBeta_mul_spoke (i j k : Fin rankNum) :
    (W.rwBeta hv h0).x j k*(W.rwAlpha hv h0).x (Fin.castSucc i) (Fin.last rankNum)=
      W.rwLeft (v := v) j (weightedC k i-scalarG*weightedC k i) := by
  rw [W.rw_spoke hv h0]
  change (W.rwL hv h0*W.toWeightedMatrix.eval RWFunctions.j*W.x j k)*_= _
  rw [mul_assoc,mul_assoc,Finset.mul_sum]
  simp only [W.rwLeft_units hv h0]
  rw [Finset.sum_ite_eq,ite_eq_left (Finset.mem_univ k)]
  have hj : W.toWeightedMatrix.eval RWFunctions.j*W.rwLeft (v := v) j (weightedC k i)=
      W.rwLeft (v := v) j (weightedC k i) := by
    simpa only [j_one,one_smul] using W.rwLeft_scalar hv h0 j RWFunctions.j (weightedC k i)
  rw [hj]
  exact W.rwL_mul_left hv h0 j (weightedC k i)

lemma rwLeft_mul_beta (r j k : Fin rankNum) (x : Defect) :
    W.rwLeft (v := v) r x*(W.rwBeta hv h0).x j k=
      W.rwLeft (v := v) r (defectMul (x-scalarG*x) (scalar RWFunctions.j*ConeModel.corner j k)) := by
  have hP : W.rwLeft (v := v) r x*W.defectCopies hv h0 W.rwH=0 :=
    left_mul_copies W.defect_selfAdjoint (W.polarVectors v) (W.polarVectors_inner hv h0)
      (W.polarVectors_annihilate h0) r (W.lambda x) W.rwH
  have hH : W.rwLeft (v := v) r x*(W.rwH:A)=W.rwLeft (v := v) r (scalarG*x) := by
    have h := W.rwLeft_mul hv h0 r x (scalar g)
    rw [W.toWeightedMatrix.coneHom_scalar,← W.rwH_val] at h
    rw [← h]
    congr 1
    apply Subtype.ext
    exact (scalar_commute g (x:Cone)).symm.eq
  have hL : W.rwLeft (v := v) r x*W.rwL hv h0=W.rwLeft (v := v) r (x-scalarG*x) := by
    calc
      _=W.rwLeft (v := v) r x-W.rwLeft (v := v) r x*(W.rwH:A)-
          W.rwLeft (v := v) r x*W.defectCopies hv h0 W.rwH := by
        rw [W.rwL_eq hv h0]
        noncomm_ring
      _=W.rwLeft (v := v) r x-W.rwLeft (v := v) r (scalarG*x) :=
        (congrArg₂ (fun y z : A => W.rwLeft (v := v) r x-y-z) hH hP).trans
          (by simp only [sub_zero])
      _=_ := (W.rwLeft_sub r x (scalarG*x)).symm
  have hm : W.coneHom (scalar RWFunctions.j*ConeModel.corner j k)=
      W.toWeightedMatrix.eval RWFunctions.j*W.x j k :=
    (map_mul W.coneHom _ _).trans (congrArg₂ (fun x y : A => x*y)
      (W.toWeightedMatrix.coneHom_scalar RWFunctions.j) (W.coneHom_corner j k))
  change W.rwLeft (v := v) r x*(W.rwL hv h0*W.toWeightedMatrix.eval RWFunctions.j*W.x j k)=_
  calc
    _=(W.rwLeft (v := v) r x*W.rwL hv h0)*(W.toWeightedMatrix.eval RWFunctions.j*W.x j k) := by noncomm_ring
    _=W.rwLeft (v := v) r (x-scalarG*x)*W.coneHom (scalar RWFunctions.j*ConeModel.corner j k) :=
      congrArg₂ (fun x y : A => x*y) hL hm.symm
    _=_ := (W.rwLeft_mul hv h0 r (x-scalarG*x) (scalar RWFunctions.j*ConeModel.corner j k)).symm

lemma rw_commute_spoke (i j k : Fin rankNum) :
    Commute ((W.rwBeta hv h0).x j k) ((W.rwAlpha hv h0).x (Fin.castSucc i) (Fin.last rankNum)) := by
  change _=_
  rw [W.rwBeta_mul_spoke hv h0,W.rw_spoke hv h0,Finset.sum_mul]
  simp only [W.rwLeft_mul_beta hv h0,weightedC_flip]
  rw [Finset.sum_eq_single j]
  · rw [ite_eq_left rfl]
  · intro r _ hrj
    rw [ite_eq_right hrj,map_zero]
  · simp

end KirchbergRordam.GenericRW.OrderZero.WeightedUnits
end

end OAI
