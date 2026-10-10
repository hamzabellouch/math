import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.DimensionDrop.UniqueTrace

namespace OAI

noncomputable section


namespace JiangSuConstruction
open scoped CStarAlgebra ComplexOrder


variable {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]

omit [DecidableEq I] in
lemma normalizedMatrixTrace_norm (a : CStarMatrix I I ℂ) :
    ‖(Fintype.card I:ℂ)⁻¹ * matrixTrace a‖≤‖a‖ := by
  have hn : (0:ℝ)<(Fintype.card I:ℝ) := by exact_mod_cast Fintype.card_pos
  rw [norm_mul,norm_inv,Complex.norm_natCast,inv_mul_le_iff₀ hn]
  change ‖∑ i:I,a i i‖≤(Fintype.card I:ℝ)*‖a‖
  calc _ ≤ ∑ _i:I,‖a‖ := (norm_sum_le _ _).trans (Finset.sum_le_sum (fun _ _ => CStarMatrix.norm_entry_le_norm))
       _ = _ := by simp

lemma normalizedMatrixTrace_one :
    (Fintype.card I:ℂ)⁻¹*matrixTrace (1:CStarMatrix I I ℂ)=1 := by
  have hn : (Fintype.card I:ℂ)≠0 := by exact_mod_cast Fintype.card_ne_zero
  change (Fintype.card I:ℂ)⁻¹*Matrix.trace (1:Matrix I I ℂ)=1
  rw [Matrix.trace_one]
  simpa only [nsmul_eq_mul,mul_one] using inv_mul_cancel₀ hn

attribute [local instance] stagePNeZero stageQNeZero

def stageTrace (n : ℕ) : StageAlgebra n →ₗ[ℂ] ℂ :=
  ((Fintype.card (Fin (stagePair n).p×Fin (stagePair n).q):ℂ)⁻¹ • matrixTrace).comp
    (((evalHom _ _ leftEndpoint).comp (dimensionDrop _ _).subtype).toLinearMap)

lemma stageTrace_norm (n : ℕ) (a : StageAlgebra n) : ‖stageTrace n a‖≤‖a‖ :=
  (normalizedMatrixTrace_norm (a.val leftEndpoint)).trans (a.val.norm_coe_le_norm leftEndpoint)
lemma stageTrace_one (n : ℕ) : stageTrace n 1=1 := normalizedMatrixTrace_one
lemma stageTrace_tracial (n : ℕ) (a b : StageAlgebra n) :
    stageTrace n (a*b)=stageTrace n (b*a) := by
  change _*matrixTrace (a.val leftEndpoint*b.val leftEndpoint)=_*matrixTrace (b.val leftEndpoint*a.val leftEndpoint)
  rw [matrixTrace_mul_comm]

def primeDropTrace : PrimeDropLimit →L[ℂ] ℂ :=
  SequentialCStar.limitTrace stageTrace stageTrace_norm concreteSystem

lemma primeDropTrace_one : primeDropTrace 1=1 :=
  SequentialCStar.limitTrace_normalized _ _ _ stageTrace_one
lemma primeDropTrace_tracial (a b : PrimeDropLimit) : primeDropTrace (a*b)=primeDropTrace (b*a) :=
  SequentialCStar.limitTrace_tracial _ _ _ stageTrace_tracial a b
lemma primeDropTrace_norm : ‖primeDropTrace‖≤1 := SequentialCStar.limitTrace_norm _ _ _

theorem primeDropLimit_existsUnique_trace :
    ∃! τ : PrimeDropLimit →L[ℂ] ℂ,
      (∀ a b,τ (a*b)=τ (b*a)) ∧ τ 1=1 ∧ ‖τ‖≤1 := by
  refine ⟨primeDropTrace,⟨primeDropTrace_tracial,primeDropTrace_one,primeDropTrace_norm⟩,?_⟩
  intro σ hσ
  exact primeDropLimit_trace_unique σ primeDropTrace hσ.1 primeDropTrace_tracial
    hσ.2.1 primeDropTrace_one hσ.2.2 primeDropTrace_norm

end JiangSuConstruction



section
open scoped CStarAlgebra ComplexOrder

namespace SequentialCStar
open TraceCone Filter

variable {C : ℕ → Type*} [∀ n,CStarAlgebra (C n)] [∀ n,Nontrivial (C n)]
variable (τ : ∀ n,C n →ₗ[ℂ] ℂ) (hτ : ∀ n a,‖τ n a‖ ≤ ‖a‖)

lemma quotientTrace_star_mul_self_nonneg
    (hpos : ∀ n a,0 ≤ τ n (star a*a)) (x : FamilyQuotient C) :
    0 ≤ quotientTrace τ hτ (star x*x) := by
  obtain ⟨a,rfl⟩ := FamilyQuotient.mk_surjective x
  change 0 ≤ familyTraceValue τ (star a*a)
  apply ge_of_tendsto (familyTraceValue_tendsto τ hτ (star a*a))
  exact Eventually.of_forall (fun n => hpos n (a n))

lemma limitTrace_nonneg (S : System C) [PartialOrder S.Limit] [StarOrderedRing S.Limit] (hpos : ∀ n a,0 ≤ τ n (star a*a))
    {x : S.Limit} (hx : 0 ≤ x) : 0 ≤ limitTrace τ hτ S x := by
  obtain ⟨a,rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hx
  exact quotientTrace_star_mul_self_nonneg τ hτ hpos a.val
end SequentialCStar

namespace JiangSuConstruction
attribute [local instance] stagePNeZero stageQNeZero

instance primeDropOrder : PartialOrder PrimeDropLimit := CStarAlgebra.spectralOrder _
instance primeDropOrderedRing : StarOrderedRing PrimeDropLimit := CStarAlgebra.spectralOrderedRing _

lemma normalizedMatrixTrace_star_mul_self_nonneg {I : Type*}
    [Fintype I] [DecidableEq I] (a : CStarMatrix I I ℂ) :
    0 ≤ (Fintype.card I:ℂ)⁻¹*matrixTrace (star a*a) := by
  apply mul_nonneg (by positivity)
  exact (Matrix.posSemidef_conjTranspose_mul_self (CStarMatrix.ofMatrix.symm a)).trace_nonneg

lemma stageTrace_star_mul_self_nonneg (n : ℕ) (a : StageAlgebra n) :
    0 ≤ stageTrace n (star a*a) := normalizedMatrixTrace_star_mul_self_nonneg (a.val leftEndpoint)

lemma primeDropTrace_nonneg {x : PrimeDropLimit} (hx : 0 ≤ x) : 0 ≤ primeDropTrace x :=
  SequentialCStar.limitTrace_nonneg stageTrace stageTrace_norm concreteSystem stageTrace_star_mul_self_nonneg hx

def primeDropPositiveTrace : PrimeDropLimit →ₚ[ℂ] ℂ where
  toLinearMap := primeDropTrace.toLinearMap
  monotone' a b h := by
    change primeDropTrace a ≤ primeDropTrace b
    have he := primeDropTrace_nonneg (sub_nonneg.mpr h)
    simpa only [map_sub,sub_nonneg] using he

lemma primeDropPositiveTrace_one : primeDropPositiveTrace 1=1 := primeDropTrace_one
lemma primeDropPositiveTrace_tracial (a b : PrimeDropLimit) :
    primeDropPositiveTrace (a*b)=primeDropPositiveTrace (b*a) := primeDropTrace_tracial a b

end JiangSuConstruction

end


namespace JiangSuConstruction
open scoped ComplexOrder

variable {I : Type*} [Fintype I] [DecidableEq I]

def matrixUnit (i j : I) : CStarMatrix I I ℂ := CStarMatrix.ofMatrix (Matrix.single i j 1)

omit [Fintype I] in
lemma matrixUnit_star (i j : I) : star (matrixUnit i j)=matrixUnit j i := by
  change CStarMatrix.ofMatrix (Matrix.single i j (1:ℂ)).conjTranspose=_
  simp [matrixUnit,Matrix.conjTranspose_single]

lemma matrixUnit_sandwich (a : CStarMatrix I I ℂ) (i j : I) :
    star (matrixUnit i j)*a*matrixUnit i j=CStarMatrix.ofMatrix (Matrix.single j j (a i i)) := by
  rw [matrixUnit_star]
  change Matrix.single j i (1:ℂ)*(CStarMatrix.ofMatrix.symm a)*Matrix.single i j 1=Matrix.single j j (a i i)
  erw [Matrix.single_mul_mul_single]
  simp only [one_mul, mul_one, CStarMatrix.ofMatrix_symm_apply]

lemma matrixUnit_sum_sandwich (a : CStarMatrix I I ℂ) :
    ∑ i:I,∑ j:I,star (matrixUnit i j)*a*matrixUnit i j=matrixTrace a • (1:CStarMatrix I I ℂ) := by
  simp only [matrixUnit_sandwich]
  change (∑ i:I,∑ j:I,Matrix.single j j (a i i))=matrixTrace a • (1:Matrix I I ℂ)
  ext u v
  by_cases huv : u=v
  · subst v
    simp only [matrixTrace,Matrix.single,Matrix.smul_apply,Matrix.sum_apply,ite_and]
    simp
    rfl
  · simp [matrixTrace,Matrix.single,Matrix.smul_apply,Matrix.sum_apply,Matrix.trace,ite_and,huv]

omit [DecidableEq I] in
lemma matrixTrace_star_mul_self_pos {a : CStarMatrix I I ℂ} (ha : a≠0) :
    0 < matrixTrace (star a*a) := by
  have hp := (Matrix.posSemidef_conjTranspose_mul_self (CStarMatrix.ofMatrix.symm a)).trace_nonneg
  apply lt_of_le_of_ne hp
  intro hz
  apply ha
  have h : (star a*a).trace=0 := hz.symm
  exact Matrix.trace_conjTranspose_mul_self_eq_zero_iff.mp h

lemma matrixUnit_sum_posDef {a : CStarMatrix I I ℂ} (ha : a≠0) :
    (CStarMatrix.ofMatrix.symm (∑ i:I,∑ j:I,star (matrixUnit i j)*(star a*a)*matrixUnit i j)).PosDef := by
  rw [matrixUnit_sum_sandwich]
  exact Matrix.PosDef.one.smul (matrixTrace_star_mul_self_pos ha)

end JiangSuConstruction



namespace JiangSuConstruction
open scoped ComplexOrder Kronecker

variable {p q : ℕ}
local instance (priority := 2000) fullDropSemiring : Semiring (DimensionDrop p q) :=
  (inferInstance : CStarAlgebra (DimensionDrop p q)).toSemiring

def leftChannel (i j : Fin p) : DimensionDrop p q :=
  ⟨⟨fun t => ((1-t.val:ℝ):ℂ) • leftAmplification p q (matrixUnit i j),by fun_prop⟩,by
    constructor
    · refine ⟨matrixUnit i j,?_⟩
      change leftAmplification p q (matrixUnit i j)=((1-(leftEndpoint:Interval).val:ℝ):ℂ) • leftAmplification p q (matrixUnit i j)
      simp [leftEndpoint]
    · refine ⟨0,?_⟩
      change rightAmplification p q 0=((1-(rightEndpoint:Interval).val:ℝ):ℂ) • _
      simp [rightEndpoint]⟩

def rightChannel (i j : Fin q) : DimensionDrop p q :=
  ⟨⟨fun t => (t.val:ℂ) • rightAmplification p q (matrixUnit i j),by fun_prop⟩,by
    constructor
    · refine ⟨0,?_⟩
      change leftAmplification p q 0=((leftEndpoint:Interval).val:ℂ) • _
      simp [leftEndpoint]
    · refine ⟨matrixUnit i j,?_⟩
      change rightAmplification p q (matrixUnit i j)=((rightEndpoint:Interval).val:ℂ) • rightAmplification p q (matrixUnit i j)
      simp [rightEndpoint]⟩

def interiorChannel (i j : Fin p×Fin q) : DimensionDrop p q :=
  ⟨⟨fun t => ((t.val*(1-t.val):ℝ):ℂ) • matrixUnit i j,by fun_prop⟩,
    interior_mem (by simp [leftEndpoint]) (by simp [rightEndpoint])⟩

lemma leftChannel_eval_left (i j : Fin p) :
    (leftChannel (q := q) i j).val leftEndpoint=leftAmplification p q (matrixUnit i j) := by
  change ((1-0:ℝ):ℂ) • leftAmplification p q (matrixUnit i j)=leftAmplification p q (matrixUnit i j)
  simp

lemma rightChannel_eval_right (i j : Fin q) :
    (rightChannel (p := p) i j).val rightEndpoint=rightAmplification p q (matrixUnit i j) := by
  change (1:ℂ) • rightAmplification p q (matrixUnit i j)=rightAmplification p q (matrixUnit i j)
  exact one_smul ℂ _

def conjugationSum {J : Type*} [Fintype J]
    (v : J → DimensionDrop p q) (a : DimensionDrop p q) : DimensionDrop p q :=
  ∑ i,star (v i)*a*v i

def fullElement (f : DimensionDrop p q) : DimensionDrop p q :=
  conjugationSum (fun ij : Fin p×Fin p => leftChannel ij.1 ij.2) (star f*f)+
  conjugationSum (fun ij : (Fin p×Fin q)×(Fin p×Fin q) => interiorChannel ij.1 ij.2) (star f*f)+
  conjugationSum (fun ij : Fin q×Fin q => rightChannel ij.1 ij.2) (star f*f)

lemma conjugationSum_mem {J : Type*} [Fintype J] (v : J → DimensionDrop p q)
    (a : DimensionDrop p q) (I : TwoSidedIdeal (DimensionDrop p q)) (ha : a∈I) :
    conjugationSum v a∈I := by
  exact sum_mem (fun i _ => I.mul_mem_right _ _ (I.mul_mem_left _ _ ha))

lemma fullElement_mem (f : DimensionDrop p q) (I : TwoSidedIdeal (DimensionDrop p q))
    (hf : f∈I) : fullElement f∈I := by
  have hh := I.mul_mem_left (star f) f hf
  exact I.add_mem (I.add_mem (conjugationSum_mem _ _ _ hh) (conjugationSum_mem _ _ _ hh))
    (conjugationSum_mem _ _ _ hh)

lemma conjugationSum_eval {J : Type*} [Fintype J] (v : J → DimensionDrop p q)
    (a : DimensionDrop p q) (t : Interval) :
    (conjugationSum v a).val t=∑ i,star ((v i).val t)*(a.val t)*(v i).val t := by
  exact map_sum ((evalHom p q t).comp (dimensionDrop p q).subtype) _ _

lemma conjugationSum_posSemidef {J : Type*} [Fintype J] (v : J → DimensionDrop p q)
    (f : DimensionDrop p q) (t : Interval) :
    (CStarMatrix.ofMatrix.symm ((conjugationSum v (star f*f)).val t)).PosSemidef := by
  rw [conjugationSum_eval]
  change (∑ i, (CStarMatrix.ofMatrix.symm ((v i).val t)).conjTranspose*
    ((CStarMatrix.ofMatrix.symm (f.val t)).conjTranspose*CStarMatrix.ofMatrix.symm (f.val t))*
    CStarMatrix.ofMatrix.symm ((v i).val t)).PosSemidef
  exact Matrix.posSemidef_sum _ (fun i _ => (Matrix.posSemidef_conjTranspose_mul_self _).conjTranspose_mul_mul_same _)

lemma weighted_sandwich {I : Type*} [Fintype I] [DecidableEq I]
    (a v : CStarMatrix I I ℂ) (r : ℝ) :
    star ((r:ℂ) • v)*a*((r:ℂ) • v)=((r*r:ℝ):ℂ) • (star v*a*v) := by
  simp only [star_smul,Complex.star_def,Complex.conj_ofReal,smul_mul_assoc,mul_smul_comm,smul_smul,Complex.ofReal_mul]

lemma interiorSum_eval (f : DimensionDrop p q) (t : Interval) :
    (conjugationSum (fun ij : (Fin p×Fin q)×(Fin p×Fin q) => interiorChannel ij.1 ij.2) (star f*f)).val t =
      ((t.val*(1-t.val)*(t.val*(1-t.val)):ℝ):ℂ) • (matrixTrace (star (f.val t)*f.val t) • (1:TensorMat p q)) := by
  rw [conjugationSum_eval,Fintype.sum_prod_type]
  change (∑ i,∑ j,star (((t.val*(1-t.val):ℝ):ℂ) • matrixUnit i j)*(star (f.val t)*f.val t)*
    (((t.val*(1-t.val):ℝ):ℂ) • matrixUnit i j))=_
  simp only [weighted_sandwich,←Finset.smul_sum]
  rw [matrixUnit_sum_sandwich]

lemma leftSum_endpoint (f : DimensionDrop p q) (a : Mat p)
    (ha : leftAmplification p q a=f.val leftEndpoint) :
    (conjugationSum (fun ij : Fin p×Fin p => leftChannel ij.1 ij.2) (star f*f)).val leftEndpoint =
      matrixTrace (star a*a) • (1:TensorMat p q) := by
  rw [conjugationSum_eval,Fintype.sum_prod_type]
  simp only [leftChannel_eval_left]
  change (∑ i,∑ j,star (leftAmplification p q (matrixUnit i j))*(star (f.val leftEndpoint)*f.val leftEndpoint)*leftAmplification p q (matrixUnit i j))=_
  rw [←ha]
  simp only [←map_star,←map_mul,←map_sum]
  rw [matrixUnit_sum_sandwich,map_smul,map_one]

lemma rightSum_endpoint (f : DimensionDrop p q) (a : Mat q)
    (ha : rightAmplification p q a=f.val rightEndpoint) :
    (conjugationSum (fun ij : Fin q×Fin q => rightChannel ij.1 ij.2) (star f*f)).val rightEndpoint =
      matrixTrace (star a*a) • (1:TensorMat p q) := by
  rw [conjugationSum_eval,Fintype.sum_prod_type]
  simp only [rightChannel_eval_right]
  change (∑ i,∑ j,star (rightAmplification p q (matrixUnit i j))*(star (f.val rightEndpoint)*f.val rightEndpoint)*rightAmplification p q (matrixUnit i j))=_
  rw [←ha]
  simp only [←map_star,←map_mul,←map_sum]
  rw [matrixUnit_sum_sandwich,map_smul,map_one]

lemma fullElement_posDef (f : DimensionDrop p q) (hf : ∀ t,f.val t≠0) (t : Interval) :
    (CStarMatrix.ofMatrix.symm ((fullElement f).val t)).PosDef := by
  have hL := conjugationSum_posSemidef (fun ij : Fin p×Fin p => leftChannel ij.1 ij.2) f t
  have hI := conjugationSum_posSemidef (fun ij : (Fin p×Fin q)×(Fin p×Fin q) => interiorChannel ij.1 ij.2) f t
  have hR := conjugationSum_posSemidef (fun ij : Fin q×Fin q => rightChannel ij.1 ij.2) f t
  change ((CStarMatrix.ofMatrix.symm ((conjugationSum (fun ij : Fin p×Fin p => leftChannel ij.1 ij.2) (star f*f)).val t))+
    (CStarMatrix.ofMatrix.symm ((conjugationSum (fun ij : (Fin p×Fin q)×(Fin p×Fin q) => interiorChannel ij.1 ij.2) (star f*f)).val t))+
    (CStarMatrix.ofMatrix.symm ((conjugationSum (fun ij : Fin q×Fin q => rightChannel ij.1 ij.2) (star f*f)).val t))).PosDef
  by_cases ht0 : t=leftEndpoint
  · subst t
    obtain ⟨a,ha⟩ := f.property.1
    change leftAmplification p q a=f.val leftEndpoint at ha
    have ha0 : a≠0 := by intro he; apply hf leftEndpoint; rw [←ha,he,map_zero]
    have hD : (CStarMatrix.ofMatrix.symm ((conjugationSum (fun ij : Fin p×Fin p => leftChannel ij.1 ij.2) (star f*f)).val leftEndpoint)).PosDef := by
      rw [leftSum_endpoint f a ha]
      exact Matrix.PosDef.one.smul (matrixTrace_star_mul_self_pos ha0)
    exact (hD.add_posSemidef hI).add_posSemidef hR
  by_cases ht1 : t=rightEndpoint
  · subst t
    obtain ⟨a,ha⟩ := f.property.2
    change rightAmplification p q a=f.val rightEndpoint at ha
    have ha0 : a≠0 := by intro he; apply hf rightEndpoint; rw [←ha,he,map_zero]
    have hD : (CStarMatrix.ofMatrix.symm ((conjugationSum (fun ij : Fin q×Fin q => rightChannel ij.1 ij.2) (star f*f)).val rightEndpoint)).PosDef := by
      rw [rightSum_endpoint f a ha]
      exact Matrix.PosDef.one.smul (matrixTrace_star_mul_self_pos ha0)
    exact Matrix.PosDef.posSemidef_add (hL.add hI) hD
  have ht : 0<t.val ∧ t.val<1 := by
    constructor
    · exact lt_of_le_of_ne t.property.1 (fun h => ht0 (Subtype.ext h.symm))
    · exact lt_of_le_of_ne t.property.2 (fun h => ht1 (Subtype.ext h))
  have hD : (CStarMatrix.ofMatrix.symm ((conjugationSum (fun ij : (Fin p×Fin q)×(Fin p×Fin q) => interiorChannel ij.1 ij.2) (star f*f)).val t)).PosDef := by
    rw [interiorSum_eval]
    have hscalar : (0:ℂ)<((t.val*(1-t.val)*(t.val*(1-t.val)):ℝ):ℂ) := by
      exact_mod_cast mul_pos (mul_pos ht.1 (sub_pos.mpr ht.2)) (mul_pos ht.1 (sub_pos.mpr ht.2))
    exact (Matrix.PosDef.smul (Matrix.PosDef.smul (Matrix.PosDef.one (n := Fin p×Fin q) (R := ℂ))
      (matrixTrace_star_mul_self_pos (hf t))) hscalar)
  exact (Matrix.PosDef.posSemidef_add hL hD).add_posSemidef hR

lemma fullElement_isUnit (f : DimensionDrop p q) (hf : ∀ t,f.val t≠0) : IsUnit (fullElement f) := by
  have h : IsUnit ((fullElement f).val) := by
    apply (ContinuousMap.isUnit_iff_forall_isUnit _).mpr
    intro t
    exact (fullElement_posDef f hf t).isUnit.map (CStarMatrix.ofMatrixStarAlgEquiv (n := Fin p×Fin q) (A := ℂ)).toMonoidHom
  exact (@StarSubalgebra.coe_isUnit C(Interval,TensorMat p q) inferInstance
    (dimensionDrop p q) (dimensionDrop_closed p q) (fullElement f)).mp h

theorem dimensionDrop_full_of_fiberwise_nonzero (f : DimensionDrop p q)
    (hf : ∀ t,f.val t≠0) (I : TwoSidedIdeal (DimensionDrop p q)) (hIf : f∈I) : I=⊤ := by
  obtain ⟨u,hu⟩ := fullElement_isUnit f hf
  apply I.eq_top
  have h := I.mul_mem_left (↑u⁻¹) (fullElement f) (fullElement_mem f I hIf)
  rw [←hu,Units.inv_mul] at h
  exact h

end JiangSuConstruction


end

end OAI
