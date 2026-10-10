import OAI.NumberTheory.DirichletL.Eisenstein.RamifiedGaussSeries
import OAI.NumberTheory.DirichletL.Reciprocity.KubotaCharacter

namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical

open scoped BigOperators Classical
namespace CubicEisenstein

section
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CompletedGauss
local notation "Eis" => ActualEisensteinCubic.O

private theorem finite_tsum_comp_addHom {R S : Type*} [AddGroup R] [AddGroup S]
    [Finite R] [Finite S] (f:R→+S) (hf:Function.Surjective f) (F:S→ℂ) :
    (∑'x:R,F (f x))=(Nat.card f.ker:ℂ)*∑'y:S,F y := by
  let:Fintype R:=Fintype.ofFinite _
  let:Fintype S:=Fintype.ofFinite _
  let:Fintype f.ker:=Fintype.ofFinite _
  rw [tsum_fintype,tsum_fintype,←Fintype.sum_fiberwise' f F]
  have hc (y:S):Fintype.card {x:R//f x=y}=Fintype.card f.ker:=
    Fintype.card_congr (AddMonoidHom.fiberEquivKerOfSurjective hf y)
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,hc,Nat.card_eq_fintype_card]
  rw [Finset.mul_sum]

lemma ramified_affine_isUnit (u:Eisˣ) (n:ℕ)
    (x:Eis⧸Ideal.span {u.val*lambda^n}) : IsUnit (1+3*x) := by
  obtain ⟨d,rfl⟩:=Ideal.Quotient.mk_surjective x
  have hh:denominatorCondition (u.val*lambda^n) (1+3*d):=
    ramified_denominator_condition u n _ ⟨d,by ring⟩
  simpa only [map_add,map_one,map_mul,map_ofNat] using
    (isUnit_quotient_span_iff _ _).mpr hh.1

def ramifiedAffineEquiv (u:Eisˣ) (n:ℕ) :
    (Eis⧸Ideal.span {u.val*lambda^n})≃AdmissibleResidue (u.val*lambda^n):=
  (Equiv.subtypeUnivEquiv (ramified_affine_isUnit u n)).symm.trans (affineResidueEquiv _)

theorem ramified_arithmetic_affine (h:Eis) (u:Eisˣ) (n:ℕ) (hn:2≤n) :
    arithmeticResidueSum h (u.val*lambda^n)=
      ∑'x:Eis⧸Ideal.span {u.val*lambda^n},
        eisEmbedding (symbol (u.val*lambda^n)
          (1+3*GaussianShiftedPartition.representative (u.val*lambda^n) x))*
        residueAdditive h (u.val*lambda^n)
          (1+3*GaussianShiftedPartition.representative (u.val*lambda^n) x) := by
  rw [arithmeticResidueSum,←(ramifiedAffineEquiv u n).tsum_eq]
  apply tsum_congr
  intro x
  let a:=u.val*lambda^n
  let d:=1+3*GaussianShiftedPartition.representative a x
  have hd:(3:Eis)∣d-1:=⟨_,by dsimp [d];ring⟩
  have hrep:3*a∣denominatorRep a ((ramifiedAffineEquiv u n) x).val-d:=
    denominatorRep_mk_congr a d
  change eisEmbedding (symbol a (denominatorRep a ((ramifiedAffineEquiv u n) x).val))*
    residueAdditive h a (denominatorRep a ((ramifiedAffineEquiv u n) x).val)=_
  rw [row_symbol_congr_modulus a _ d (ramifiedElement_level u n hn) hd hrep,
    residueAdditive_congr h a _ d (ramifiedElement_ne_zero u n) hrep]

def ramifiedReduction (u:Eisˣ) (n:ℕ) (hn:2≤n) :
    (Eis⧸Ideal.span {u.val*lambda^n})→+*(Eis⧸Ideal.span {(3:Eis)}):=
  Ideal.Quotient.factor (Ideal.span_singleton_le_span_singleton.mpr
    (ramifiedElement_level u n hn))

lemma ramifiedReduction_surjective (u:Eisˣ) (n:ℕ) (hn:2≤n) :
    Function.Surjective (ramifiedReduction u n hn):=
  Ideal.Quotient.factor_surjective _

lemma ramifiedReduction_rep (u:Eisˣ) (n:ℕ) (hn:2≤n)
    (x:Eis⧸Ideal.span {u.val*lambda^n}) :
    (3:Eis)∣GaussianShiftedPartition.representative (u.val*lambda^n) x-
      GaussianShiftedPartition.representative 3 (ramifiedReduction u n hn x) := by
  apply Ideal.mem_span_singleton.mp
  apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp
  rw [GaussianShiftedPartition.representative_spec]
  have hh:=congrArg (ramifiedReduction u n hn)
    (GaussianShiftedPartition.representative_spec (u.val*lambda^n) x)
  exact hh

lemma residueAdditive_ramified_scale (h k a d:Eis) (ha:a≠0) (hk:3*h=a*k) :
    residueAdditive h a d=residueAdditive k 3 d := by
  unfold residueAdditive cuspFrequency
  congr 1
  have he:=congrArg eisEmbedding hk
  simp only [map_mul,map_ofNat] at he
  have ha':eisEmbedding a≠0:=eisEmbedding_ne_zero ha
  simp only [map_ofNat]
  field_simp
  linear_combination eisLam⁻¹*eisEmbedding d*he

def ramifiedNineSum (k:Eis) (u:Eisˣ) (n:ℕ):ℂ:=
  ∑'x:Eis⧸Ideal.span {(3:Eis)},
    eisEmbedding (symbol (u.val*lambda^n)
      (1+3*GaussianShiftedPartition.representative 3 x))*
      residueAdditive k 3 (1+3*GaussianShiftedPartition.representative 3 x)

lemma ramifiedReduction_kernel_card (u:Eisˣ) (n:ℕ) (hn:2≤n) :
    Nat.card (ramifiedReduction u n hn).toAddMonoidHom.ker=3^(n-2) := by
  have hc:=card_ring_eq_card_mul_kernel (ramifiedReduction u n hn)
    (ramifiedReduction_surjective u n hn)
  change Ideal.absNorm (Ideal.span {u.val*lambda^n})=
    Ideal.absNorm (Ideal.span {(3:Eis)})*Nat.card (ramifiedReduction u n hn).toAddMonoidHom.ker at hc
  rw [ramifiedElement_absNorm,three_absNorm] at hc
  have hn':n=2+(n-2):=by omega
  have hp:(3:ℕ)^n=9*3^(n-2):=by
    conv_lhs => rw [hn']
    rw [pow_add]
    norm_num
  omega

theorem ramified_arithmetic_nine_sum (h k:Eis) (u:Eisˣ) (n:ℕ) (hn:2≤n)
    (hk:3*h=(u.val*lambda^n)*k) :
    arithmeticResidueSum h (u.val*lambda^n)=
      ((3^(n-2):ℕ):ℂ)*ramifiedNineSum k u n := by
  let a:=u.val*lambda^n
  let f:=ramifiedReduction u n hn
  let F:Eis⧸Ideal.span {(3:Eis)}→ℂ:=fun x=>
    eisEmbedding (symbol a (1+3*GaussianShiftedPartition.representative 3 x))*
      residueAdditive k 3 (1+3*GaussianShiftedPartition.representative 3 x)
  have hpoint (x:Eis⧸Ideal.span {a}):
      eisEmbedding (symbol a (1+3*GaussianShiftedPartition.representative a x))*
        residueAdditive h a (1+3*GaussianShiftedPartition.representative a x)=F (f x):=by
    let d:=1+3*GaussianShiftedPartition.representative a x
    let e:=1+3*GaussianShiftedPartition.representative 3 (f x)
    have hd:(3:Eis)∣d-1:=⟨_,by dsimp [d];ring⟩
    have he:(3:Eis)∣e-1:=⟨_,by dsimp [e];ring⟩
    have h9:(9:Eis)∣d-e:=by
      obtain ⟨w,hw⟩:=ramifiedReduction_rep u n hn x
      exact ⟨w,by dsimp [d,e,f,a] at *;linear_combination 3*hw⟩
    change eisEmbedding (symbol a d)*residueAdditive h a d=F (f x)
    rw [ramified_symbol_congr_mod_nine u n d e hd he h9,
      residueAdditive_ramified_scale h k a d (ramifiedElement_ne_zero u n) hk,
      residueAdditive_congr k 3 d e (by norm_num) (by convert h9 using 1 ;norm_num)]
  let:Finite (Eis⧸Ideal.span {a}):=finite_quotient_span (ramifiedElement_ne_zero u n)
  let:Finite (Eis⧸Ideal.span {(3:Eis)}):=finite_quotient_span (by norm_num)
  rw [ramified_arithmetic_affine h u n hn]
  calc
    _=∑'x:Eis⧸Ideal.span {a},F (f x):=tsum_congr hpoint
    _=(Nat.card f.toAddMonoidHom.ker:ℂ)*∑'x,F x:=
      finite_tsum_comp_addHom f.toAddMonoidHom (ramifiedReduction_surjective u n hn) F
    _=_:=by rw [ramifiedReduction_kernel_card u n hn];rfl

end

open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CompletedGauss
local notation "Eis" => ActualEisensteinCubic.O

def ramifiedLinearChar (u:Eisˣ) (n:ℕ):AddChar Eis ℂ where
  toFun x:=eisEmbedding (symbol (u.val*lambda^n) (1+3*x))
  map_zero_eq_one':=by simp
  map_add_eq_mul':=by
    intro x y
    have hp (z:Eis):(3:Eis)∣1+3*z-1:=⟨z,by ring⟩
    have hprod:(3:Eis)∣(1+3*x)*(1+3*y)-1:=⟨x+y+3*x*y,by ring⟩
    rw [ramified_symbol_congr_mod_nine u n (1+3*(x+y))
      ((1+3*x)*(1+3*y)) (hp _) hprod ⟨-x*y,by ring⟩,
      symbol_mul_denominator,map_mul]

lemma ramifiedLinearChar_period (u:Eisˣ) (n:ℕ) (x:Eis)
    (hx:x∈Ideal.span {(3:Eis)}) : ramifiedLinearChar u n x=1 := by
  obtain ⟨w,rfl⟩:=Ideal.mem_span_singleton.mp hx
  change eisEmbedding (symbol (u.val*lambda^n) (1+3*(3*w)))=1
  rw [ramified_symbol_congr_mod_nine u n _ 1 ⟨3*w,by ring⟩ (by simp) ⟨w,by ring⟩]
  simp

def ramifiedQuotientChar (u:Eisˣ) (n:ℕ):AddChar (Eis⧸Ideal.span {(3:Eis)}) ℂ:=
  IdealGaussCRT.quotientAddChar _ (ramifiedLinearChar u n) (ramifiedLinearChar_period u n)

lemma ramifiedQuotientChar_rep (u:Eisˣ) (n:ℕ) (x:Eis⧸Ideal.span {(3:Eis)}) :
    ramifiedQuotientChar u n x=
      eisEmbedding (symbol (u.val*lambda^n)
        (1+3*GaussianShiftedPartition.representative 3 x)) := by
  conv_lhs => rw [←GaussianShiftedPartition.representative_spec 3 x]
  rfl

def ramifiedFrequencyChar (k:Eis) (u:Eisˣ) (n:ℕ):
    AddChar (Eis⧸Ideal.span {(3:Eis)}) ℂ:=
  ramifiedQuotientChar u n *
    (eisTraceModChar ShortDraftTrace.breveE ConcreteBreveE.breveE_period_coordinates
      3 (by norm_num)).mulShift (Ideal.Quotient.mk _ k)

lemma ramifiedFrequencyChar_rep (k:Eis) (u:Eisˣ) (n:ℕ)
    (x:Eis⧸Ideal.span {(3:Eis)}) :
    ramifiedFrequencyChar k u n x=
      eisEmbedding (symbol (u.val*lambda^n)
        (1+3*GaussianShiftedPartition.representative 3 x))*
      residueAdditive k 3 (3*GaussianShiftedPartition.representative 3 x) := by
  rw [ramifiedFrequencyChar,AddChar.mul_apply,ramifiedQuotientChar_rep]
  congr 1
  conv_lhs => rw [←GaussianShiftedPartition.representative_spec 3 x]
  simp only [AddChar.mulShift_apply,←map_mul,eisTraceModChar,IdealGaussCRT.traceModChar_mk]
  unfold residueAdditive cuspFrequency
  simp only [map_mul,map_ofNat]
  congr 1
  field_simp

theorem ramifiedNineSum_eq_character_test (k:Eis) (u:Eisˣ) (n:ℕ) :
    ramifiedNineSum k u n=
      if ramifiedFrequencyChar k u n=1 then 9*residueAdditive k 3 1 else 0 := by
  let:Finite (Eis⧸Ideal.span {(3:Eis)}):=finite_quotient_span (by norm_num)
  let:Fintype (Eis⧸Ideal.span {(3:Eis)}):=Fintype.ofFinite _
  have hcard:(Fintype.card (Eis⧸Ideal.span {(3:Eis)}):ℂ)=9:=by
    have hh:=three_absNorm
    change Nat.card (Eis⧸Ideal.span {(3:Eis)})=9 at hh
    exact_mod_cast (show Fintype.card (Eis⧸Ideal.span {(3:Eis)})=9 by
      simpa only [Nat.card_eq_fintype_card] using hh)
  have he:ramifiedNineSum k u n=residueAdditive k 3 1*
      ∑'x:Eis⧸Ideal.span {(3:Eis)},ramifiedFrequencyChar k u n x:=by
    rw [ramifiedNineSum,←tsum_mul_left]
    apply tsum_congr
    intro x
    rw [ramifiedFrequencyChar_rep,residueAdditive_add]
    ring
  rw [he,tsum_fintype]
  split_ifs with hchar
  · rw [AddChar.sum_eq_card_of_eq_one hchar,hcard]
    ring
  · rw [AddChar.sum_eq_zero_of_ne_one hchar,mul_zero]

theorem ramified_arithmetic_character_test (h k:Eis) (u:Eisˣ) (n:ℕ) (hn:2≤n)
    (hk:3*h=(u.val*lambda^n)*k) :
    arithmeticResidueSum h (u.val*lambda^n)=
      if ramifiedFrequencyChar k u n=1 then ((3^n:ℕ):ℂ)*residueAdditive k 3 1 else 0 := by
  rw [ramified_arithmetic_nine_sum h k u n hn hk,ramifiedNineSum_eq_character_test]
  have hp:(3:ℕ)^n=3^(n-2)*9:=by
    have hn':n=(n-2)+2:=by omega
    conv_lhs => rw [hn']
    rw [pow_add]
    norm_num
  split_ifs
  · rw [hp,Nat.cast_mul]
    norm_num
    ring
  · ring

end CubicEisenstein

namespace CubicKubota

open scoped Classical MatrixGroups

section
open ActualEisensteinCubic
open CubicEisenstein

def levelThreeInTwo : Subgroup levelTwo := levelThree.comap levelTwo.subtype

instance levelThreeInTwo_normal : levelThreeInTwo.Normal := by
  constructor
  intro n hn g
  exact (levelThreeConjugate (g:SL(2,ActualEisensteinCubic.O)) ⟨(n:SL(2,ActualEisensteinCubic.O)),hn⟩).property

instance levelThreeInTwo_finiteIndex : levelThreeInTwo.FiniteIndex := by
  let : levelThree.FiniteIndex := levelThree_finiteIndex
  change (levelThree.comap levelTwo.subtype).FiniteIndex
  infer_instance

def rationalLift : SL(2,ℤ)→*levelTwo where
  toFun r := ⟨rationalEmbedding r,rational_mem_levelTwo r⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' _ _ := Subtype.ext (map_mul _ _ _)

def rationalQuotient : SL(2,ℤ)→*(levelTwo ⧸ levelThreeInTwo) :=
  (QuotientGroup.mk' levelThreeInTwo).comp rationalLift

theorem rationalQuotient_surjective : Function.Surjective rationalQuotient := by
  intro q
  obtain ⟨g,rfl⟩ := QuotientGroup.mk'_surjective levelThreeInTwo q
  obtain ⟨n,r,hr⟩ := g.property
  refine ⟨r,?_⟩
  let n2 : levelTwo := ⟨(n:SL(2,ActualEisensteinCubic.O)),levelThree_le_levelTwo n.property⟩
  have he : g=n2*rationalLift r := Subtype.ext hr.symm
  have hn : QuotientGroup.mk' levelThreeInTwo n2=1 :=
    (QuotientGroup.eq_one_iff n2).mpr n.property
  change QuotientGroup.mk' levelThreeInTwo (rationalLift r)=_
  rw [he,map_mul,hn,one_mul]

def rationalCongruenceThree : Subgroup (SL(2,ℤ)) := rationalQuotient.ker

instance rationalCongruenceThree_normal : rationalCongruenceThree.Normal := by
  unfold rationalCongruenceThree
  infer_instance

theorem mem_rationalCongruenceThree (r : SL(2,ℤ)) :
    r∈rationalCongruenceThree ↔ rationalEmbedding r∈levelThree := by
  change QuotientGroup.mk' levelThreeInTwo (rationalLift r)=1 ↔ _
  exact QuotientGroup.eq_one_iff _

def rationalQuotientEquiv : (SL(2,ℤ) ⧸ rationalCongruenceThree) ≃*
    (levelTwo ⧸ levelThreeInTwo) :=
  QuotientGroup.quotientKerEquivOfSurjective rationalQuotient rationalQuotient_surjective

instance rationalCongruenceThree_finiteIndex : rationalCongruenceThree.FiniteIndex := by
  have he : rationalCongruenceThree=levelThree.comap rationalEmbedding := by
    ext r
    exact mem_rationalCongruenceThree r
  rw [he]
  let : levelThree.FiniteIndex := levelThree_finiteIndex
  infer_instance

theorem finite_rational_representatives : ∃R : Finset (SL(2,ℤ)),
    ∀g : levelTwo,∃r∈R,(g:SL(2,ActualEisensteinCubic.O))*(rationalEmbedding r)⁻¹∈levelThree := by
  let : Fintype (levelTwo ⧸ levelThreeInTwo) := Fintype.ofFinite _
  let sectionMap : (levelTwo ⧸ levelThreeInTwo)→SL(2,ℤ) :=
    fun q => (rationalQuotient_surjective q).choose
  have hsection : ∀q,rationalQuotient (sectionMap q)=q :=
    fun q => (rationalQuotient_surjective q).choose_spec
  refine ⟨Finset.univ.image sectionMap,fun g => ?_⟩
  let q := QuotientGroup.mk' levelThreeInTwo g
  refine ⟨sectionMap q,Finset.mem_image.mpr ⟨q,Finset.mem_univ _,rfl⟩,?_⟩
  have he : QuotientGroup.mk' levelThreeInTwo (g*(rationalLift (sectionMap q))⁻¹)=1 := by
    rw [map_mul,map_inv]
    change q*(rationalQuotient (sectionMap q))⁻¹=1
    rw [hsection,mul_inv_cancel]
  exact (QuotientGroup.eq_one_iff (N:=levelThreeInTwo)
    (g*(rationalLift (sectionMap q))⁻¹)).mp he

end

open ActualEisensteinCubic

lemma three_dvd_intCast_iff (a : ℤ) : (3:ActualEisensteinCubic.O)∣(a:ActualEisensteinCubic.O) ↔ (3:ℤ)∣a := by
  constructor
  · rintro ⟨x,hx⟩
    obtain ⟨u,v,huv⟩ := ActualEisensteinCoordinates.exists_coordinates x
    have he : ActualEisensteinCoordinates.eval a 0=
        ActualEisensteinCoordinates.eval (3*u) (3*v) := by
      dsimp [ActualEisensteinCoordinates.eval]
      rw [hx,huv]
      push_cast
      ring
    exact ⟨u,(ActualEisensteinCoordinates.unique_coordinates he).1⟩
  · rintro ⟨b,hb⟩
    refine ⟨(b:ActualEisensteinCubic.O),?_⟩
    simpa only [Int.cast_mul,Int.cast_ofNat] using congrArg (fun z : ℤ => (z:ActualEisensteinCubic.O)) hb

lemma mem_levelThree_iff_entries (g : SL(2,ActualEisensteinCubic.O)) : g∈levelThree ↔
    ∀i j,(3:ActualEisensteinCubic.O)∣g i j-(if i=j then 1 else 0) := by
  constructor
  · intro hg i j
    exact levelThree_entry ⟨g,hg⟩ i j
  · intro h
    change Matrix.SpecialLinearGroup.map (n:=Fin 2)
      (Ideal.Quotient.mk (Ideal.span {(3:ActualEisensteinCubic.O)})) g=1
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    change Ideal.Quotient.mk (Ideal.span {(3:ActualEisensteinCubic.O)}) (g i j)=
      (1:Matrix (Fin 2) (Fin 2) (ActualEisensteinCubic.O ⧸ Ideal.span {(3:ActualEisensteinCubic.O)})) i j
    rw [Matrix.one_apply]
    have he := (Ideal.Quotient.mk_eq_mk_iff_sub_mem (g i j) (if i=j then 1 else 0)).mpr
      (Ideal.mem_span_singleton.mpr (h i j))
    simpa only [apply_ite,map_one,map_zero] using he

def rationalReductionThree : SL(2,ℤ)→*SL(2,ZMod 3) :=
  Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod 3))

lemma rationalReductionThree_eq_one_iff (g : SL(2,ℤ)) :
    rationalReductionThree g=1 ↔ g∈rationalCongruenceThree := by
  rw [mem_rationalCongruenceThree,mem_levelThree_iff_entries]
  constructor
  · intro hg i j
    have he := congrArg (fun h : SL(2,ZMod 3) => h i j) hg
    change (g i j:ZMod 3)=(1:Matrix (Fin 2) (Fin 2) (ZMod 3)) i j at he
    rw [Matrix.one_apply] at he
    have hd : (3:ℤ)∣g i j-(if i=j then 1 else 0) := by
      apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mp
      simpa only [Int.cast_sub,Int.cast_ite,Int.cast_one,Int.cast_zero] using sub_eq_zero.mpr he
    have hO := (three_dvd_intCast_iff (g i j-(if i=j then 1 else 0))).mpr hd
    simpa only [rationalEmbedding,Matrix.SpecialLinearGroup.map_apply_coe,
      RingHom.mapMatrix_apply,Matrix.map_apply,Int.coe_castRingHom,
      Int.cast_sub,Int.cast_ite,Int.cast_one,Int.cast_zero] using hO
  · intro hg
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    change (g i j:ZMod 3)=(1:Matrix (Fin 2) (Fin 2) (ZMod 3)) i j
    rw [Matrix.one_apply]
    apply sub_eq_zero.mp
    have hd : (3:ℤ)∣g i j-(if i=j then 1 else 0) := by
      apply (three_dvd_intCast_iff _).mp
      simpa only [rationalEmbedding,Matrix.SpecialLinearGroup.map_apply_coe,
      RingHom.mapMatrix_apply,Matrix.map_apply,Int.coe_castRingHom,
        Int.cast_sub,Int.cast_ite,Int.cast_one,Int.cast_zero] using hg i j
    have hz := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mpr hd
    simpa only [Int.cast_sub,Int.cast_ite,Int.cast_one,Int.cast_zero] using hz

abbrev RationalBruhatIndex := Fin 2 × (Fin 3 ⊕ (Fin 3 × Fin 3))

def rationalBruhatRep (i : RationalBruhatIndex) : SL(2,ℤ) :=
  ModularGroup.S^(2*i.1.val) * match i.2 with
    | Sum.inl a => ModularGroup.T^a.val
    | Sum.inr ab => ModularGroup.T^ab.1.val*ModularGroup.S*ModularGroup.T^ab.2.val

lemma rationalBruhat_complete : ∀g : SL(2,ZMod 3),
    ∃i : RationalBruhatIndex,rationalReductionThree (rationalBruhatRep i)=g := by
  decide +kernel

lemma rationalReductionThree_surjective : Function.Surjective rationalReductionThree := by
  intro g
  obtain ⟨i,hi⟩ := rationalBruhat_complete g
  exact ⟨rationalBruhatRep i,hi⟩

lemma rationalBruhat_injective : Function.Injective
    (fun i : RationalBruhatIndex => rationalReductionThree (rationalBruhatRep i)) := by
  decide +kernel

def rationalBruhatEquiv : RationalBruhatIndex ≃ SL(2,ZMod 3) :=
  Equiv.ofBijective (fun i => rationalReductionThree (rationalBruhatRep i))
    ⟨rationalBruhat_injective,rationalBruhat_complete⟩

lemma card_SLThree : Fintype.card (SL(2,ZMod 3))=24 := by
  rw [←Fintype.card_congr rationalBruhatEquiv]
  decide

lemma rationalCongruenceThree_eq_ker : rationalCongruenceThree=rationalReductionThree.ker := by
  ext g
  exact (rationalReductionThree_eq_one_iff g).symm

def rationalCongruenceEquivSLThree : (SL(2,ℤ) ⧸ rationalCongruenceThree) ≃* SL(2,ZMod 3) :=
  (QuotientGroup.quotientMulEquivOfEq rationalCongruenceThree_eq_ker).trans
    (QuotientGroup.quotientKerEquivOfSurjective rationalReductionThree rationalReductionThree_surjective)

def sourceQuotientEquivSLThree : (levelTwo ⧸ levelThreeInTwo) ≃* SL(2,ZMod 3) :=
  rationalQuotientEquiv.symm.trans rationalCongruenceEquivSLThree

lemma sourceQuotient_card : Nat.card (levelTwo ⧸ levelThreeInTwo)=24 := by
  rw [Nat.card_congr sourceQuotientEquivSLThree.toEquiv,Nat.card_eq_fintype_card,card_SLThree]

lemma levelThreeInTwo_index : levelThreeInTwo.index=24 := sourceQuotient_card

theorem twentyFour_rational_representatives (g : levelTwo) :
    ∃i : RationalBruhatIndex,
      (g:SL(2,ActualEisensteinCubic.O))*(rationalEmbedding (rationalBruhatRep i))⁻¹∈levelThree := by
  obtain ⟨r,hr⟩ := rationalQuotient_surjective (QuotientGroup.mk' levelThreeInTwo g)
  obtain ⟨i,hi⟩ := rationalBruhat_complete (rationalReductionThree r)
  refine ⟨i,?_⟩
  have hred : rationalReductionThree (r*(rationalBruhatRep i)⁻¹)=1 := by
    rw [map_mul,map_inv,hi,mul_inv_cancel]
  have hker := (rationalReductionThree_eq_one_iff _).mp hred
  have hquot : rationalQuotient r=rationalQuotient (rationalBruhatRep i) := by
    have hz : rationalQuotient (r*(rationalBruhatRep i)⁻¹)=1 := hker
    rw [map_mul,map_inv,mul_inv_eq_one] at hz
    exact hz
  have he : QuotientGroup.mk' levelThreeInTwo
      (g*(rationalLift (rationalBruhatRep i))⁻¹)=1 := by
    rw [map_mul,map_inv,←hr,hquot]
    exact mul_inv_cancel _
  exact (QuotientGroup.eq_one_iff (N:=levelThreeInTwo)
    (g*(rationalLift (rationalBruhatRep i))⁻¹)).mp he

end CubicKubota

open scoped BigOperators Classical MatrixGroups
namespace CubicKubota
open ActualEisensteinCubic
open CubicEisenstein

lemma rationalQuotient_eq_iff_reduction (r s : SL(2,ℤ)) :
    rationalQuotient r=rationalQuotient s ↔
      rationalReductionThree r=rationalReductionThree s := by
  have hleft : rationalQuotient r=rationalQuotient s ↔ r*s⁻¹∈rationalCongruenceThree := by
    change _ ↔ rationalQuotient (r*s⁻¹)=1
    rw [map_mul,map_inv,mul_inv_eq_one]
  rw [hleft,←rationalReductionThree_eq_one_iff,map_mul,map_inv,mul_inv_eq_one]

lemma levelTwoComplexCharacter_rationalLift (r : SL(2,ℤ)) :
    levelTwoComplexCharacter (rationalLift r)=1 := levelTwoComplexCharacter_rational r

def rationalCosetEquiv : RationalBruhatIndex ≃ (levelTwo ⧸ levelThreeInTwo) :=
  Equiv.ofBijective (fun i => rationalQuotient (rationalBruhatRep i)) ⟨by
    intro i j h
    exact rationalBruhat_injective ((rationalQuotient_eq_iff_reduction _ _).mp h),by
    intro q
    obtain ⟨r,hr⟩ := rationalQuotient_surjective q
    obtain ⟨i,hi⟩ := rationalBruhat_complete (rationalReductionThree r)
    exact ⟨i,((rationalQuotient_eq_iff_reduction _ _).mpr hi).trans hr⟩⟩

instance sourceQuotientFintype : Fintype (levelTwo ⧸ levelThreeInTwo) := Fintype.ofFinite _

def sourceRationalSection (q : levelTwo ⧸ levelThreeInTwo) : SL(2,ℤ) :=
  rationalBruhatRep (rationalCosetEquiv.symm q)

lemma sourceRationalSection_spec (q : levelTwo ⧸ levelThreeInTwo) :
    rationalQuotient (sourceRationalSection q)=q := rationalCosetEquiv.apply_symm_apply q

def sourceProjection (f : HyperbolicSpace→ℂ) (w : HyperbolicSpace) : ℂ :=
  (24:ℂ)⁻¹ * ∑q : levelTwo ⧸ levelThreeInTwo,
    f (integralComplexMatrix (rationalEmbedding (sourceRationalSection q)) • w)

lemma sourceProjection_eq_twentyFour (f : HyperbolicSpace→ℂ) (w : HyperbolicSpace) :
    sourceProjection f w=(24:ℂ)⁻¹ * ∑i : RationalBruhatIndex,
      f (integralComplexMatrix (rationalEmbedding (rationalBruhatRep i)) • w) := by
  unfold sourceProjection
  congr 1
  rw [←rationalCosetEquiv.sum_comp]
  simp only [sourceRationalSection,Equiv.symm_apply_apply]

lemma sourceSection_translate (f : HyperbolicSpace→ℂ)
    (hf : ∀n : levelThree,∀w,f (complexMatrix n • w)=complexCharacter n*f w)
    (q : levelTwo ⧸ levelThreeInTwo) (g : levelTwo) (w : HyperbolicSpace) :
    f (integralComplexMatrix (rationalEmbedding (sourceRationalSection q)) •
      (integralComplexMatrix (g:SL(2,ActualEisensteinCubic.O)) • w)) =
    levelTwoComplexCharacter g *
      f (integralComplexMatrix (rationalEmbedding (sourceRationalSection
        (q*QuotientGroup.mk' levelThreeInTwo g))) • w) := by
  let r := sourceRationalSection q
  let s := sourceRationalSection (q*QuotientGroup.mk' levelThreeInTwo g)
  let n2 : levelTwo := rationalLift r*g*(rationalLift s)⁻¹
  have hn2 : n2∈levelThreeInTwo := by
    apply (QuotientGroup.eq_one_iff (N:=levelThreeInTwo) n2).mp
    change QuotientGroup.mk' levelThreeInTwo (rationalLift r*g*(rationalLift s)⁻¹)=1
    rw [map_mul,map_mul,map_inv]
    change rationalQuotient r * QuotientGroup.mk' levelThreeInTwo g *
      (rationalQuotient s)⁻¹=1
    rw [sourceRationalSection_spec,sourceRationalSection_spec,mul_inv_cancel]
  let n : levelThree := ⟨(n2:SL(2,ActualEisensteinCubic.O)),hn2⟩
  have hc : complexCharacter n=levelTwoComplexCharacter g := by
    rw [←levelTwoComplexCharacter_restrict n]
    change levelTwoComplexCharacter (rationalLift r*g*(rationalLift s)⁻¹)=_
    rw [map_mul,map_mul,←map_inv rationalLift]
    change levelTwoComplexCharacter (rationalLift r)*levelTwoComplexCharacter g*
      levelTwoComplexCharacter (rationalLift s⁻¹)=_
    rw [levelTwoComplexCharacter_rationalLift,levelTwoComplexCharacter_rationalLift,one_mul,mul_one]
  have he : rationalEmbedding r*(g:SL(2,ActualEisensteinCubic.O))=(n:SL(2,ActualEisensteinCubic.O))*rationalEmbedding s := by
    change _=(rationalEmbedding r*(g:SL(2,ActualEisensteinCubic.O))*(rationalEmbedding s)⁻¹)*rationalEmbedding s
    group
  change f (integralComplexMatrix (rationalEmbedding r) •
    (integralComplexMatrix (g:SL(2,ActualEisensteinCubic.O)) • w))=
    levelTwoComplexCharacter g*f (integralComplexMatrix (rationalEmbedding s) • w)
  rw [←mul_smul,←map_mul,he,map_mul,integralComplexMatrix_levelThree,mul_smul,hf,hc]

theorem sourceProjection_automorphy (f : HyperbolicSpace→ℂ)
    (hf : ∀n : levelThree,∀w,f (complexMatrix n • w)=complexCharacter n*f w)
    (g : levelTwo) (w : HyperbolicSpace) :
    sourceProjection f (integralComplexMatrix (g:SL(2,ActualEisensteinCubic.O)) • w)=
      levelTwoComplexCharacter g * sourceProjection f w := by
  unfold sourceProjection
  simp_rw [sourceSection_translate f hf]
  rw [←Finset.mul_sum]
  rw [Function.Bijective.sum_comp
    (Group.mulRight_bijective (QuotientGroup.mk' levelThreeInTwo g))
    (fun q => f (integralComplexMatrix (rationalEmbedding (sourceRationalSection q)) • w))]
  ring

theorem sourceProjection_fixed (f : HyperbolicSpace→ℂ)
    (hf : ∀g : levelTwo,∀w,f (integralComplexMatrix (g:SL(2,ActualEisensteinCubic.O)) • w)=
      levelTwoComplexCharacter g*f w) (w : HyperbolicSpace) : sourceProjection f w=f w := by
  unfold sourceProjection
  have he : ∀q : levelTwo ⧸ levelThreeInTwo,
      f (integralComplexMatrix (rationalEmbedding (sourceRationalSection q)) • w)=f w := by
    intro q
    have hh := hf (rationalLift (sourceRationalSection q)) w
    rw [levelTwoComplexCharacter_rationalLift,one_mul] at hh
    exact hh
  simp only [he,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  have hc : Fintype.card (levelTwo ⧸ levelThreeInTwo)=24 := by
    simpa only [Nat.card_eq_fintype_card] using sourceQuotient_card
  rw [hc]
  push_cast
  ring

lemma sourceProjection_idempotent (f : HyperbolicSpace→ℂ)
    (hf : ∀n : levelThree,∀w,f (complexMatrix n • w)=complexCharacter n*f w) :
    sourceProjection (sourceProjection f)=sourceProjection f := by
  funext w
  exact sourceProjection_fixed _ (sourceProjection_automorphy f hf) w

def sourceEisenstein (s : ℂ) : HyperbolicSpace→ℂ := sourceProjection (hyperbolicEisenstein s)

theorem sourceEisenstein_automorphy (s : ℂ) (hs : 2<s.re) (g : levelTwo) (w : HyperbolicSpace) :
    sourceEisenstein s (integralComplexMatrix (g:SL(2,ActualEisensteinCubic.O)) • w)=
      levelTwoComplexCharacter g*sourceEisenstein s w :=
  sourceProjection_automorphy _ (fun n w => hyperbolicEisenstein_automorphy n s hs w) g w

end CubicKubota

end

end OAI
