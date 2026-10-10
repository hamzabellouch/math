import OAI.NumberTheory.DirichletL.Cusp.ResiduesModThree

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

section

open scoped Classical MatrixGroups
namespace CubicJacobiGlobal
open ActualEisensteinCubic CubicRamified
local notation "Eis" => ActualEisensteinCubic.O

lemma integer_congruence_primary_cases (c : Eis) (r : ℤ) (h : (3:Eis)∣c-(r:Eis)) :
    (3:Eis)∣c ∨ lambda^2∣c-1 ∨ lambda^2∣(-c)-1 := by
  have hr : (3:ℤ)∣r ∨ (3:ℤ)∣r-1 ∨ (3:ℤ)∣r+1 := by omega
  rcases hr with hr|hr|hr
  · left
    obtain ⟨t,ht⟩:=hr
    have hn:(3:Eis)∣(r:Eis):=⟨(t:Eis),by exact_mod_cast ht⟩
    simpa using dvd_add h hn
  · right;left
    obtain ⟨t,ht⟩:=hr
    have hn:(3:Eis)∣(r:Eis)-1:=⟨(t:Eis),by exact_mod_cast ht⟩
    exact lambda_sq_dvd_three.trans (by simpa using dvd_add h hn)
  · right;right
    obtain ⟨t,ht⟩:=hr
    have hn:(3:Eis)∣(r:Eis)+1:=⟨(t:Eis),by exact_mod_cast ht⟩
    apply lambda_sq_dvd_three.trans
    convert dvd_neg.mpr (dvd_add h hn) using 1 ; ring

lemma symbol_three_shift_primary (c a t:Eis) (hc:lambda^2∣c-1) (ha:lambda^2∣a-1) :
    symbol c (a+3*t*c)=symbol c a := by
  have hs:=primary_add_multiple_three a c t ha
  calc
    _=symbol (a+3*t*c) c:=symbol_reciprocity _ _ (primary_ne_zero _ hc) (primary_ne_zero _ hs) hc hs
    _=symbol a c:=symbol_congr ⟨3*t,by ring⟩
    _=symbol c a:=(symbol_reciprocity _ _ (primary_ne_zero _ hc) (primary_ne_zero _ ha) hc ha).symm

lemma symbol_three_shift_integer (c a t:Eis) (r:ℤ)
    (ha:lambda^2∣a-1) (hc:(3:Eis)∣c-(r:Eis)) :
    symbol c (a+3*t*c)=symbol c a := by
  rcases integer_congruence_primary_cases c r hc with h|h|h
  · exact symbol_three_shift c a t ha h
  · exact symbol_three_shift_primary c a t h ha
  · have hh:=symbol_three_shift_primary (-c) a (-t) h ha
    have he:a+3*(-t)*(-c)=a+3*t*c:=by ring
    rw [he,symbol_neg_numerator _ _ (primary_add_multiple_three a c t ha),
      symbol_neg_numerator _ _ ha] at hh
    exact hh

end CubicJacobiGlobal
namespace CubicKubota
open ActualEisensteinCubic ConcreteTraceCRT CubicEisenstein CubicJacobiGlobal CubicRamified
local notation "Eis" => ActualEisensteinCubic.O

lemma levelTwo_cube_phase_balance (A N:levelTwo) (p q:Eis) (j:ℕ)
    (hp:lambda^2∣p-1)
    (hA:lambda^2∣((A:SL(2,Eis)) 0 0)-1)
    (hN:lambda^2∣((N:SL(2,Eis)) 0 0)-1)
    (hx:(A:SL(2,Eis)) 0 0+3*q*(A:SL(2,Eis)) 1 0=p^j*(N:SL(2,Eis)) 0 0)
    (hc:(N:SL(2,Eis)) 1 0=p^(3-j)*(A:SL(2,Eis)) 1 0) :
    levelTwoComplexCharacter N *
        eisEmbedding (symbol ((A:SL(2,Eis)) 1 0) p)^j =
      levelTwoComplexCharacter A *
        eisEmbedding (symbol ((N:SL(2,Eis)) 0 0) p)^(3-j) := by
  have hs : symbol ((A:SL(2,Eis)) 1 0) ((A:SL(2,Eis)) 0 0) =
      symbol ((A:SL(2,Eis)) 1 0) p ^ j *
        symbol ((A:SL(2,Eis)) 1 0) ((N:SL(2,Eis)) 0 0) := by
    rw [←symbol_three_shift_integer _ _ q (levelTwoRight A 1 0) hA (levelTwo_entry_integer A 1 0),
      hx,symbol_mul_denominator,cubicSymbol_pow_denominator]
  rw [levelTwoComplexCharacter_primary N hN,levelTwoComplexCharacter_primary A hA,hc,
    symbol_mul_numerator _ _ _ hN,symbol_pow_numerator _ _ hN,
    symbol_reciprocity p ((N:SL(2,Eis)) 0 0) (primary_ne_zero _ hp) (primary_ne_zero _ hN) hp hN,
    hs,map_mul,map_pow,map_mul,map_pow]
  ring

lemma levelTwo_comparison_character (A N:levelTwo)
    (hNA:(N:SL(2,Eis))*(A:SL(2,Eis))⁻¹∈levelThree) :
    complexCharacter ⟨(N:SL(2,Eis))*(A:SL(2,Eis))⁻¹,hNA⟩ *
        levelTwoComplexCharacter A = levelTwoComplexCharacter N := by
  rw [←levelTwoComplexCharacter_restrict ⟨(N:SL(2,Eis))*(A:SL(2,Eis))⁻¹,hNA⟩]
  change levelTwoComplexCharacter (N*A⁻¹)*levelTwoComplexCharacter A=levelTwoComplexCharacter N
  rw [map_mul,map_inv,mul_assoc]
  have hA:levelTwoComplexCharacter A≠0:=by
    intro he
    have hh:=levelTwoComplexCharacter_cube A
    rw [he] at hh
    norm_num at hh
  rw [inv_mul_cancel₀ hA,mul_one]

lemma levelTwo_cube_comparison_phase (A N:levelTwo) (p q:Eis) (j:ℕ) (hj:j≤3)
    (hp:lambda^2∣p-1)
    (hA:lambda^2∣((A:SL(2,Eis)) 0 0)-1)
    (hN:lambda^2∣((N:SL(2,Eis)) 0 0)-1)
    (hx:(A:SL(2,Eis)) 0 0+3*q*(A:SL(2,Eis)) 1 0=p^j*(N:SL(2,Eis)) 0 0)
    (hc:(N:SL(2,Eis)) 1 0=p^(3-j)*(A:SL(2,Eis)) 1 0)
    (hC:IsCoprime ((A:SL(2,Eis)) 1 0) p)
    (hNA:(N:SL(2,Eis))*(A:SL(2,Eis))⁻¹∈levelThree) :
    complexCharacter ⟨(N:SL(2,Eis))*(A:SL(2,Eis))⁻¹,hNA⟩ =
      eisEmbedding (symbol (((N:SL(2,Eis)) 0 0)*((A:SL(2,Eis)) 1 0)) p)^(3-j) := by
  let a:=eisEmbedding (symbol ((A:SL(2,Eis)) 1 0) p)
  let b:=eisEmbedding (symbol ((N:SL(2,Eis)) 0 0) p)
  have ha3:a^3=1:=by
    dsimp [a]
    rw [←map_pow,symbol_cube_of_isCoprime _ _ hp hC,map_one]
  have hpow:a^j*a^(3-j)=1:=by rw [←pow_add,Nat.add_sub_of_le hj,ha3]
  have hbal:=levelTwo_cube_phase_balance A N p q j hp hA hN hx hc
  change levelTwoComplexCharacter N*a^j=levelTwoComplexCharacter A*b^(3-j) at hbal
  have he:levelTwoComplexCharacter N=levelTwoComplexCharacter A*(b*a)^(3-j):=by
    calc
      _=levelTwoComplexCharacter N*(a^j*a^(3-j)):=by rw [hpow,mul_one]
      _=(levelTwoComplexCharacter N*a^j)*a^(3-j):=(mul_assoc _ _ _).symm
      _=(levelTwoComplexCharacter A*b^(3-j))*a^(3-j):=by rw [hbal]
      _=_:=by rw [mul_pow];ring
  have hcomp:=levelTwo_comparison_character A N hNA
  have hbase:levelTwoComplexCharacter A≠0:=by
    intro he
    have hh:=levelTwoComplexCharacter_cube A
    rw [he] at hh
    norm_num at hh
  rw [symbol_mul_numerator _ _ _ hp,map_mul]
  change complexCharacter ⟨(N:SL(2,Eis))*(A:SL(2,Eis))⁻¹,hNA⟩=(b*a)^(3-j)
  apply mul_right_cancel₀ hbase
  rw [hcomp,he]
  ring

end CubicKubota
end

open scoped BigOperators Classical

namespace CubicEisenstein

section
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CubicRamified
local notation "Eis" => ActualEisensteinCubic.O

lemma ramified_cubicExp_nat_mul (n : ℕ) (t : ℤ) :
    cubicExp ((n:ℤ)*t)=cubicExp t^n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.cast_add,Nat.cast_one,add_mul,one_mul,cubicExp_add,ih,pow_succ]

lemma ramified_trace_symbol (a : Eis) (ha : lambda^2∣a-1) :
    symbol ramifiedTraceLambda a=linearRay 0 (-1) a := by
  have h := symbol_traceLambda_eq_linearRay a ha
  change symbol ramifiedTraceLambda a=linearRay 0 (-1) a at h
  exact h

lemma ramifiedSymbol_primaryCoord (j n : ℕ) (A B : ℤ) :
    symbol (omega^j*ramifiedTraceLambda^n) (primaryCoord A B)=
      cubicExp ((j:ℤ)*(2*A-B)-(n:ℤ)*B) := by
  rw [symbol_mul_numerator _ _ _ (primaryCoord_primary _ _),
    symbol_pow_numerator _ _ (primaryCoord_primary _ _) j,
    symbol_pow_numerator _ _ (primaryCoord_primary _ _) n,
    symbol_omega_eq_linearRay _ (primaryCoord_primary _ _),
    ramified_trace_symbol _ (primaryCoord_primary _ _),linearRay_primaryCoord,linearRay_primaryCoord,
    ←ramified_cubicExp_nat_mul,←ramified_cubicExp_nat_mul,←cubicExp_add]
  congr 1
  ring

def ramifiedAffineParameter (j n : ℕ) : Eis := (j:Eis)*ramifiedTraceLambda-(n:Eis)

lemma ramifiedAffineParameter_coords (j n : ℕ) (C D : ℤ) :
    (ActualEisensteinCoordinates.coords
      (ramifiedAffineParameter j n*ActualEisensteinCoordinates.eval C D)).2=
      (j:ℤ)*(2*C-D)-(n:ℤ)*D := by
  have hk : ramifiedAffineParameter j n=ActualEisensteinCoordinates.eval ((j:ℤ)-(n:ℤ)) (2*(j:ℤ)) := by
    change (j:Eis)*(1+2*omega)-(n:Eis)=(((j:ℤ)-(n:ℤ):ℤ):Eis)+((2*(j:ℤ):ℤ):Eis)*omega
    push_cast
    ring
  rw [hk,ActualEisensteinCoordinates.eval_mul,ShortDraftLatticeCount.coords_eval]
  ring

theorem ramified_symbol_primary_shift (j n : ℕ) (a x : Eis) (ha : lambda^2∣a-1) :
    eisEmbedding (symbol (omega^j*ramifiedTraceLambda^n) (a+3*x))=
      eisEmbedding (symbol (omega^j*ramifiedTraceLambda^n) a)*
        ShortDraftTrace.breveE (eisEmbedding (ramifiedAffineParameter j n*x)/eisLam/3) := by
  obtain ⟨A,B,rfl⟩ := exists_primaryCoord a ha
  let C := (ActualEisensteinCoordinates.coords x).1
  let D := (ActualEisensteinCoordinates.coords x).2
  have hx : x=ActualEisensteinCoordinates.eval C D := (ActualEisensteinCoordinates.eval_coords x).symm
  have hsum : primaryCoord A B+3*x=primaryCoord (A+C) (B+D) := by
    rw [hx,primaryCoord_eq,primaryCoord_eq]
    change 1+3*(A:Eis)+3*(B:Eis)*omega+3*((C:Eis)+(D:Eis)*omega)=_
    push_cast
    ring
  rw [hsum,ramifiedSymbol_primaryCoord,ramifiedSymbol_primaryCoord]
  have ht := breveE_real_trace_of_O (3:ℝ) (ramifiedAffineParameter j n*x)
  norm_num only [Complex.ofReal_ofNat] at ht
  rw [ht,hx,ramifiedAffineParameter_coords,←embedding_cubicExp,←map_mul,←cubicExp_add]
  apply congrArg eisEmbedding
  apply congrArg cubicExp
  ring

lemma ramified_symbol_primary_shift_signed (j n : ℕ) (r a x : Eis)
    (hr : r=omega^j*ramifiedTraceLambda^n ∨ r=-(omega^j*ramifiedTraceLambda^n))
    (ha : lambda^2∣a-1) :
    eisEmbedding (symbol r (a+3*x))=eisEmbedding (symbol r a)*
      ShortDraftTrace.breveE (eisEmbedding (ramifiedAffineParameter j n*x)/eisLam/3) := by
  rcases hr with rfl|rfl
  · exact ramified_symbol_primary_shift j n a x ha
  · rw [symbol_neg_numerator _ _ (primary_add_three a x ha),symbol_neg_numerator _ _ ha]
    exact ramified_symbol_primary_shift j n a x ha

end
section

open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CubicRamified
local notation "Eis" => ActualEisensteinCubic.O

lemma ramifiedTraceLambda_square : ramifiedTraceLambda^2=(-3:Eis) := by
  unfold ramifiedTraceLambda
  linear_combination 4*ramified_omega_relation

lemma ramified_character_coprime (j n : ℕ) (r a : Eis)
    (hr : r=omega^j*ramifiedTraceLambda^n ∨ r=-(omega^j*ramifiedTraceLambda^n))
    (ha : lambda^2∣a-1) : IsCoprime r a := by
  have hc3 := (primary_coprime_three a ha).symm
  have ht : ramifiedTraceLambda∣(3:Eis) := by
    refine ⟨-ramifiedTraceLambda,?_⟩
    linear_combination ramifiedTraceLambda_square
  have hcT := hc3.of_isCoprime_of_dvd_left ht
  have hcW : IsCoprime omega a := by
    refine ⟨omega^2,0,?_⟩
    rw [zero_mul,add_zero,←pow_succ,omega_primitive.pow_eq_one]
  have hc : IsCoprime (omega^j*ramifiedTraceLambda^n) a := hcW.pow_left.mul_left hcT.pow_left
  rcases hr with rfl|rfl
  · exact hc
  · exact hc.neg_left

lemma affineCusp_phase_identity (h h1 q a k c x : Eis)
    (ha : a≠0) (hq : q≠0) (hh : h=q*h1) (hk : 3*k=h1+c*a) :
    ShortDraftTrace.breveE (eisEmbedding (c*x)/eisLam/3)*
      ShortDraftTrace.breveE (ninthCuspFrequency h*eisEmbedding (a+3*x)/eisEmbedding (q*a))=
      ShortDraftTrace.breveE (ninthCuspFrequency h/eisEmbedding q)*residueAdditive (3*k) a x := by
  have hk' : eisEmbedding k=(eisEmbedding h1+eisEmbedding c*eisEmbedding a)/3 := by
    apply (eq_div_iff (by norm_num : (3:ℂ)≠0)).mpr
    have he := congrArg eisEmbedding hk
    simp only [map_mul,map_add,map_ofNat] at he
    linear_combination he
  rw [←AddChar.map_add_eq_mul]
  unfold residueAdditive
  rw [←AddChar.map_add_eq_mul]
  apply congrArg ShortDraftTrace.breveE
  rw [hh]
  simp only [ninthCuspFrequency,cuspFrequency,map_add,map_mul,map_ofNat]
  rw [hk']
  field_simp [eisEmbedding_ne_zero ha,eisEmbedding_ne_zero hq,eisLam_ne_zero]
  ;ring

def ramifiedAffineGauss (h q r a : Eis) : ℂ :=
  ∑'x:CubicUnitResidue a,
    (eisEmbedding (symbol r (a+3*GaussianShiftedPartition.representative a x.val))*
      eisEmbedding (symbol (a+3*GaussianShiftedPartition.representative a x.val) a))*
      ShortDraftTrace.breveE (ninthCuspFrequency h*
        eisEmbedding (a+3*GaussianShiftedPartition.representative a x.val)/eisEmbedding (q*a))

lemma ramifiedAffineGauss_factor (h h1 q r a k : Eis) (j n : ℕ)
    (ha : a≠0) (hprimary : lambda^2∣a-1) (hq : q≠0)
    (hr : r=omega^j*ramifiedTraceLambda^n ∨ r=-(omega^j*ramifiedTraceLambda^n))
    (hh : h=q*h1) (hk : 3*k=h1+ramifiedAffineParameter j n*a) :
    ramifiedAffineGauss h q r a=
      ShortDraftTrace.breveE (ninthCuspFrequency h/eisEmbedding q)*
        (eisEmbedding (symbol r a)*eisEmbedding (symbol 3 a))*cubicUnitGaussSum k a := by
  rw [ramifiedAffineGauss,cubicUnitGaussSum,←tsum_mul_left]
  apply tsum_congr
  intro x
  let t := GaussianShiftedPartition.representative a x.val
  have hs : symbol (a+3*t) a=symbol (3*t) a := symbol_congr ⟨1,by ring⟩
  change (eisEmbedding (symbol r (a+3*t))*eisEmbedding (symbol (a+3*t) a))*
    ShortDraftTrace.breveE (ninthCuspFrequency h*eisEmbedding (a+3*t)/eisEmbedding (q*a))=_
  rw [ramified_symbol_primary_shift_signed j n r a t hr hprimary,hs,
    symbol_mul_numerator _ _ _ hprimary]
  rw [map_mul eisEmbedding (symbol 3 a) (symbol t a)]
  have hp := affineCusp_phase_identity h h1 q a k (ramifiedAffineParameter j n) t ha hq hh hk
  calc
    _ = (eisEmbedding (symbol r a)*eisEmbedding (symbol 3 a)*eisEmbedding (symbol t a))*
      (ShortDraftTrace.breveE (eisEmbedding (ramifiedAffineParameter j n*t)/eisLam/3)*
        ShortDraftTrace.breveE (ninthCuspFrequency h*eisEmbedding (a+3*t)/eisEmbedding (q*a))) := by ring
    _ = _ := by rw [hp];ring

theorem ramifiedAffineGauss_eq_unramified (h h1 q r a k : Eis) (j n : ℕ)
    (ha : a≠0) (hprimary : lambda^2∣a-1) (hq : q≠0)
    (hr : r=omega^j*ramifiedTraceLambda^n ∨ r=-(omega^j*ramifiedTraceLambda^n))
    (hh : h=q*h1) (hk : 3*k=h1+ramifiedAffineParameter j n*a) :
    ramifiedAffineGauss h q r a=
      ShortDraftTrace.breveE (ninthCuspFrequency h/eisEmbedding q)*
        cubicUnitGaussSum (3*r^2*h1) a := by
  rw [ramifiedAffineGauss_factor h h1 q r a k j n ha hprimary hq hr hh hk]
  have hcop := ramified_character_coprime j n r a hr hprimary
  have hcop3 : IsCoprime (3*r^2) a := (primary_coprime_three a hprimary).symm.mul_left hcop.pow_left
  have hp := cubicUnitGaussSum_phase_shift k (r^2) a ha hprimary hcop3
  have hc := symbol_cube_of_isCoprime r a hprimary hcop
  have hchars : eisEmbedding (symbol (r^2) a)*eisEmbedding (symbol (3*r^2) a)=
      eisEmbedding (symbol r a)*eisEmbedding (symbol 3 a) := by
    rw [←map_mul,←symbol_mul_numerator _ _ a hprimary,
      show r^2*(3*r^2)=3*r^4 by ring,symbol_mul_numerator _ _ a hprimary,
      symbol_pow_numerator _ _ hprimary 4,pow_succ,hc,one_mul,map_mul]
    ring
  rw [hchars] at hp
  have hcong : a∣k*(9*r^2)-3*r^2*h1 := by
    refine ⟨3*r^2*ramifiedAffineParameter j n,?_⟩
    linear_combination 3*r^2*hk
  have hg := cubicUnitGaussSum_frequency_congr (k*(9*r^2)) (3*r^2*h1) a ha hcong
  calc
    _ = ShortDraftTrace.breveE (ninthCuspFrequency h/eisEmbedding q)*
      (eisEmbedding (symbol r a)*eisEmbedding (symbol 3 a)*cubicUnitGaussSum k a) := by ring
    _ = _ := by rw [hp,hg]

end

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology Pointwise

open ConcreteTraceCRT
local notation "O" => ActualEisensteinCubic.O

def eisensteinUnitRotation (u : ActualEisensteinCubic.Oˣ) : ℂ≃ₗᵢ[ℝ]ℂ where
  toFun z := eisEmbedding (u:ActualEisensteinCubic.O)*z
  invFun z := eisEmbedding (↑u⁻¹:ActualEisensteinCubic.O)*z
  left_inv z := by
    dsimp only
    rw [←mul_assoc,←map_mul]
    simp
  right_inv z := by
    dsimp only
    rw [←mul_assoc,←map_mul]
    simp
  map_add' z w := mul_add _ _ _
  map_smul' t z := by
    simp only [RingHom.id_apply,Complex.real_smul]
    ring
  norm_map' z := by
    change ‖eisEmbedding (u:ActualEisensteinCubic.O)*z‖=‖z‖
    rw [norm_mul,GaussGeneratorTransport.norm_eisEmbedding_unit,one_mul]

def eisensteinUnitEquiv (u : ActualEisensteinCubic.Oˣ) : ActualEisensteinCubic.O≃ActualEisensteinCubic.O where
  toFun x := (u:ActualEisensteinCubic.O)*x
  invFun x := (↑u⁻¹:ActualEisensteinCubic.O)*x
  left_inv x := by dsimp only; rw [←mul_assoc];simp
  right_inv x := by dsimp only; rw [←mul_assoc];simp

def periodUnitEquiv (u : ActualEisensteinCubic.Oˣ) : periodLattice≃periodLattice :=
  (periodEquiv.symm.trans (eisensteinUnitEquiv u)).trans periodEquiv

lemma periodUnitEquiv_val (u : ActualEisensteinCubic.Oˣ) (x : periodLattice) :
    (periodUnitEquiv u x:ℂ)=eisEmbedding (u:ActualEisensteinCubic.O)*(x:ℂ) := by
  obtain ⟨n,rfl⟩ := periodEquiv.surjective x
  dsimp only [periodUnitEquiv,Equiv.trans_apply]
  rw [Equiv.symm_apply_apply]
  change (periodEquiv ((u:ActualEisensteinCubic.O)*n):ℂ)=eisEmbedding (u:ActualEisensteinCubic.O)*(periodEquiv n:ℂ)
  change 3*eisEmbedding ((u:ActualEisensteinCubic.O)*n)=eisEmbedding (u:ActualEisensteinCubic.O)*(3*eisEmbedding n)
  rw [map_mul]
  ring

lemma periodDomain_unit_rotation (u : ActualEisensteinCubic.Oˣ) :
    IsAddFundamentalDomain periodLattice (eisensteinUnitRotation u '' periodDomain) volume := by
  apply periodDomain_fundamental.image_of_equiv (eisensteinUnitRotation u).toEquiv
    (eisensteinUnitRotation u).symm.measurePreserving.quasiMeasurePreserving (periodUnitEquiv u⁻¹)
  intro n z
  change eisEmbedding (u:ActualEisensteinCubic.O)*((periodUnitEquiv u⁻¹ n:ℂ)+z)=
    (n:ℂ)+eisEmbedding (u:ActualEisensteinCubic.O)*z
  rw [periodUnitEquiv_val,mul_add,←mul_assoc,←map_mul]
  simp

theorem period_integral_unit_rotation (f : ℂ→ℂ)
    (hp : ∀n : ActualEisensteinCubic.O,∀z : ℂ,f (z+3*eisEmbedding n)=f z) (u : ActualEisensteinCubic.Oˣ) :
    (∫z in periodDomain,f (eisEmbedding (u:ActualEisensteinCubic.O)*z))=∫z in periodDomain,f z := by
  have hperiod (n : periodLattice) (z : ℂ) : f (n+ᵥz)=f z := by
    obtain ⟨m,rfl⟩ := periodEquiv.surjective n
    change f (3*eisEmbedding m+z)=f z
    simpa only [add_comm] using hp m z
  have heq := periodDomain_fundamental.setIntegral_eq (periodDomain_unit_rotation u) hperiod
  have hchange := (eisensteinUnitRotation u).measurePreserving.setIntegral_image_emb
    (eisensteinUnitRotation u).toHomeomorph.measurableEmbedding f periodDomain
  exact hchange.symm.trans heq.symm

theorem period_integral_unit_affine (f : ℂ→ℂ)
    (hp : ∀n : ActualEisensteinCubic.O,∀z : ℂ,f (z+3*eisEmbedding n)=f z) (u : ActualEisensteinCubic.Oˣ) (b : ℂ) :
    (∫z in periodDomain,f (eisEmbedding (u:ActualEisensteinCubic.O)*z+b))=∫z in periodDomain,f z := by
  have hg : ∀n : ActualEisensteinCubic.O,∀z : ℂ,(fun w=>f (w+b)) (z+3*eisEmbedding n)=(fun w=>f (w+b)) z := by
    intro n z
    dsimp
    rw [show z+3*eisEmbedding n+b=(z+b)+3*eisEmbedding n by ring,hp]
  rw [period_integral_unit_rotation (fun w=>f (w+b)) hg u]
  simpa only [add_comm] using period_integral_translation f hp b

end

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups

open ConcreteTraceCRT
local notation "O" => ActualEisensteinCubic.O

lemma integral_upper_triangular_action (T : SL(2,ActualEisensteinCubic.O)) (hc : T 1 0=0)
    (z : ℂ) (v : ℝ) (hv : 0<v) :
    integralComplexMatrix T • upperPoint z v hv=
      upperPoint (eisEmbedding (T 0 0)^2*z+eisEmbedding (T 0 0*T 0 1)) v hv := by
  have hdet : T 0 0*T 1 1=1 := by
    simpa only [Matrix.det_fin_two,hc,mul_zero,sub_zero] using T.property
  let u : ActualEisensteinCubic.Oˣ := ⟨T 1 1,T 0 0,by rw [mul_comm,hdet],hdet⟩
  have hn : ‖eisEmbedding (T 1 1)‖=1 := GaussGeneratorTransport.norm_eisEmbedding_unit u
  have hprod : eisEmbedding (T 1 1)*star (eisEmbedding (T 1 1))=1 := by
    simpa only [Complex.star_def,Complex.normSq_eq_norm_sq,hn,one_pow,Complex.ofReal_one] using
      Complex.mul_conj (eisEmbedding (T 1 1))
  have hstar : star (eisEmbedding (T 1 1))=eisEmbedding (T 0 0) := by
    have hnon : eisEmbedding (T 1 1)≠0 := by
      intro hz
      rw [hz,norm_zero] at hn
      exact zero_ne_one hn
    apply mul_left_cancel₀ hnon
    rw [hprod,←map_mul,mul_comm,hdet,map_one]
  rw [mobius_upperPoint]
  apply upperPoint_congr
  · simp only [integralComplexMatrix_apply,hc,map_zero,zero_mul,zero_add,star_zero,
      mul_zero,add_zero,norm_zero,hn,one_pow,hstar,map_mul]
    norm_num
    ; ring
  · simp only [integralComplexMatrix_apply,hc,map_zero,zero_mul,zero_add,norm_zero,
      hn,one_pow,]
    norm_num

theorem period_integral_upper_triangular
    (F : HyperbolicSpace→ℂ) (v : ℝ) (hv : 0<v)
    (hp : ∀n : ActualEisensteinCubic.O,∀z : ℂ,
      F (upperPoint (3*(z+3*eisEmbedding n)) v hv)=F (upperPoint (3*z) v hv))
    (T : SL(2,ActualEisensteinCubic.O)) (hc : T 1 0=0) :
    (∫z in periodDomain,F (integralComplexMatrix T • upperPoint (3*z) v hv))=
      ∫z in periodDomain,F (upperPoint (3*z) v hv) := by
  have hdet : T 0 0*T 1 1=1 := by
    simpa only [Matrix.det_fin_two,hc,mul_zero,sub_zero] using T.property
  let u : ActualEisensteinCubic.Oˣ := ⟨T 0 0,T 1 1,hdet,by rw [mul_comm,hdet]⟩
  let f : ℂ→ℂ := fun z=>F (upperPoint (3*z) v hv)
  have he (z : ℂ) : F (integralComplexMatrix T • upperPoint (3*z) v hv)=
      f (eisEmbedding (↑(u^2):ActualEisensteinCubic.O)*z+eisEmbedding (T 0 0*T 0 1)/3) := by
    rw [integral_upper_triangular_action T hc]
    dsimp only [f]
    congr 2
    simp only [Units.val_pow_eq_pow_val,map_pow]
    ring
  simp_rw [he]
  exact period_integral_unit_affine f hp (u^2) _

end

open Filter MeasureTheory
open scoped BigOperators Classical Topology ENNReal

local notation "O" => ActualEisensteinCubic.O
namespace SubexponentialBesselCoefficients

lemma series_scaled_three_average_zero (coeff : SubexponentialBesselCoefficients)
    (v : ℝ) (hv : 0<v) : (∫z in periodDomain,coeff.series (v,3*z))=0 := by
  let : Countable ActualEisensteinCubic.O := ActualEisensteinCubic.latticeCoordEquiv.injective.countable
  let : IsFiniteMeasure (volume.restrict periodDomain) := isFiniteMeasure_restrict.mpr (by
    rw [periodDomain_volume]
    exact ENNReal.ofReal_ne_top)
  let f : ActualEisensteinCubic.O→ℂ→ℂ := fun h z => coeff.term h (v,3*z)
  have hc (h : ActualEisensteinCubic.O) : Continuous (f h) := by
    change Continuous (fun z : ℂ => coeff.term h (v,3*z))
    simp_rw [coeff.term_eq_amplitude v hv h]
    change Continuous (fun z : ℂ => coeff.amplitude v h*
      Complex.exp (2*Real.pi*Complex.I*((cuspFrequency h*(3*z))+
        starRingEnd ℂ (cuspFrequency h*(3*z)))))
    fun_prop
  obtain ⟨C,hC,hbound⟩ := coeff.slab_bound v v hv le_rfl
  have hfbound (h : ActualEisensteinCubic.O) (z : ℂ) : ‖f h z‖≤C*Real.exp (-(Real.pi*v)*‖cuspFrequency h‖) :=
    hbound h (v,3*z) ⟨le_rfl,le_rfl⟩
  have hi (h : ActualEisensteinCubic.O) : IntegrableOn (f h) periodDomain volume :=
    (integrable_const (C*Real.exp (-(Real.pi*v)*‖cuspFrequency h‖))).mono'
      (hc h).aestronglyMeasurable (Eventually.of_forall (hfbound h))
  have hnorm (h : ActualEisensteinCubic.O) : (∫z in periodDomain,‖f h z‖)≤
      volume.real periodDomain*(C*Real.exp (-(Real.pi*v)*‖cuspFrequency h‖)) := by
    have hh := integral_mono_ae (hi h).norm (integrable_const (C*Real.exp (-(Real.pi*v)*‖cuspFrequency h‖)))
      (Eventually.of_forall (hfbound h))
    simpa only [setIntegral_const,smul_eq_mul] using hh
  have hs : Summable (fun h : ActualEisensteinCubic.O => ∫z in periodDomain,‖f h z‖) := by
    apply Summable.of_nonneg_of_le (fun h => integral_nonneg (fun z => norm_nonneg _)) hnorm
    exact ((summable_exp_neg_cuspFrequency_norm (Real.pi*v) (mul_pos Real.pi_pos hv)).mul_left C).mul_left
      (volume.real periodDomain)
  have hterm (h : ActualEisensteinCubic.O) : (∫z in periodDomain,f h z)=0 := by
    have he (z : ℂ) : cuspFrequency h*(3*z)= -cuspFrequency (-(3*h))*z := by
      simp only [cuspFrequency,map_neg,map_mul,map_ofNat]
      ring
    change (∫z in periodDomain,coeff.term h (v,3*z))=0
    simp_rw [coeff.term_eq_amplitude v hv h,he]
    rw [integral_const_mul,integral_cusp_character]
    by_cases hh : h=0
    · simp [hh,amplitude]
    · have hk : -(3*h)≠(0:ActualEisensteinCubic.O) := neg_ne_zero.mpr (mul_ne_zero (by norm_num) hh)
      simp [hk]
  change (∫z in periodDomain,∑'h : ActualEisensteinCubic.O,f h z)=0
  rw [←integral_tsum_of_summable_integral_norm hi hs]
  simp_rw [hterm]
  exact tsum_zero

lemma fullFunction_scaled_three_average (coeff : SubexponentialBesselCoefficients)
    (c : ℂ) (v : ℝ) (hv : 0<v) :
    (∫z in periodDomain,coeff.fullFunction c (upperPoint (3*z) v hv))=
      ((9*Real.sqrt 3/2:ℝ):ℂ)*c*(v:ℂ)^(2/3:ℂ) := by
  let : IsFiniteMeasure (volume.restrict periodDomain) := isFiniteMeasure_restrict.mpr (by
    rw [periodDomain_volume]
    exact ENNReal.ofReal_ne_top)
  have hc : Continuous (fun z : ℂ=>coeff.series (v,3*z)) :=
    (coeff.series_height_continuous v hv).comp (continuous_const.mul continuous_id)
  simp only [fullFunction,function,hyperbolicHeight_upperPoint,hyperbolicHorizontal_upperPoint]
  rw [integral_add (integrable_const _) (periodDomain_integrable_of_continuous _ hc),
    series_scaled_three_average_zero coeff v hv,add_zero,setIntegral_const]
  rw [Measure.real,periodDomain_volume,ENNReal.toReal_ofReal (by positivity)]
  simp only [Complex.real_smul]
  ring

end SubexponentialBesselCoefficients

theorem cubicSource_scaled_three_average (v : ℝ) (hv : 0<v) :
    (∫z in periodDomain,cubicSourceResidualFunction (upperPoint (3*z) v hv))=
      ((9*Real.sqrt 3/2:ℝ):ℂ)*((3*(Real.pi:ℂ))*constantArithmeticResidue)*(v:ℂ)^(2/3:ℂ) := by
  rw [cubicSourceResidualFunction_eq_bessel]
  exact sourceBesselCoefficients.fullFunction_scaled_three_average _ v hv

end CubicEisenstein

open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups

namespace CubicEisenstein
open ConcreteTraceCRT CubicKubota EisensteinCuspModThree
local notation "O" => ActualEisensteinCubic.O

lemma lowerCuspMatrix_zero : lowerCuspMatrix (0:ActualEisensteinCubic.O)=1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [lowerCuspMatrix]

lemma cubicSource_scaled_periodic (v : ℝ) (hv : 0<v) (n : ActualEisensteinCubic.O) (z : ℂ) :
    cubicSourceResidualFunction (upperPoint (3*(z+3*eisEmbedding n)) v hv)=
      cubicSourceResidualFunction (upperPoint (3*z) v hv) := by
  have he : 3*(z+3*eisEmbedding n)=3*z+3*eisEmbedding (3*n) := by
    rw [map_mul,map_ofNat]
    ring
  rw [cubicSourceResidualFunction_eq_bessel,he]
  exact sourceBesselFunction_period v hv (3*z) (3*n)

lemma sourceCuspRepresentative_periodic (j : Fin 3) (v : ℝ) (hv : 0<v) (n : ActualEisensteinCubic.O) (z : ℂ) :
    cubicSourceResidualFunction (integralComplexMatrix (cuspRepresentative j) •
      upperPoint (3*(z+3*eisEmbedding n)) v hv)=
    cubicSourceResidualFunction (integralComplexMatrix (cuspRepresentative j) •
      upperPoint (3*z) v hv) := by
  fin_cases j
  · simpa [cuspRepresentative,cuspParameter,lowerCuspMatrix_zero] using cubicSource_scaled_periodic v hv n z
  · simpa [cuspRepresentative,cuspParameter,ramifiedSourceFunction] using ramifiedSource_scaled_periodic10 v hv n z
  · simpa [cuspRepresentative,cuspParameter,ramifiedSourceFunction] using ramifiedSource_scaled_periodic19 v hv n z

def sourcePrincipalCuspConstant : ℂ :=
  ((9*Real.sqrt 3/2:ℝ):ℂ)*((3*(Real.pi:ℂ))*constantArithmeticResidue)

lemma sourceCuspRepresentative_average (j : Fin 3) (v : ℝ) (hv : 0<v) :
    (∫z in periodDomain,cubicSourceResidualFunction
      (integralComplexMatrix (cuspRepresentative j) • upperPoint (3*z) v hv))=
      (if j=0 then sourcePrincipalCuspConstant else 0)*(v:ℂ)^(2/3:ℂ) := by
  fin_cases j
  · simpa [cuspRepresentative,cuspParameter,lowerCuspMatrix_zero,sourcePrincipalCuspConstant] using
      cubicSource_scaled_three_average v hv
  · simpa [cuspRepresentative,cuspParameter,ramifiedSourceFunction] using ramifiedSource_zero_mode10 v hv
  · simpa [cuspRepresentative,cuspParameter,ramifiedSourceFunction] using ramifiedSource_zero_mode19 v hv

lemma sourceCusp_average_of_decomposition (M : SL(2,ActualEisensteinCubic.O)) (G : levelTwo) (j : Fin 3)
    (T : SL(2,ActualEisensteinCubic.O)) (hT : T 1 0=0) (hM : M=(G:SL(2,ActualEisensteinCubic.O))*cuspRepresentative j*T)
    (v : ℝ) (hv : 0<v) :
    (∫z in periodDomain,cubicSourceResidualFunction (integralComplexMatrix M • upperPoint (3*z) v hv))=
      (levelTwoComplexCharacter G*(if j=0 then sourcePrincipalCuspConstant else 0))*(v:ℂ)^(2/3:ℂ) := by
  have he (z : ℂ) : cubicSourceResidualFunction (integralComplexMatrix M • upperPoint (3*z) v hv)=
      levelTwoComplexCharacter G*cubicSourceResidualFunction
        (integralComplexMatrix (cuspRepresentative j) • (integralComplexMatrix T • upperPoint (3*z) v hv)) := by
    rw [hM,map_mul,map_mul,mul_smul,mul_smul,cubicSourceResidualFunction_automorphy]
  simp_rw [he]
  rw [integral_const_mul]
  have hi := period_integral_upper_triangular
    (fun w=>cubicSourceResidualFunction (integralComplexMatrix (cuspRepresentative j) • w))
    v hv (sourceCuspRepresentative_periodic j v hv) T hT
  rw [hi,sourceCuspRepresentative_average]
  ring

def sourceCuspConstant (M : SL(2,ActualEisensteinCubic.O)) : ℂ :=
  ∫z in periodDomain,cubicSourceResidualFunction (integralComplexMatrix M • upperPoint (3*z) 1 (by norm_num))

theorem sourceCusp_average_all (M : SL(2,ActualEisensteinCubic.O)) (v : ℝ) (hv : 0<v) :
    (∫z in periodDomain,cubicSourceResidualFunction (integralComplexMatrix M • upperPoint (3*z) v hv))=
      sourceCuspConstant M*(v:ℂ)^(2/3:ℂ) := by
  obtain ⟨G,j,T,hT,_,_,hM⟩ := three_cusp_decomposition M
  have h1 := sourceCusp_average_of_decomposition M G j T hT hM 1 (by norm_num)
  have hc : sourceCuspConstant M=levelTwoComplexCharacter G*(if j=0 then sourcePrincipalCuspConstant else 0) := by
    simpa only [sourceCuspConstant,Complex.ofReal_one,Complex.one_cpow,mul_one] using h1
  rw [hc]
  exact sourceCusp_average_of_decomposition M G j T hT hM v hv

theorem sourceCuspConstant_decomposition (M : SL(2,ActualEisensteinCubic.O)) (G : levelTwo) (j : Fin 3)
    (T : SL(2,ActualEisensteinCubic.O)) (hT : T 1 0=0) (hM : M=(G:SL(2,ActualEisensteinCubic.O))*cuspRepresentative j*T) :
    sourceCuspConstant M=levelTwoComplexCharacter G*(if j=0 then sourcePrincipalCuspConstant else 0) := by
  simpa only [sourceCuspConstant,Complex.ofReal_one,Complex.one_cpow,mul_one] using
    sourceCusp_average_of_decomposition M G j T hT hM 1 (by norm_num)

lemma sourcePrincipalCuspConstant_ne_zero : sourcePrincipalCuspConstant≠0 := by
  unfold sourcePrincipalCuspConstant
  apply mul_ne_zero
  · exact Complex.ofReal_ne_zero.mpr (ne_of_gt (by positivity))
  · exact mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
      constantArithmeticResidue_ne_zero

lemma sourceCuspConstant_zero_iff (M : SL(2,ActualEisensteinCubic.O)) (G : levelTwo) (j : Fin 3)
    (T : SL(2,ActualEisensteinCubic.O)) (hT : T 1 0=0) (hM : M=(G:SL(2,ActualEisensteinCubic.O))*cuspRepresentative j*T) :
    sourceCuspConstant M=0 ↔ j≠0 := by
  have hG : levelTwoComplexCharacter G≠0 := by
    intro hz
    have hn := norm_levelTwoComplexCharacter G
    rw [hz,norm_zero] at hn
    exact zero_ne_one hn
  rw [sourceCuspConstant_decomposition M G j T hT hM]
  by_cases hj : j=0 <;> simp [hj,hG,sourcePrincipalCuspConstant_ne_zero]

lemma sourceCuspConstant_left (G : levelTwo) (M : SL(2,ActualEisensteinCubic.O)) :
    sourceCuspConstant ((G:SL(2,ActualEisensteinCubic.O))*M)=levelTwoComplexCharacter G*sourceCuspConstant M := by
  unfold sourceCuspConstant
  simp_rw [map_mul,mul_smul,cubicSourceResidualFunction_automorphy]
  exact integral_const_mul _ _

lemma sourceCuspConstant_upper_right (M T : SL(2,ActualEisensteinCubic.O)) (hT : T 1 0=0) :
    sourceCuspConstant (M*T)=sourceCuspConstant M := by
  obtain ⟨G,j,S,hS,_,_,hM⟩ := three_cusp_decomposition M
  have hST : (S*T) 1 0=0 := by
    change (∑k : Fin 2,S 1 k*T k 0)=0
    rw [Fin.sum_univ_two,hS,hT]
    ring
  have he : M*T=(G:SL(2,ActualEisensteinCubic.O))*cuspRepresentative j*(S*T) := by rw [hM]; group
  rw [sourceCuspConstant_decomposition (M*T) G j (S*T) hST he,
    sourceCuspConstant_decomposition M G j S hS hM]

end CubicEisenstein

end

end OAI
