import OAI.NumberTheory.DirichletL.Eisenstein.ConjugateCuspProfiles
import OAI.NumberTheory.DirichletL.Eisenstein.CuspDilation

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

open scoped Classical MatrixGroups

namespace EisensteinCuspModThree

section
local notation "O" => ActualEisensteinCubic.O
open ActualEisensteinCoordinates (eval coords eval_coords unique_coordinates eval_mul)

abbrev Pair := ZMod 3 × ZMod 3
def add (x y : Pair) : Pair := (x.1+y.1,x.2+y.2)
def neg (x : Pair) : Pair := (-x.1,-x.2)
def sub (x y : Pair) : Pair := add x (neg y)
def mul (x y : Pair) : Pair := (x.1*y.1-x.2*y.2,x.1*y.2+x.2*y.1-x.2*y.2)
def scalar (a : ZMod 3) (x : Pair) : Pair := (a*x.1,a*x.2)
def residue (x : ActualEisensteinCubic.O) : Pair := ((coords x).1,(coords x).2)

lemma residue_eval (a b : ℤ) : residue (eval a b)=((a:ZMod 3),(b:ZMod 3)) := by
  have h := unique_coordinates (eval_coords (eval a b))
  exact Prod.ext (congrArg (fun n : ℤ => (n:ZMod 3)) h.1)
    (congrArg (fun n : ℤ => (n:ZMod 3)) h.2)

lemma residue_intCast (a : ℤ) : residue (a:ActualEisensteinCubic.O)=((a:ZMod 3),0) := by
  simpa [eval] using residue_eval a 0

lemma residue_zero : residue (0:ActualEisensteinCubic.O)=(0,0) := by simpa using residue_intCast 0
lemma residue_one : residue (1:ActualEisensteinCubic.O)=(1,0) := by simpa using residue_intCast 1

lemma residue_add (x y : ActualEisensteinCubic.O) : residue (x+y)=add (residue x) (residue y) := by
  have he : x+y=eval ((coords x).1+(coords y).1) ((coords x).2+(coords y).2) := by
    nth_rw 1 [←eval_coords x,←eval_coords y]
    simp only [eval,Int.cast_add]
    ring
  rw [he,residue_eval]
  simp [residue,add]

lemma residue_neg (x : ActualEisensteinCubic.O) : residue (-x)=neg (residue x) := by
  have he : -x=eval (-(coords x).1) (-(coords x).2) := by
    nth_rw 1 [←eval_coords x]
    simp only [eval,Int.cast_neg]
    ring
  rw [he,residue_eval]
  simp [residue,neg]

lemma residue_sub (x y : ActualEisensteinCubic.O) : residue (x-y)=sub (residue x) (residue y) := by
  rw [sub_eq_add_neg,residue_add,residue_neg]
  rfl

lemma residue_mul (x y : ActualEisensteinCubic.O) : residue (x*y)=mul (residue x) (residue y) := by
  calc
    residue (x*y)=residue (eval (coords x).1 (coords x).2*eval (coords y).1 (coords y).2) := by
      rw [eval_coords,eval_coords]
    _ = _ := by rw [eval_mul,residue_eval]; simp [residue,mul]

lemma residue_eq_implies_three_dvd {x y : ActualEisensteinCubic.O} (h : residue x=residue y) : (3:ActualEisensteinCubic.O)∣x-y := by
  have h1 : (3:ℤ)∣(coords x).1-(coords y).1 :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub (coords y).1 (coords x).1 3).mp
      (congrArg Prod.fst h).symm
  have h2 : (3:ℤ)∣(coords x).2-(coords y).2 :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub (coords y).2 (coords x).2 3).mp
      (congrArg Prod.snd h).symm
  obtain ⟨a,ha⟩ := h1
  obtain ⟨b,hb⟩ := h2
  refine ⟨eval a b,?_⟩
  nth_rw 1 [←eval_coords x,←eval_coords y]
  have he1 : (coords x).1=(coords y).1+3*a := by omega
  have he2 : (coords x).2=(coords y).2+3*b := by omega
  simp only [eval,he1,he2]
  push_cast
  ring

lemma residue_mul_intCast (a : ℤ) (x : ActualEisensteinCubic.O) : residue ((a:ActualEisensteinCubic.O)*x)=scalar (a:ZMod 3) (residue x) := by
  rw [residue_mul,residue_intCast]
  simp [mul,scalar]

def primitive (a c : Pair) : Prop := ¬(a.1+a.2=0 ∧ c.1+c.2=0)
instance primitive_decidable (a c : Pair) : Decidable (primitive a c) := inferInstanceAs
  (Decidable (¬(a.1+a.2=0 ∧ c.1+c.2=0)))

lemma primitive_of_determinant : ∀a b c d : Pair,sub (mul a d) (mul b c)=(1,0) → primitive a c := by
  decide +kernel

lemma first_column_primitive (M : SL(2,ActualEisensteinCubic.O)) : primitive (residue (M 0 0)) (residue (M 1 0)) := by
  have hd : M 0 0*M 1 1-M 0 1*M 1 0=1 := by simpa only [Matrix.det_fin_two] using M.property
  have hh := congrArg residue hd
  rw [residue_sub,residue_mul,residue_mul,residue_one] at hh
  exact primitive_of_determinant _ _ _ _ hh

def omegaPower (k : Fin 3) : Pair := if k=0 then (1,0) else if k=1 then (0,1) else (-1,-1)
def unitPair (u : Fin 2 × Fin 3) : Pair := scalar ((-1:ZMod 3)^u.1.val) (omegaPower u.2)
def cuspPair (j : Fin 3) : Pair := if j=0 then (0,0) else if j=1 then (0,1) else (-1,-1)

def columnTop (g : SL(2,ZMod 3)) (j : Fin 3) (u : Fin 2 × Fin 3) : Pair :=
  mul (add (g 0 0,0) (scalar (g 0 1) (cuspPair j))) (unitPair u)
def columnBottom (g : SL(2,ZMod 3)) (j : Fin 3) (u : Fin 2 × Fin 3) : Pair :=
  mul (add (g 1 0,0) (scalar (g 1 1) (cuspPair j))) (unitPair u)

theorem primitive_column_three_cusps : ∀a c : Pair, primitive a c →
    ∃g : SL(2,ZMod 3), ∃j : Fin 3, ∃u : Fin 2 × Fin 3,
      columnTop g j u=a ∧ columnBottom g j u=c := by
  decide +kernel

end

open scoped Classical MatrixGroups Matrix

local notation "O" => ActualEisensteinCubic.O
local notation "ζ" => ActualEisensteinCubic.omega
open CubicKubota CubicEisenstein

def unitRepresentative (u : Fin 2 × Fin 3) : ActualEisensteinCubic.Oˣ :=
  (-1:ActualEisensteinCubic.Oˣ)^u.1.val*CubicRamified.omega_isUnit.unit^u.2.val

lemma unitRepresentative_value (u : Fin 2 × Fin 3) :
    (unitRepresentative u:ActualEisensteinCubic.O)=(-1:ActualEisensteinCubic.O)^u.1.val*ζ^u.2.val := by
  simp [unitRepresentative]

lemma residue_omega : residue ζ=(0,1) := by
  have he : ActualEisensteinCoordinates.eval 0 1=ζ := by
    simp only [ActualEisensteinCoordinates.eval,Int.cast_zero,Int.cast_one,zero_add,one_mul]
    rfl
  rw [←he]
  exact residue_eval 0 1

lemma residue_omega_sq : residue (ζ^2)=(-1,-1) := by
  rw [pow_two,residue_mul,residue_omega]
  norm_num [mul]

lemma unitRepresentative_residue (u : Fin 2 × Fin 3) :
    residue (unitRepresentative u:ActualEisensteinCubic.O)=unitPair u := by
  rw [unitRepresentative_value]
  rcases u with ⟨i,j⟩
  fin_cases i <;> fin_cases j <;>
    norm_num [unitPair,omegaPower,scalar,residue_one,residue_neg,residue_omega,residue_omega_sq,neg]

def cuspParameter (j : Fin 3) : ActualEisensteinCubic.O := if j=0 then 0 else if j=1 then ζ else ζ^2
def cuspRepresentative (j : Fin 3) : SL(2,ActualEisensteinCubic.O) := lowerCuspMatrix (cuspParameter j)

lemma cuspParameter_residue (j : Fin 3) : residue (cuspParameter j)=cuspPair j := by
  fin_cases j <;> simp [cuspParameter,cuspPair,residue_zero,residue_omega,residue_omega_sq]

def unitDiagonal (u : ActualEisensteinCubic.Oˣ) : SL(2,ActualEisensteinCubic.O) :=
  ⟨!![(u:ActualEisensteinCubic.O),0;0,(↑u⁻¹:ActualEisensteinCubic.O)],by simp [Matrix.det_fin_two]⟩

def columnRepresentative (r : SL(2,ℤ)) (j : Fin 3) (u : Fin 2 × Fin 3) : SL(2,ActualEisensteinCubic.O) :=
  rationalEmbedding r*cuspRepresentative j*unitDiagonal (unitRepresentative u)

lemma columnRepresentative_entry (r : SL(2,ℤ)) (j : Fin 3) (u : Fin 2 × Fin 3) (i : Fin 2) :
    columnRepresentative r j u i 0=
      ((r i 0:ActualEisensteinCubic.O)+(r i 1:ActualEisensteinCubic.O)*cuspParameter j)*(unitRepresentative u:ActualEisensteinCubic.O) := by
  change (((r : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom O) *
    !![1, 0; cuspParameter j, 1]) *
    !![(unitRepresentative u : O), 0; 0, (↑(unitRepresentative u)⁻¹ : O)]) i 0 = _
  simp [Matrix.mul_apply, Fin.sum_univ_two]

lemma columnRepresentative_top_residue (r : SL(2,ℤ)) (j : Fin 3) (u : Fin 2 × Fin 3) :
    residue (columnRepresentative r j u 0 0)=columnTop (rationalReductionThree r) j u := by
  rw [columnRepresentative_entry,residue_mul,residue_add,residue_intCast,
    residue_mul_intCast,cuspParameter_residue,unitRepresentative_residue]
  rfl

lemma columnRepresentative_bottom_residue (r : SL(2,ℤ)) (j : Fin 3) (u : Fin 2 × Fin 3) :
    residue (columnRepresentative r j u 1 0)=columnBottom (rationalReductionThree r) j u := by
  rw [columnRepresentative_entry,residue_mul,residue_add,residue_intCast,
    residue_mul_intCast,cuspParameter_residue,unitRepresentative_residue]
  rfl

lemma same_column_quotient_lower_zero (M N : SL(2,ActualEisensteinCubic.O))
    (h0 : N 0 0=M 0 0) (h1 : N 1 0=M 1 0) : (N⁻¹*M) 1 0=0 := by
  simp only [Matrix.SpecialLinearGroup.coe_mul,Matrix.SpecialLinearGroup.coe_inv,
    Matrix.adjugate_fin_two,Matrix.mul_apply,Fin.sum_univ_two,Matrix.of_apply,
    Matrix.cons_val_zero,Matrix.cons_val_one,]
  rw [h0,h1]
  ring

theorem three_cusp_decomposition (M : SL(2,ActualEisensteinCubic.O)) :
    ∃G : levelTwo, ∃j : Fin 3, ∃T : SL(2,ActualEisensteinCubic.O),
      T 1 0=0 ∧ IsUnit (T 0 0) ∧ IsUnit (T 1 1) ∧
        M=(G:SL(2,ActualEisensteinCubic.O))*cuspRepresentative j*T := by
  obtain ⟨g,j,u,ht,hb⟩ := primitive_column_three_cusps _ _ (first_column_primitive M)
  obtain ⟨r,hr⟩ := rationalReductionThree_surjective g
  let B := columnRepresentative r j u
  have hB0 : residue (B 0 0)=residue (M 0 0) := by
    dsimp only [B]
    rw [columnRepresentative_top_residue,hr]
    exact ht
  have hB1 : residue (B 1 0)=residue (M 1 0) := by
    dsimp only [B]
    rw [columnRepresentative_bottom_residue,hr]
    exact hb
  have hxy : IsCoprime (M 0 0) (M 1 0) := by
    refine ⟨M 1 1,-M 0 1,?_⟩
    have hd := M.property
    rw [Matrix.det_fin_two] at hd
    linear_combination hd
  obtain ⟨N,hN0,hN1,hNB⟩ := exists_congruent_cusp_completion B (M 0 0) (M 1 0) hxy
    (residue_eq_implies_three_dvd hB0.symm) (residue_eq_implies_three_dvd hB1.symm)
  let G : levelTwo := ⟨(N*B⁻¹)*rationalEmbedding r,⟨⟨N*B⁻¹,hNB⟩,r,rfl⟩⟩
  let T : SL(2,ActualEisensteinCubic.O) := unitDiagonal (unitRepresentative u)*(N⁻¹*M)
  have hT : T 1 0=0 := by
    have hz := same_column_quotient_lower_zero M N hN0 hN1
    change (∑k : Fin 2,(unitDiagonal (unitRepresentative u)) 1 k*(N⁻¹*M) k 0)=0
    rw [Fin.sum_univ_two]
    change 0*(N⁻¹*M) 0 0+(↑(unitRepresentative u)⁻¹:ActualEisensteinCubic.O)*(N⁻¹*M) 1 0=0
    rw [hz]
    ring
  have hdet : T 0 0*T 1 1=1 := by
    have hd := T.property
    simpa only [Matrix.det_fin_two,hT,mul_zero,sub_zero] using hd
  refine ⟨G,j,T,hT,?_,?_,?_⟩
  · exact IsUnit.of_mul_eq_one _ hdet
  · exact IsUnit.of_mul_eq_one _ (show T 1 1*T 0 0=1 by simpa only [mul_comm] using hdet)
  · dsimp [G,T,B,columnRepresentative]
    group

end EisensteinCuspModThree

namespace CubicEisenstein
open MeasureTheory Filter
open scoped BigOperators Classical MatrixGroups

open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CubicRamified
local notation "Eis" => ActualEisensteinCubic.O
abbrev PrimaryCoprimeDenominator (a : PrimaryLower) := {d:PrimaryLower//IsCoprime a.val d.val}

def primaryDenominatorFromCoprime (a : PrimaryLower) (x : CoprimeElement a.val) :
    PrimaryCoprimeDenominator a := by
  refine ⟨⟨a.val+3*x.val,?_⟩,?_⟩
  · convert dvd_add a.2 (dvd_mul_right (3:Eis) x.val) using 1 ;ring
  · apply (isCoprime_right_congr_of_dvd a.val (a.val+3*x.val) (3*x.val) ⟨1,by ring⟩).mpr
    exact (primary_coprime_three a.val (primaryLower_primary a)).mul_right x.2

lemma primaryDenominatorFromCoprime_bijective (a : PrimaryLower) :
    Function.Bijective (primaryDenominatorFromCoprime a) := by
  constructor
  · intro x y h
    apply Subtype.ext
    have he := congrArg (fun d : PrimaryCoprimeDenominator a => d.val.val) h
    change a.val+3*x.val=a.val+3*y.val at he
    exact mul_left_cancel₀ (by norm_num : (3:Eis)≠0) (add_left_cancel he)
  · intro d
    have hdiv : (3:Eis)∣d.val.val-a.val := by
      simpa only [sub_sub_sub_cancel_right] using dvd_sub d.val.2 a.2
    obtain ⟨x,hx⟩ := hdiv
    have hd : d.val.val=a.val+3*x := by linear_combination hx
    have hcop : IsCoprime a.val x := by
      have hc : IsCoprime a.val (3*x) :=
        (isCoprime_right_congr_of_dvd a.val d.val.val (3*x) ⟨1,by rw [hd];ring⟩).mp d.2
      exact hc.of_isCoprime_of_dvd_right (dvd_mul_left x 3)
    refine ⟨⟨x,hcop⟩,Subtype.ext (Subtype.ext ?_)⟩
    exact hd.symm

def primaryDenominatorEquiv (a : PrimaryLower) : CoprimeElement a.val≃PrimaryCoprimeDenominator a :=
  Equiv.ofBijective _ (primaryDenominatorFromCoprime_bijective a)

def unitLowerIntegral (u : Eisˣ) (v : ℝ) (s freq : ℂ) (a d : Eis) : ℂ :=
  ∫z in periodDomain,unitLowerTerm u z v s a d*ShortDraftTrace.breveE (-freq*z)

lemma hasSum_unitLowerIntegrals (u : Eisˣ) (v : ℝ) (hv : 0<v) (s freq : ℂ) (hs : 2<s.re) :
    HasSum (fun p : UnitLowerData => unitLowerIntegral u v s freq p.1.val p.2.val.val)
      (∫z in periodDomain,eisenstein (integralComplexMatrix (lowerCuspMatrix (u:Eis))*
        upperSection z v hv) s*ShortDraftTrace.breveE (-freq*z)) := by
  have hh := ((unitLowerEquiv u).trans primitiveRowEquiv.symm).hasSum_iff.mpr
    (hasSum_integral_fixed_left_Eisenstein (integralComplexMatrix (lowerCuspMatrix (u:Eis))) v hv s freq hs)
  apply hh.congr_fun
  intro p
  apply integral_congr_ae
  exact Eventually.of_forall (fun z => by
    dsimp only [Equiv.trans_apply,unitLowerIntegral]
    rw [unitLower_summand])

lemma unitLowerTerm_eq_shifted (u : Eisˣ) (z : ℂ) (v : ℝ) (hv : 0<v)
    (s : ℂ) (a d : Eis) (ha : a≠0) :
    unitLowerTerm u z v s a d=
      (eisEmbedding (symbol (u:Eis) d)*eisEmbedding (symbol d a)*
        ((‖eisEmbedding a‖^2:ℝ):ℂ)^(-s))*
          shiftedHeightKernel v s (eisEmbedding d/eisEmbedding ((u:Eis)*a)) z := by
  rw [unitLowerTerm,rowHeight_eq_shiftedHeightKernel z v hv s ((u:Eis)*a) d (mul_ne_zero u.ne_zero ha),
    GaussGeneratorTransport.norm_eisEmbedding_unit_mul]
  ring

lemma unitLowerTerm_integrable (u : Eisˣ) (v : ℝ) (hv : 0<v)
    (s : ℂ) (hs : 1<s.re) (a d : Eis) (ha : a≠0) :
    Integrable (fun z=>unitLowerTerm u z v s a d) := by
  simp_rw [unitLowerTerm_eq_shifted u _ v hv s a d ha]
  exact (shiftedHeightKernel_integrable v hv s _ hs).const_mul _

lemma unitLowerTerm_fourier_integral (u : Eisˣ) (v : ℝ) (hv : 0<v)
    (s freq : ℂ) (a d : Eis) (ha : a≠0) :
    (∫z:ℂ,unitLowerTerm u z v s a d*ShortDraftTrace.breveE (-freq*z))=
      ((v:ℂ)^(2-s)*sourceFourierKernel s (freq*v))*
        ((‖eisEmbedding a‖^2:ℝ):ℂ)^(-s)*
          ((eisEmbedding (symbol (u:Eis) d)*eisEmbedding (symbol d a))*
            ShortDraftTrace.breveE (freq*eisEmbedding d/eisEmbedding ((u:Eis)*a))) := by
  simp_rw [unitLowerTerm_eq_shifted u _ v hv s a d ha,mul_assoc]
  rw [integral_const_mul,integral_const_mul,integral_const_mul,
    traceIntegral_shiftedHeightKernel v hv s (eisEmbedding d/eisEmbedding ((u:Eis)*a)) freq]
  ring_nf

lemma unitLowerGaussTerm_factor (h a k r : Eis) (u : Eisˣ) (j : ℕ)
    (ha : a≠0) (hprimary : lambda^2∣a-1) (hu : (u:Eis)=omega^j)
    (hk : 3*k=h*(↑u⁻¹:Eis)+(j:Eis)*a*ramifiedTraceLambda) :
    (eisEmbedding (symbol (u:Eis) (a+3*r))*eisEmbedding (symbol (a+3*r) a))*
      ShortDraftTrace.breveE (ninthCuspFrequency h*eisEmbedding (a+3*r)/eisEmbedding ((u:Eis)*a))=
    (ShortDraftTrace.breveE (ninthCuspFrequency h/eisEmbedding (u:Eis))*
      (eisEmbedding (symbol (u:Eis) a)*eisEmbedding (symbol 3 a)))*
        (eisEmbedding (symbol r a)*residueAdditive (3*k) a r) := by
  have hchar : eisEmbedding (symbol (u:Eis) (a+3*r))=
      eisEmbedding (symbol (u:Eis) a)*ShortDraftTrace.breveE ((j:ℂ)*eisEmbedding r/3) := by
    rw [hu]
    exact symbol_omega_pow_primary_shift j a r hprimary
  have hs : symbol (a+3*r) a=symbol (3*r) a := symbol_congr ⟨1,by ring⟩
  rw [hchar,hs,symbol_mul_numerator _ _ _ hprimary,map_mul]
  have hp := unitLower_phase_identity h a r k u j ha hk
  calc
    _ = (eisEmbedding (symbol (u:Eis) a)*eisEmbedding (symbol 3 a)*eisEmbedding (symbol r a))*
      (ShortDraftTrace.breveE ((j:ℂ)*eisEmbedding r/3)*
        ShortDraftTrace.breveE (ninthCuspFrequency h*eisEmbedding (a+3*r)/eisEmbedding ((u:Eis)*a))) := by ring
    _ = _ := by rw [hp];ring

end CubicEisenstein

open Filter MeasureTheory
open scoped BigOperators Classical

namespace CubicEisenstein

section
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CubicRamified
local notation "Eis" => ActualEisensteinCubic.O

lemma unitLowerTwistedCoefficient_add (h a k r n : Eis) (u : Eisˣ) (j : ℕ)
    (ha : a≠0) (hprimary : lambda^2∣a-1) (hu : (u:Eis)=omega^j)
    (hk : 3*k=h*(↑u⁻¹:Eis)+(j:Eis)*a*ramifiedTraceLambda) :
    (eisEmbedding (symbol (u:Eis) (a+3*(r+a*n)))*eisEmbedding (symbol (a+3*(r+a*n)) a))*
      ShortDraftTrace.breveE (ninthCuspFrequency h*eisEmbedding (a+3*(r+a*n))/eisEmbedding ((u:Eis)*a))=
    (eisEmbedding (symbol (u:Eis) (a+3*r))*eisEmbedding (symbol (a+3*r) a))*
      ShortDraftTrace.breveE (ninthCuspFrequency h*eisEmbedding (a+3*r)/eisEmbedding ((u:Eis)*a)) := by
  rw [unitLowerGaussTerm_factor h a k (r+a*n) u j ha hprimary hu hk,
    unitLowerGaussTerm_factor h a k r u j ha hprimary hu hk]
  rw [symbol_congr (show a∣r+a*n-r from ⟨n,by ring⟩),
    residueAdditive_three_congr k a (r+a*n) r ha ⟨n,by ring⟩]

lemma unitLowerTerm_weighted_translate (h a k r n : Eis) (u : Eisˣ) (j : ℕ)
    (ha : a≠0) (hprimary : lambda^2∣a-1) (hu : (u:Eis)=omega^j)
    (hk : 3*k=h*(↑u⁻¹:Eis)+(j:Eis)*a*ramifiedTraceLambda)
    (z : ℂ) (v : ℝ) (s : ℂ) :
    unitLowerTerm u z v s a (a+3*(r+a*((u:Eis)*n)))*
      ShortDraftTrace.breveE (-ninthCuspFrequency h*z)=
    unitLowerTerm u (z+3*eisEmbedding n) v s a (a+3*r)*
      ShortDraftTrace.breveE (-ninthCuspFrequency h*(z+3*eisEmbedding n)) := by
  let c1 := eisEmbedding (symbol (u:Eis) (a+3*(r+a*((u:Eis)*n))))*
    eisEmbedding (symbol (a+3*(r+a*((u:Eis)*n))) a)
  let c0 := eisEmbedding (symbol (u:Eis) (a+3*r))*eisEmbedding (symbol (a+3*r) a)
  let B := ninthCuspFrequency h*eisEmbedding (a+3*r)/eisEmbedding ((u:Eis)*a)
  let Q := ninthCuspFrequency h*(3*eisEmbedding n)
  have hc0 := eisEmbedding_ne_zero (mul_ne_zero u.ne_zero ha)
  have harg : ninthCuspFrequency h*eisEmbedding (a+3*(r+a*((u:Eis)*n)))/eisEmbedding ((u:Eis)*a)=B+Q := by
    dsimp [B,Q]
    simp only [map_add,map_mul,map_ofNat]
    field_simp [eisEmbedding_ne_zero u.ne_zero,eisEmbedding_ne_zero ha]
    ;ring
  have hcoef := unitLowerTwistedCoefficient_add h a k r ((u:Eis)*n) u j ha hprimary hu hk
  change c1*ShortDraftTrace.breveE (ninthCuspFrequency h*
    eisEmbedding (a+3*(r+a*((u:Eis)*n)))/eisEmbedding ((u:Eis)*a))=c0*ShortDraftTrace.breveE B at hcoef
  rw [harg,AddChar.map_add_eq_mul] at hcoef
  have heB : ShortDraftTrace.breveE B≠0 := Complex.exp_ne_zero _
  have heQ : ShortDraftTrace.breveE Q≠0 := Complex.exp_ne_zero _
  have hmult : c1*ShortDraftTrace.breveE Q=c0 := by
    apply mul_right_cancel₀ heB
    calc
      _ = c1*(ShortDraftTrace.breveE B*ShortDraftTrace.breveE Q) := by ring
      _ = _ := hcoef
  have hsolve : c1=c0*ShortDraftTrace.breveE (-Q) := by
    rw [AddChar.map_neg_eq_inv]
    calc
      c1=c1*(ShortDraftTrace.breveE Q*(ShortDraftTrace.breveE Q)⁻¹) := by rw [mul_inv_cancel₀ heQ,mul_one]
      _ = (c1*ShortDraftTrace.breveE Q)*(ShortDraftTrace.breveE Q)⁻¹ := by ring
      _ = _ := by rw [hmult]
  have hrow : eisEmbedding ((u:Eis)*a)*z+eisEmbedding (a+3*(r+a*((u:Eis)*n)))=
      eisEmbedding ((u:Eis)*a)*(z+3*eisEmbedding n)+eisEmbedding (a+3*r) := by
    simp only [map_add,map_mul,map_ofNat]
    ring
  change c1*((v/(‖eisEmbedding ((u:Eis)*a)*z+eisEmbedding (a+3*(r+a*((u:Eis)*n)))‖^2+
    ‖eisEmbedding ((u:Eis)*a)‖^2*v^2):ℝ):ℂ)^s*ShortDraftTrace.breveE (-ninthCuspFrequency h*z)=_
  rw [hsolve,hrow]
  unfold unitLowerTerm
  have hphase : -ninthCuspFrequency h*(z+3*eisEmbedding n)=(-Q)+(-ninthCuspFrequency h*z) := by
    dsimp [Q]
    ring
  rw [hphase,AddChar.map_add_eq_mul]
  dsimp only [c0]
  ring

lemma unitLowerIntegral_sum_translate (h a k r : Eis) (u : Eisˣ) (j : ℕ)
    (ha : a≠0) (hprimary : lambda^2∣a-1) (hu : (u:Eis)=omega^j)
    (hk : 3*k=h*(↑u⁻¹:Eis)+(j:Eis)*a*ramifiedTraceLambda)
    (v : ℝ) (hv : 0<v) (s : ℂ) (hs : 1<s.re) :
    (∑'n:Eis,unitLowerIntegral u v s (ninthCuspFrequency h) a (a+3*(r+a*((u:Eis)*n))))=
      ∫z:ℂ,unitLowerTerm u z v s a (a+3*r)*ShortDraftTrace.breveE (-ninthCuspFrequency h*z) := by
  have hint := trace_mul_integrable (fun z=>unitLowerTerm u z v s a (a+3*r))
    (unitLowerTerm_integrable u v hv s hs a (a+3*r) ha) (ninthCuspFrequency h)
  rw [integral_eq_period_integrals _ hint]
  apply tsum_congr
  intro n
  apply integral_congr_ae
  exact Eventually.of_forall (fun z => unitLowerTerm_weighted_translate h a k r n u j ha hprimary hu hk z v s)

def unitCuspIndexEquiv (u : Eisˣ) : Eis≃Eis where
  toFun n := (u:Eis)*n
  invFun n := (↑u⁻¹:Eis)*n
  left_inv n := by simp [←mul_assoc]
  right_inv n := by simp [←mul_assoc]

end

open Filter MeasureTheory
open scoped BigOperators Classical MatrixGroups

open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CubicRamified
local notation "Eis" => ActualEisensteinCubic.O

lemma unitDenominator_integral_formula (u : Eisˣ) (j : ℕ) (hu : (u:Eis)=omega^j)
    (h : Eis) (hh : UnitCuspFrequency h u j) (a : PrimaryLower)
    (v : ℝ) (hv : 0<v) (s : ℂ) (hs : 2<s.re) :
    (∑'d:PrimaryCoprimeDenominator a,unitLowerIntegral u v s (ninthCuspFrequency h) a.val d.val.val)=
      ((v:ℂ)^(2-s)*sourceFourierKernel s (ninthCuspFrequency h*v))*
        ((‖eisEmbedding a.val‖^2:ℝ):ℂ)^(-s)*unitLowerGauss h u a.val := by
  obtain ⟨k,hk⟩ := unitCuspFrequency_lift h a.val u j (primaryLower_primary a) hh
  let e := (cubicResidueElementEquiv a.val (primaryLower_ne_zero a)).trans (primaryDenominatorEquiv a)
  have hf : Summable (fun d:PrimaryCoprimeDenominator a =>
      unitLowerIntegral u v s (ninthCuspFrequency h) a.val d.val.val) :=
    (hasSum_unitLowerIntegrals u v hv s (ninthCuspFrequency h) hs).summable.sigma_factor a
  have hsum := e.summable_iff.mpr hf
  change Summable (fun q:CubicUnitResidue a.val×Eis =>
    unitLowerIntegral u v s (ninthCuspFrequency h) a.val
      (a.val+3*(GaussianShiftedPartition.representative a.val q.1.val+a.val*q.2))) at hsum
  rw [←e.tsum_eq]
  change (∑'q:CubicUnitResidue a.val×Eis,
    unitLowerIntegral u v s (ninthCuspFrequency h) a.val
      (a.val+3*(GaussianShiftedPartition.representative a.val q.1.val+a.val*q.2)))=_
  rw [hsum.tsum_prod]
  have hinner (r:CubicUnitResidue a.val) :
      (∑'n:Eis,unitLowerIntegral u v s (ninthCuspFrequency h) a.val
        (a.val+3*(GaussianShiftedPartition.representative a.val r.val+a.val*n)))=
      ((v:ℂ)^(2-s)*sourceFourierKernel s (ninthCuspFrequency h*v))*
        ((‖eisEmbedding a.val‖^2:ℝ):ℂ)^(-s)*
          ((eisEmbedding (symbol (u:Eis) (a.val+3*GaussianShiftedPartition.representative a.val r.val))*
            eisEmbedding (symbol (a.val+3*GaussianShiftedPartition.representative a.val r.val) a.val))*
              ShortDraftTrace.breveE (ninthCuspFrequency h*
                eisEmbedding (a.val+3*GaussianShiftedPartition.representative a.val r.val)/eisEmbedding ((u:Eis)*a.val))) := by
    rw [←(unitCuspIndexEquiv u).tsum_eq]
    exact (unitLowerIntegral_sum_translate h a.val k
      (GaussianShiftedPartition.representative a.val r.val) u j (primaryLower_ne_zero a)
      (primaryLower_primary a) hu hk v hv s (by linarith)).trans
        (unitLowerTerm_fourier_integral u v hv s (ninthCuspFrequency h) a.val _ (primaryLower_ne_zero a))
  simp_rw [hinner]
  exact tsum_mul_left

theorem unitLowerEisenstein_fourier (u : Eisˣ) (j : ℕ) (hu : (u:Eis)=omega^j)
    (h : Eis) (hh : UnitCuspFrequency h u j)
    (v : ℝ) (hv : 0<v) (s : ℂ) (hs : 2<s.re) :
    (∫z in periodDomain,eisenstein (integralComplexMatrix (lowerCuspMatrix (u:Eis))*
      upperSection z v hv) s*ShortDraftTrace.breveE (-ninthCuspFrequency h*z))=
      ((v:ℂ)^(2-s)*sourceFourierKernel s (ninthCuspFrequency h*v))*
        ShortDraftTrace.breveE (ninthCuspFrequency h/eisEmbedding (u:Eis))*
          unramifiedCubicGaussSeries s (3*h*(u:Eis)) := by
  have hhSum := hasSum_unitLowerIntegrals u v hv s (ninthCuspFrequency h) hs
  rw [←hhSum.tsum_eq,hhSum.summable.tsum_sigma]
  simp_rw [unitDenominator_integral_formula u j hu h hh _ v hv s hs]
  have he : (∑'a:PrimaryLower,
      ((v:ℂ)^(2-s)*sourceFourierKernel s (ninthCuspFrequency h*v))*
        ((‖eisEmbedding a.val‖^2:ℝ):ℂ)^(-s)*unitLowerGauss h u a.val)=
      ((v:ℂ)^(2-s)*sourceFourierKernel s (ninthCuspFrequency h*v))*unitCuspArithmeticSeries s h u := by
    rw [unitCuspArithmeticSeries,←tsum_mul_left]
    apply tsum_congr
    intro a
    ring
  rw [he,unitCuspArithmeticSeries_eq s h u j hu hh]
  ring

end CubicEisenstein

open scoped Classical MatrixGroups
namespace CubicKubota
open ActualEisensteinCubic ConcreteTraceCRT CubicEisenstein CubicJacobiGlobal CubicRamified
local notation "Eis" => ActualEisensteinCubic.O

lemma levelTwo_entry_integer (g : levelTwo) (i j : Fin 2) :
    (3:Eis)∣((g:SL(2,Eis)) i j-((levelTwoRight g) i j:ℤ)) := by
  have he : Matrix.SpecialLinearGroup.map (n:=Fin 2)
      (Ideal.Quotient.mk (Ideal.span {(3:Eis)})) (g:SL(2,Eis)) =
      Matrix.SpecialLinearGroup.map (n:=Fin 2)
      (Ideal.Quotient.mk (Ideal.span {(3:Eis)})) (rationalEmbedding (levelTwoRight g)) := by
    rw [←levelTwo_product g,map_mul]
    have hn : Matrix.SpecialLinearGroup.map (n:=Fin 2)
        (Ideal.Quotient.mk (Ideal.span {(3:Eis)})) (levelTwoLeft g:SL(2,Eis))=1 := (levelTwoLeft g).property
    rw [hn,one_mul]
  have h := congrArg (fun A : SL(2,Eis⧸Ideal.span {(3:Eis)})=>A i j) he
  exact Ideal.mem_span_singleton.mp ((Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp h)

def integerUpper (b : ℤ) : SL(2,ℤ) := ⟨!![1,b;0,1],by simp [Matrix.det_fin_two_of]⟩
def integerLower (c : ℤ) : SL(2,ℤ) := ⟨!![1,0;c,1],by simp [Matrix.det_fin_two_of]⟩

lemma levelTwoComplexCharacter_primary (g : levelTwo)
    (ha : lambda^2∣((g:SL(2,Eis)) 0 0)-1) :
    levelTwoComplexCharacter g =
      eisEmbedding (symbol ((g:SL(2,Eis)) 1 0) ((g:SL(2,Eis)) 0 0)) := by
  let A : SL(2,Eis) := g
  let b : ℤ := levelTwoRight g 0 1
  let c : ℤ := levelTwoRight g 1 0
  have hA : (3:Eis)∣A 0 0-1 := three_dvd_primary_sub_one _ ha
  have hB : (3:Eis)∣A 0 1-(b:Eis) := levelTwo_entry_integer g 0 1
  have hC : (3:Eis)∣A 1 0-(c:Eis) := levelTwo_entry_integer g 1 0
  have hdet : A 0 0*A 1 1-A 0 1*A 1 0=1 := by
    simpa only [Matrix.det_fin_two] using A.property
  have hD : (3:Eis)∣A 1 1-(1+(b:Eis)*(c:Eis)) := by
    have hh := dvd_add (dvd_add (dvd_neg.mpr (dvd_mul_of_dvd_left hA (A 1 1)))
      (dvd_mul_of_dvd_left hB (A 1 0))) (dvd_mul_of_dvd_right hC (b:Eis))
    convert hh using 1 ; linear_combination hdet
  let N : SL(2,Eis) := ⟨!![A 0 0,A 0 1-(b:Eis)*A 0 0;
    A 1 0-(c:Eis)*A 0 0,A 1 1-(c:Eis)*A 0 1-(b:Eis)*(A 1 0-(c:Eis)*A 0 0)],by
    rw [Matrix.det_fin_two_of]
    linear_combination hdet⟩
  have hN : N∈levelThree := by
    apply (mem_levelThree_iff_entries N).mpr
    intro i j
    fin_cases i <;> fin_cases j
    · exact hA
    · have hh:=dvd_sub hB (dvd_mul_of_dvd_right hA (b:Eis))
      convert hh using 1 ; dsimp [N] ; ring
    · have hh:=dvd_sub hC (dvd_mul_of_dvd_right hA (c:Eis))
      convert hh using 1 ; dsimp [N] ; ring
    · have hh:=dvd_add (dvd_sub (dvd_sub hD (dvd_mul_of_dvd_right hB (c:Eis)))
        (dvd_mul_of_dvd_right hC (b:Eis))) (dvd_mul_of_dvd_right hA ((b:Eis)*(c:Eis)))
      convert hh using 1 ; dsimp [N] ; ring
  let lengthScale : levelTwo := ⟨rationalEmbedding (integerLower c),rational_mem_levelTwo _⟩
  let U : levelTwo := ⟨rationalEmbedding (integerUpper b),rational_mem_levelTwo _⟩
  let n : levelThree := ⟨N,hN⟩
  let n2 : levelTwo := ⟨N,levelThree_le_levelTwo hN⟩
  have he : g=lengthScale*n2*U := by
    apply Subtype.ext
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    change A i j = (((!![(1 : ℤ), 0; c, 1]).map (Int.castRingHom Eis) *
      (N : Matrix (Fin 2) (Fin 2) Eis)) *
      (!![(1 : ℤ), b; 0, 1]).map (Int.castRingHom Eis)) i j
    fin_cases i <;> fin_cases j <;>
      norm_num [N, Matrix.mul_apply, Fin.sum_univ_two] <;> ring
  conv_lhs => rw [he,map_mul,map_mul]
  have hL : levelTwoComplexCharacter lengthScale=1 := levelTwoComplexCharacter_rational _
  have hU : levelTwoComplexCharacter U=1 := levelTwoComplexCharacter_rational _
  rw [hL,hU,one_mul,mul_one]
  change levelTwoComplexCharacter ⟨(n:SL(2,Eis)),levelThree_le_levelTwo n.property⟩=_
  rw [levelTwoComplexCharacter_restrict]
  change eisEmbedding (symbol (A 1 0-(c:Eis)*A 0 0) (A 0 0))=_
  congr 1
  exact symbol_congr (x:=A 1 0-(c:Eis)*A 0 0) (y:=A 1 0) (d:=A 0 0) ⟨-(c:Eis),by ring⟩

end CubicKubota

end

end OAI
