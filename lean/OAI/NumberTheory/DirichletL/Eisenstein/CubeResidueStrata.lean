import OAI.NumberTheory.DirichletL.Reciprocity.PrimaryCongruences

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

namespace CubicEisenstein

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology

local notation "O" => ActualEisensteinCubic.O
namespace SubexponentialBesselCoefficients

theorem series_cusp_decay (coeff : SubexponentialBesselCoefficients) (a : ℝ) (ha : 0<a) :
    ∃C : ℝ,0≤C ∧ ∀v z,a≤v → ‖coeff.series (v,z)‖≤C*Real.exp (-residualCuspDecayRate*v) := by
  obtain ⟨D,hD,hterm⟩ := coeff.term_cusp_bound a ha
  let S : ℝ := ∑'h : ActualEisensteinCubic.O,Real.exp (-(Real.pi*a/2)*‖cuspFrequency h‖)
  have hS : 0≤S := tsum_nonneg (fun h => (Real.exp_pos _).le)
  have hs := summable_exp_neg_cuspFrequency_norm (Real.pi*a/2) (by positivity)
  refine ⟨D*S*(2/(2*residualCuspDecayRate)),by have := residualCuspDecayRate_pos;positivity,?_⟩
  intro v z hav
  have hv : 0<v := ha.trans_le hav
  have hb (h : ActualEisensteinCubic.O) : ‖coeff.term h (v,z)‖≤
      (D*v*Real.exp (-(2*residualCuspDecayRate)*v))*Real.exp (-(Real.pi*a/2)*‖cuspFrequency h‖) := by
    by_cases hh : h=0
    · simp only [term,ite_eq_left hh,norm_zero]
      positivity
    have he : Real.exp (-(Real.pi*v)*‖cuspFrequency h‖)≤
        Real.exp (-(2*residualCuspDecayRate)*v)*Real.exp (-(Real.pi*a/2)*‖cuspFrequency h‖) := by
      rw [←Real.exp_add]
      apply Real.exp_le_exp.mpr
      have h1 := mul_le_mul_of_nonneg_left (cuspFrequency_norm_lower h hh)
        (show 0≤Real.pi*v/2 by positivity)
      have h2 := mul_le_mul_of_nonneg_left hav (show 0≤Real.pi*‖cuspFrequency h‖/2 by positivity)
      unfold residualCuspDecayRate
      nlinarith
    exact (hterm h v z hav).trans ((mul_le_mul_of_nonneg_left he (by positivity)).trans_eq (by ring))
  have hsum := tsum_of_norm_bounded (hs.hasSum.mul_left (D*v*Real.exp (-(2*residualCuspDecayRate)*v))) hb
  calc
    _ ≤ (D*v*Real.exp (-(2*residualCuspDecayRate)*v))*S := hsum
    _ = (D*S)*(v*Real.exp (-(2*residualCuspDecayRate)*v)) := by ring
    _ ≤ (D*S)*((2/(2*residualCuspDecayRate))*Real.exp (-((2*residualCuspDecayRate)/2)*v)) :=
      mul_le_mul_of_nonneg_left (norm_mul_exp_neg_bound (2*residualCuspDecayRate) v
        (mul_pos (by norm_num) residualCuspDecayRate_pos)) (mul_nonneg hD hS)
    _ = _ := by
      rw [show -((2*residualCuspDecayRate)/2)*v=-residualCuspDecayRate*v by ring]
      ring

theorem series_cubic_decay (coeff : SubexponentialBesselCoefficients) (a : ℝ) (ha : 0<a) :
    ∃C : ℝ,0≤C ∧ ∀v z,a≤v → ‖coeff.series (v,z)‖≤C/v^3 := by
  obtain ⟨C,hC,hbound⟩ := coeff.series_cusp_decay a ha
  let k := residualCuspDecayRate
  have hk : 0<k := residualCuspDecayRate_pos
  refine ⟨C*(6/k^3),by positivity,?_⟩
  intro v z hav
  have hv : 0<v := ha.trans_le hav
  have he : Real.exp (-k*v)*v^3≤6/k^3 := by
    have hb := Real.pow_div_factorial_le_exp (k*v) (mul_nonneg hk.le hv.le) 3
    norm_num only [Nat.factorial] at hb
    have hm := mul_le_mul_of_nonneg_right hb (Real.exp_pos (-k*v)).le
    rw [←Real.exp_add,show k*v+ -k*v=0 by ring,Real.exp_zero] at hm
    apply (le_div_iff₀ (pow_pos hk 3)).mpr
    nlinarith [hm]
  apply (le_div_iff₀ (pow_pos hv 3)).mpr
  calc
    _ ≤ (C*Real.exp (-k*v))*v^3 := mul_le_mul_of_nonneg_right (hbound v z hav) (pow_nonneg hv.le 3)
    _ = C*(Real.exp (-k*v)*v^3) := by ring
    _ ≤ C*(6/k^3) := mul_le_mul_of_nonneg_left he hC

theorem fullFunction_zero_cubic_decay (coeff : SubexponentialBesselCoefficients) (a : ℝ) (ha : 0<a) :
    ∃C : ℝ,0≤C ∧ ∀v (hv : 0<v) z,a≤v →
      ‖coeff.fullFunction 0 (upperPoint z v hv)‖≤C/v^3 := by
  obtain ⟨C,hC,hbound⟩ := coeff.series_cubic_decay a ha
  refine ⟨C,hC,fun v hv z hav => ?_⟩
  simpa only [fullFunction,zero_mul,zero_add,function,hyperbolicHeight_upperPoint,hyperbolicHorizontal_upperPoint]
    using hbound v z hav

end SubexponentialBesselCoefficients
end

open scoped BigOperators Classical MatrixGroups Matrix

section
open ActualEisensteinCubic CubicKubota ConcreteTraceCRT CompletedGauss
open PrimaryIdealUnitReindex (GoodIdeal GoodElement)
local notation "Eis" => ActualEisensteinCubic.O
local notation "ramLambda" => (omega-1:Eis)

lemma halfPrimary_lambda_dvd_three : ramLambda ∣ (3:Eis) := by
  exact (dvd_pow_self ramLambda (by decide : (2:ℕ)≠0)).trans lambda_sq_dvd_three

lemma halfPrimary_lambda_not_dvd_one : ¬ramLambda ∣ (1:Eis) := by
  intro h
  exact PrimaryIdealUnitReindex.lambda_prime_actual.not_isUnit (isUnit_of_dvd_one h)

lemma halfPrimary_omega_pow (j:ℕ) : ramLambda ∣ omega^j-1 := by
  simpa only [one_pow] using sub_dvd_pow_sub_pow omega (1:Eis) j

lemma halfPrimary_not_negative (j:ℕ) : ¬ramLambda ∣ -(omega^j)-1 := by
  intro h
  have h2 : ramLambda ∣ (2:Eis) := by
    have hh:=dvd_add h (halfPrimary_omega_pow j)
    convert dvd_neg.mpr hh using 1 ;ring
  apply halfPrimary_lambda_not_dvd_one
  convert dvd_sub halfPrimary_lambda_dvd_three h2 using 1 ;ring

abbrev HalfPrimary := {b:Eis // ramLambda ∣ b-1}

lemma halfPrimary_ne_zero (b:HalfPrimary) : b.val≠0 := by
  intro h
  apply halfPrimary_lambda_not_dvd_one
  simpa only [h,zero_sub,dvd_neg] using b.2

lemma halfPrimary_not_dvd (b:HalfPrimary) : ¬ramLambda∣b.val := by
  intro h
  apply halfPrimary_lambda_not_dvd_one
  convert dvd_sub h b.2 using 1 ;ring

def halfPrimaryFromAssociate (p:Fin 3×PrimaryLower) : HalfPrimary :=
  ⟨omega^p.1.val*p.2.val,by
    have ha:ramLambda∣p.2.val-1:=halfPrimary_lambda_dvd_three.trans p.2.2
    convert dvd_add ((halfPrimary_omega_pow p.1.val).mul_right p.2.val) ha using 1 ;ring⟩

lemma halfPrimaryFromAssociate_injective : Function.Injective halfPrimaryFromAssociate := by
  intro p q hpq
  have he:omega^p.1.val*p.2.val=omega^q.1.val*q.2.val:=congrArg Subtype.val hpq
  have hunit (j:Fin 3):IsUnit (omega^j.val):=(omega_primitive.isUnit (by decide)).pow _
  have hs:(Ideal.span {p.2.val}:Ideal Eis)=Ideal.span {q.2.val}:=by
    simpa only [Ideal.span_singleton_mul_left_unit (hunit p.1),
      Ideal.span_singleton_mul_left_unit (hunit q.1)] using
      congrArg (fun z:Eis=>(Ideal.span {z}:Ideal Eis)) he
  have hab:p.2=q.2:=by
    apply Subtype.ext
    have hg:=congrArg primaryGenerator hs
    simpa only [primaryGenerator_span p.2.val (primaryLower_ne_zero p.2) (primaryLower_primary p.2),
      primaryGenerator_span q.2.val (primaryLower_ne_zero q.2) (primaryLower_primary q.2)] using hg
  have hj:p.1=q.1:=by
    apply Fin.ext
    apply omega_primitive.pow_inj p.1.isLt q.1.isLt
    rw [hab] at he
    exact mul_right_cancel₀ (primaryLower_ne_zero q.2) he
  exact Prod.ext hj hab

lemma halfPrimaryFromAssociate_surjective : Function.Surjective halfPrimaryFromAssociate := by
  intro b
  let z:GoodElement:=⟨b.val,PrimaryIdealUnitReindex.primaryGenerator_span_ne_zero_iff b.val |>.mpr
    (halfPrimary_not_dvd b)⟩
  let p:=PrimaryIdealUnitReindex.unitIdealEquiv.symm z
  have he:(p.1:Eis)*primaryGenerator p.2.val=b.val:=
    congrArg Subtype.val (PrimaryIdealUnitReindex.unitIdealEquiv.apply_symm_apply z)
  let a:PrimaryLower:=primaryLowerIdealEquiv.symm p.2
  have ha:a.val=primaryGenerator p.2.val:=rfl
  have hea:(p.1:Eis)*a.val=b.val:=by simpa only [ha] using he
  have hu:ramLambda∣(p.1:Eis)-1:=by
    have hpa:ramLambda∣a.val-1:=halfPrimary_lambda_dvd_three.trans a.2
    have hh:=dvd_sub b.2 (hpa.mul_left (p.1:Eis))
    rw [←hea] at hh
    convert hh using 1 ;ring
  obtain ⟨j,hj|hj⟩:=unit_eq_sign_omega p.1
  · exact ⟨(j,a),Subtype.ext (by simpa only [halfPrimaryFromAssociate,hj] using hea)⟩
  · exact (halfPrimary_not_negative j.val (by simpa only [hj] using hu)).elim

def halfPrimaryAssociateEquiv : Fin 3×PrimaryLower ≃ HalfPrimary :=
  Equiv.ofBijective halfPrimaryFromAssociate
    ⟨halfPrimaryFromAssociate_injective,halfPrimaryFromAssociate_surjective⟩

lemma halfPrimaryAssociateEquiv_apply (j:Fin 3) (a:PrimaryLower) :
    (halfPrimaryAssociateEquiv (j,a)).val=omega^j.val*a.val:=rfl

lemma halfPrimary_tsum (f:Eis→ℂ) :
    (∑'b:HalfPrimary,f b.val)=∑'p:Fin 3×PrimaryLower,f (omega^p.1.val*p.2.val) :=
  halfPrimaryAssociateEquiv.tsum_eq (fun b:HalfPrimary=>f b.val) |>.symm

end

open ActualEisensteinCubic CubicKubota ConcreteTraceCRT
local notation "Eis" => ActualEisensteinCubic.O

def unitCuspUpper (b : Eis) : SL(2,Eis) := ⟨!![1,b;0,1],by simp [Matrix.det_fin_two]⟩
def unitCuspDiagonal (u : Eisˣ) : SL(2,Eis) := ⟨!![(u:Eis),0;0,(↑u⁻¹:Eis)],by
  simp [Matrix.det_fin_two]⟩

theorem rational_cusp_lower_factor (u : Eisˣ) (n : ℤ) :
    rationalEmbedding ModularGroup.S*unitCuspUpper (n:Eis)*lowerCuspMatrix (u:Eis)=
      unitCuspDiagonal (-u)*lowerCuspMatrix (-(u:Eis)*(1+(n:Eis)*(u:Eis)))*
        unitCuspUpper (↑u⁻¹:Eis) := by
  apply Subtype.ext
  change ((!![(0 : ℤ), -1; 1, 0]).map (Int.castRingHom Eis) *
    !![1, (n : Eis); 0, 1] * !![1, 0; (u : Eis), 1]) =
    (!![(↑(-u) : Eis), 0; 0, (↑(-u)⁻¹ : Eis)] *
      !![1, 0; -(u : Eis) * (1 + (n : Eis) * (u : Eis)), 1] *
      !![1, (↑u⁻¹ : Eis); 0, 1])
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, neg_mul, Units.val_neg,
      mul_add, add_mul, mul_assoc, add_comm]

lemma unitCuspUpper_section (b : Eis) (z : ℂ) (v : ℝ) (hv : 0<v) :
    integralComplexMatrix (unitCuspUpper b)*upperSection z v hv=
      upperSection (z+eisEmbedding b) v hv := by
  apply Subtype.ext
  change ((!![1, b; 0, 1] : Matrix (Fin 2) (Fin 2) Eis).map eisEmbedding *
    !![(Real.sqrt v : ℂ), z / Real.sqrt v; 0, (Real.sqrt v : ℂ)⁻¹]) =
    !![(Real.sqrt v : ℂ), (z + eisEmbedding b) / Real.sqrt v;
      0, (Real.sqrt v : ℂ)⁻¹]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  ring

lemma unitCuspDiagonal_norm (u : Eisˣ) :
    ‖eisEmbedding (u:Eis)‖=1 ∧ ‖eisEmbedding (↑u⁻¹:Eis)‖=1 :=
  ⟨GaussGeneratorTransport.norm_eisEmbedding_unit u,
    GaussGeneratorTransport.norm_eisEmbedding_unit u⁻¹⟩

end CubicEisenstein

open scoped Classical MatrixGroups
namespace CubicEisenstein

section
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CubicKubota
local notation "Eis" => ActualEisensteinCubic.O

abbrev CubeResidueStrata (p:Eis) := Σj:Fin 4,CubicUnitResidue (p^(3-j.val))

def cubeResidueStratumMap (p:Eis) (x:CubeResidueStrata p) : Eis⧸Ideal.span {p^3} :=
  Ideal.Quotient.mk _ (p^x.1.val * GaussianShiftedPartition.representative (p^(3-x.1.val)) x.2.1)

private lemma unit_rep_coprime (c:Eis) (x:CubicUnitResidue c) :
    IsCoprime c (GaussianShiftedPartition.representative c x.1) := by
  apply (isUnit_quotient_span_iff c _).mp
  simpa only [GaussianShiftedPartition.representative_spec] using x.2

private lemma cube_strata_exponents (p:Eis) (hp:Prime p) (j k:Fin 4)
    (b d:Eis) (hb:IsCoprime (p^(3-j.val)) b)
    (he:p^3∣p^j.val*b-p^k.val*d) : ¬j.val<k.val := by
  intro hjk
  have hj3:j.val+1≤3:=by omega
  have hjk':j.val+1≤k.val:=by omega
  have h1:p^(j.val+1)∣p^j.val*b-p^k.val*d:=
    (pow_dvd_pow p hj3).trans he
  have h2:p^(j.val+1)∣p^k.val*d:=
    dvd_mul_of_dvd_left (pow_dvd_pow p hjk') d
  have h3:p^(j.val+1)∣p^j.val*b:=by
    simpa only [sub_add_cancel] using dvd_add h1 h2
  rw [pow_succ] at h3
  have hpb:p∣b:=(mul_dvd_mul_iff_left (pow_ne_zero j.val hp.ne_zero)).mp h3
  have hpc:IsCoprime p b:=hb.of_isCoprime_of_dvd_left
    (dvd_pow_self p (by omega:3-j.val≠0))
  exact (hp.coprime_iff_not_dvd.mp hpc) hpb

lemma cubeResidueStratumMap_injective (p:Eis) (hp:Prime p) :
    Function.Injective (cubeResidueStratumMap p) := by
  rintro ⟨j,b⟩ ⟨k,d⟩ he
  have hd:p^3∣p^j.val*GaussianShiftedPartition.representative (p^(3-j.val)) b.1-
      p^k.val*GaussianShiftedPartition.representative (p^(3-k.val)) d.1 :=
    Ideal.mem_span_singleton.mp ((Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp he)
  have hle:=cube_strata_exponents p hp j k _ _ (unit_rep_coprime _ b) hd
  have hge:=cube_strata_exponents p hp k j _ _ (unit_rep_coprime _ d)
    (by simpa only [neg_sub] using dvd_neg.mpr hd)
  have hjk:j=k:=Fin.ext (by omega)
  subst k
  have hpow:p^3=p^j.val*p^(3-j.val):=by rw [←pow_add,Nat.add_sub_of_le (by omega:j.val≤3)]
  rw [hpow,←mul_sub] at hd
  have hrep:p^(3-j.val)∣GaussianShiftedPartition.representative (p^(3-j.val)) b.1-
      GaussianShiftedPartition.representative (p^(3-j.val)) d.1:=
    (mul_dvd_mul_iff_left (pow_ne_zero j.val hp.ne_zero)).mp hd
  have hbd:b=d:=by
    apply Subtype.ext
    rw [←GaussianShiftedPartition.representative_spec (p^(3-j.val)) b.1,
      ←GaussianShiftedPartition.representative_spec (p^(3-j.val)) d.1]
    exact (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr (Ideal.mem_span_singleton.mpr hrep)
  subst d
  rfl

lemma cubeResidueStratumMap_surjective (p:Eis) (hp:Prime p) (hprimary:lambda^2∣p-1) :
    Function.Surjective (cubeResidueStratumMap p) := by
  intro r
  let a:=GaussianShiftedPartition.representative (p^3) r
  let A:SL(2,Eis):=⟨!![a,-1;1,0],by simp [Matrix.det_fin_two_of]⟩
  obtain ⟨j,hj,N,hx,hc,hNA,hjN,hupper⟩:=cube_average_cusp_reduction A p 0 hp hprimary
  have ha:a=p^j*N 0 0:=by simpa [A] using hx
  have hc':p^3=p^j*N 1 0:=by simpa [A] using hc
  have hpow:p^3=p^j*p^(3-j):=by rw [←pow_add,Nat.add_sub_of_le hj]
  have hN10:N 1 0=p^(3-j):=by
    apply mul_left_cancel₀ (pow_ne_zero j hp.ne_zero)
    exact hc'.symm.trans hpow
  have hcop:IsCoprime (p^(3-j)) (N 0 0):=by
    refine ⟨-N 0 1,N 1 1,?_⟩
    have hd:N 0 0*N 1 1-N 0 1*N 1 0=1:=by
      simpa only [Matrix.det_fin_two] using N.property
    rw [hN10] at hd
    linear_combination hd
  let b:CubicUnitResidue (p^(3-j)):=⟨Ideal.Quotient.mk _ (N 0 0),
    (isUnit_quotient_span_iff _ _).mpr hcop⟩
  refine ⟨⟨⟨j,by omega⟩,b⟩,?_⟩
  change Ideal.Quotient.mk (Ideal.span {p^3})
      (p^j*GaussianShiftedPartition.representative (p^(3-j)) b.1)=r
  rw [←GaussianShiftedPartition.representative_spec (p^3) r]
  apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr
  apply Ideal.mem_span_singleton.mpr
  change p^3∣p^j*GaussianShiftedPartition.representative (p^(3-j)) b.1-a
  rw [ha,←mul_sub,hpow]
  exact mul_dvd_mul_left (p^j) (gaussRep_mk_congr (p^(3-j)) (N 0 0))

def cubeResidueStrataEquiv (p:Eis) (hp:Prime p) (hprimary:lambda^2∣p-1) :
    CubeResidueStrata p≃(Eis⧸Ideal.span {p^3}) :=
  Equiv.ofBijective (cubeResidueStratumMap p)
    ⟨cubeResidueStratumMap_injective p hp,cubeResidueStratumMap_surjective p hp hprimary⟩

end

open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CubicKubota
local notation "Eis" => ActualEisensteinCubic.O

def cubeStratumSymbol (p C:Eis) (j:Fin 4) (b:CubicUnitResidue (p^(3-j.val))) : ℂ :=
  eisEmbedding (symbol (GaussianShiftedPartition.representative (p^(3-j.val)) b.1*C) (p^(3-j.val)))

lemma unit_stratum_symbol_gauss (p C:Eis) (hp:lambda^2∣p-1) (n:ℕ) :
    (∑' b:CubicUnitResidue (p^n),
      eisEmbedding (symbol (GaussianShiftedPartition.representative (p^n) b.1*C) (p^n))) =
      cubicUnitGaussSum 0 (p^n)*eisEmbedding (symbol C (p^n)) := by
  rw [cubicUnitGaussSum]
  simp only [mul_zero,residueAdditive,map_zero,cuspFrequency,zero_div,zero_mul,
    AddChar.map_zero_eq_one,mul_one]
  rw [←tsum_mul_right]
  apply tsum_congr
  intro b
  rw [symbol_mul_numerator _ _ _ (primary_pow_congruence p hp n),map_mul]

lemma cubeStratumSymbol_sum (p C:Eis) (hp:Prime p) (hprimary:lambda^2∣p-1)
    (hC:IsCoprime C p) (j:Fin 4) :
    (∑' b:CubicUnitResidue (p^(3-j.val)), cubeStratumSymbol p C j b) =
      if j=0 then (Ideal.absNorm (Ideal.span {p}):ℂ)^2*((Ideal.absNorm (Ideal.span {p}):ℂ)-1)
      else if j=3 then 1 else 0 := by
  have h3:eisEmbedding (symbol C (p^3))=1:=by
    rw [cubicSymbol_pow_denominator,symbol_cube_of_isCoprime C p hprimary hC,map_one]
  unfold cubeStratumSymbol
  rw [unit_stratum_symbol_gauss p C hprimary (3-j.val)]
  fin_cases j
  · have hh:=cubicUnitGaussSum_prime_power_zero p hp hprimary 2
    norm_num at hh ⊢
    rw [hh,h3,mul_one]
  · have hh:=cubicUnitGaussSum_prime_power_zero p hp hprimary 1
    norm_num at hh ⊢
    simp [hh]
  · have hh:=cubicUnitGaussSum_prime_power_zero p hp hprimary 0
    norm_num at hh ⊢
    simp [hh]
  · simp

lemma cubeStrata_weighted_sum (p C:Eis) (hp:Prime p) (hprimary:lambda^2∣p-1)
    (hC:IsCoprime C p) (w:Fin 4→ℂ) :
    (∑ j:Fin 4, w j * ∑' b:CubicUnitResidue (p^(3-j.val)), cubeStratumSymbol p C j b) =
      w 0*(Ideal.absNorm (Ideal.span {p}):ℂ)^2*((Ideal.absNorm (Ideal.span {p}):ℂ)-1)+w 3 := by
  simp_rw [cubeStratumSymbol_sum p C hp hprimary hC]
  simp [Fin.sum_univ_succ]
  ring

end CubicEisenstein

open scoped Classical MatrixGroups
namespace CubicKubota
open ActualEisensteinCubic ConcreteTraceCRT CubicEisenstein CubicJacobiGlobal CubicRamified
local notation "Eis" => ActualEisensteinCubic.O

lemma comparison_mod_three (A N:SL(2,Eis)) (hNA:N*A⁻¹∈levelThree) (i j:Fin 2) :
    (3:Eis)∣N i j-A i j := by
  have hh:Matrix.SpecialLinearGroup.map (n:=Fin 2)
      (Ideal.Quotient.mk (Ideal.span {(3:Eis)})) (N*A⁻¹)=1:=hNA
  rw [map_mul,map_inv] at hh
  have he:=mul_inv_eq_one.mp hh
  have he' :=congrArg (fun B:SL(2,Eis⧸Ideal.span {(3:Eis)})=>B i j) he
  exact Ideal.mem_span_singleton.mp ((Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp he')

lemma comparison_primary (A N:SL(2,Eis)) (hNA:N*A⁻¹∈levelThree)
    (hA:lambda^2∣A 0 0-1) : lambda^2∣N 0 0-1 := by
  have hh:=lambda_sq_dvd_three.trans (comparison_mod_three A N hNA 0 0)
  simpa only [sub_add_sub_cancel] using dvd_add hh hA

lemma comparison_levelTwo (A:levelTwo) (N:SL(2,Eis))
    (hNA:N*(A:SL(2,Eis))⁻¹∈levelThree) : N∈levelTwo := by
  have hh:=Subgroup.mul_mem levelTwo (levelThree_le_levelTwo hNA) A.property
  simpa only [inv_mul_cancel_right] using hh

lemma levelTwo_cube_zero_phase (A N:levelTwo) (p q:Eis)
    (hp:lambda^2∣p-1)
    (hA:lambda^2∣((A:SL(2,Eis)) 0 0)-1)
    (hN:lambda^2∣((N:SL(2,Eis)) 0 0)-1)
    (hx:(A:SL(2,Eis)) 0 0+3*q*(A:SL(2,Eis)) 1 0=(N:SL(2,Eis)) 0 0)
    (hc:(N:SL(2,Eis)) 1 0=p^3*(A:SL(2,Eis)) 1 0)
    (hNA:(N:SL(2,Eis))*(A:SL(2,Eis))⁻¹∈levelThree) :
    complexCharacter ⟨(N:SL(2,Eis))*(A:SL(2,Eis))⁻¹,hNA⟩=1 := by
  have hcop:IsCoprime ((N:SL(2,Eis)) 0 0) p:=by
    refine ⟨(N:SL(2,Eis)) 1 1,-(N:SL(2,Eis)) 0 1*p^2*(A:SL(2,Eis)) 1 0,?_⟩
    have hd:(N:SL(2,Eis)) 0 0*(N:SL(2,Eis)) 1 1-
        (N:SL(2,Eis)) 0 1*(N:SL(2,Eis)) 1 0=1:=by
      simpa only [Matrix.det_fin_two] using (N:SL(2,Eis)).property
    rw [hc] at hd
    linear_combination hd
  have hcube:eisEmbedding (symbol ((N:SL(2,Eis)) 0 0) p)^3=1:=by
    rw [←map_pow,symbol_cube_of_isCoprime _ _ hp hcop,map_one]
  have hb:=levelTwo_cube_phase_balance A N p q 0 hp hA hN (by simpa using hx) (by simpa using hc)
  simp only [pow_zero,mul_one,Nat.sub_zero,hcube] at hb
  have hcomp:=levelTwo_comparison_character A N hNA
  have hbase:levelTwoComplexCharacter A≠0:=by
    intro he
    have hh:=levelTwoComplexCharacter_cube A
    rw [he] at hh
    norm_num at hh
  apply mul_right_cancel₀ hbase
  rw [one_mul,hcomp,hb]

lemma cube_exponent_zero_of_lower_divisible (A N:SL(2,Eis)) (p q:Eis) (j:ℕ)
    (hp:Prime p) (hC:p∣A 1 0)
    (hx:A 0 0+3*q*A 1 0=p^j*N 0 0) : j=0 := by
  by_contra hj
  have hpx:p∣A 0 0+3*q*A 1 0:=by
    rw [hx]
    exact dvd_mul_of_dvd_left (dvd_pow_self p hj) (N 0 0)
  have hpa:p∣A 0 0:=by
    simpa only [add_sub_cancel_right] using dvd_sub hpx (dvd_mul_of_dvd_right hC (3*q))
  have hone:p∣(1:Eis):=by
    have hh:=dvd_sub (dvd_mul_of_dvd_left hpa (A 1 1)) (dvd_mul_of_dvd_right hC (A 0 1))
    have hd:A 0 0*A 1 1-A 0 1*A 1 0=1:=by
      simpa only [Matrix.det_fin_two] using A.property
    rwa [hd] at hh
  exact hp.not_isUnit (isUnit_of_dvd_one hone)

end CubicKubota

namespace CubicEisenstein
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CubicKubota
local notation "Eis" => ActualEisensteinCubic.O

lemma cube_affine_coefficient_unit (p C:Eis) (hprimary:lambda^2∣p-1) (hC:IsCoprime C p) :
    IsUnit (Ideal.Quotient.mk (Ideal.span {p^3}) (3*C)) := by
  obtain ⟨t,ht⟩:=(three_dvd_primary_sub_one p hprimary)
  have hp3:IsCoprime p (3:Eis):=by
    refine ⟨1,-t,?_⟩
    linear_combination ht
  apply (isUnit_quotient_span_iff _ _).mpr
  exact hp3.pow_left.mul_right hC.symm.pow_left

def cubeCuspAffineEquiv (p A C:Eis) (hprimary:lambda^2∣p-1) (hC:IsCoprime C p) :
    (Eis⧸Ideal.span {p^3})≃(Eis⧸Ideal.span {p^3}) := by
  let a:=Ideal.Quotient.mk (Ideal.span {p^3}) A
  let u:Units (Eis⧸Ideal.span {p^3}):=(cube_affine_coefficient_unit p C hprimary hC).unit
  exact {
    toFun:=fun r=>a+(u:_) * r
    invFun:=fun r=>(↑u⁻¹:_)*(r-a)
    left_inv:=by
      intro r
      simp only [add_sub_cancel_left,←mul_assoc,Units.inv_mul,one_mul]
    right_inv:=by
      intro r
      simp only [←mul_assoc,Units.mul_inv,one_mul,add_sub_cancel] }

lemma cubeCuspAffineEquiv_apply (p A C:Eis) (hprimary:lambda^2∣p-1) (hC:IsCoprime C p)
    (r:Eis⧸Ideal.span {p^3}) :
    cubeCuspAffineEquiv p A C hprimary hC r=
      Ideal.Quotient.mk (Ideal.span {p^3}) A+
        Ideal.Quotient.mk (Ideal.span {p^3}) (3*C)*r := by
  simp only [cubeCuspAffineEquiv,IsUnit.unit_spec]
  rfl

lemma cubeCuspAffineEquiv_mk (p A C q:Eis) (hprimary:lambda^2∣p-1) (hC:IsCoprime C p) :
    cubeCuspAffineEquiv p A C hprimary hC (Ideal.Quotient.mk _ q)=
      Ideal.Quotient.mk (Ideal.span {p^3}) (A+3*q*C) := by
  rw [cubeCuspAffineEquiv_apply]
  simp only [map_add,map_mul]
  ring

end CubicEisenstein

open scoped Classical MatrixGroups BigOperators
namespace CubicKubota
open ActualEisensteinCubic ConcreteTraceCRT CubicEisenstein CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O

structure CubeCuspData (A:SL(2,Eis)) (p q:Eis) where
  exponent : Fin 4
  matrix : SL(2,Eis)
  first : A 0 0+3*q*A 1 0=p^exponent.val*matrix 0 0
  second : p^3*A 1 0=p^exponent.val*matrix 1 0
  congruent : matrix*A⁻¹∈levelThree

def actualCubeCuspData (A:SL(2,Eis)) (p q:Eis) (hp:Prime p) (hprimary:lambda^2∣p-1) :
    CubeCuspData A p q := by
  let h:=cube_average_cusp_reduction A p q hp hprimary
  let j:=Classical.choose h
  have hj:j≤3:=(Classical.choose_spec h).1
  let N:=Classical.choose (Classical.choose_spec h).2
  have hN:=(Classical.choose_spec (Classical.choose_spec h).2)
  exact ⟨⟨j,by omega⟩,N,hN.1,hN.2.1,hN.2.2.1⟩

namespace CubeCuspData
variable {A:SL(2,Eis)} {p q:Eis}

lemma lower_eq (d:CubeCuspData A p q) (hp:p≠0) :
    d.matrix 1 0=p^(3-d.exponent.val)*A 1 0 := by
  apply mul_left_cancel₀ (pow_ne_zero d.exponent.val hp)
  rw [←d.second,←mul_assoc,←pow_add,Nat.add_sub_of_le (by omega:d.exponent.val≤3)]

lemma unit_top (d:CubeCuspData A p q) (hp:p≠0) :
    IsUnit (Ideal.Quotient.mk (Ideal.span {p^(3-d.exponent.val)}) (d.matrix 0 0)) := by
  apply (isUnit_quotient_span_iff _ _).mpr
  refine ⟨-d.matrix 0 1*A 1 0,d.matrix 1 1,?_⟩
  have hd:d.matrix 0 0*d.matrix 1 1-d.matrix 0 1*d.matrix 1 0=1:=by
    simpa only [Matrix.det_fin_two] using d.matrix.property
  rw [d.lower_eq hp] at hd
  linear_combination hd

def stratum (d:CubeCuspData A p q) (hp:p≠0) : CubeResidueStrata p :=
  ⟨d.exponent,⟨Ideal.Quotient.mk _ (d.matrix 0 0),d.unit_top hp⟩⟩

lemma stratum_map (d:CubeCuspData A p q) (hp:p≠0) :
    cubeResidueStratumMap p (d.stratum hp)=
      Ideal.Quotient.mk (Ideal.span {p^3}) (A 0 0+3*q*A 1 0) := by
  apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr
  apply Ideal.mem_span_singleton.mpr
  change p^3∣p^d.exponent.val*GaussianShiftedPartition.representative
    (p^(3-d.exponent.val)) (Ideal.Quotient.mk _ (d.matrix 0 0))-(A 0 0+3*q*A 1 0)
  rw [d.first,←mul_sub]
  have hpow:p^3=p^d.exponent.val*p^(3-d.exponent.val):=by
    rw [←pow_add,Nat.add_sub_of_le (by omega:d.exponent.val≤3)]
  rw [hpow]
  exact mul_dvd_mul_left _ (gaussRep_mk_congr _ _)

lemma comparison_phase (A2:levelTwo) (d:CubeCuspData (A2:SL(2,Eis)) p q)
    (hp:Prime p) (hprimary:lambda^2∣p-1)
    (hA:lambda^2∣((A2:SL(2,Eis)) 0 0)-1)
    (hC:IsCoprime ((A2:SL(2,Eis)) 1 0) p) :
    complexCharacter ⟨d.matrix*(A2:SL(2,Eis))⁻¹,d.congruent⟩ =
      cubeStratumSymbol p ((A2:SL(2,Eis)) 1 0) d.exponent (d.stratum hp.ne_zero).2 := by
  let N2:levelTwo:=⟨d.matrix,comparison_levelTwo A2 d.matrix d.congruent⟩
  have hN:lambda^2∣d.matrix 0 0-1:=comparison_primary _ _ d.congruent hA
  have he:=levelTwo_cube_comparison_phase A2 N2 p q d.exponent.val
    (by omega:d.exponent.val≤3) hprimary hA hN d.first (d.lower_eq hp.ne_zero) hC d.congruent
  rw [he]
  unfold cubeStratumSymbol
  rw [←map_pow,←cubicSymbol_pow_denominator]
  apply congrArg eisEmbedding
  apply symbol_congr
  have hd:=gaussRep_mk_congr (p^(3-d.exponent.val)) (d.matrix 0 0)
  change p^(3-d.exponent.val)∣d.matrix 0 0*((A2:SL(2,Eis)) 1 0)-
    GaussianShiftedPartition.representative (p^(3-d.exponent.val))
      (Ideal.Quotient.mk _ (d.matrix 0 0))*((A2:SL(2,Eis)) 1 0)
  convert dvd_mul_of_dvd_left (dvd_neg.mpr hd) ((A2:SL(2,Eis)) 1 0) using 1 ; ring

end CubeCuspData
end CubicKubota

end

end OAI
