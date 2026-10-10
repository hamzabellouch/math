import OAI.NumberTheory.DirichletL.GaussSum.DualKernelSummability
import OAI.NumberTheory.DirichletL.GaussSum.BesselReflection

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

namespace CompletedGauss
open Filter MeasureTheory
open scoped Classical BigOperators Topology ContDiff

open CubicEisenstein

lemma positive_cpow_comp_continuous (r : ℝ) (hr : 0<r)
    (f : ℝ→ℂ) (hf : Continuous f) : Continuous (fun t=>(r:ℂ)^(f t)) := by
  let : NeZero (r:ℂ) := ⟨Complex.ofReal_ne_zero.mpr hr.ne'⟩
  exact (_root_.continuous_const_cpow (r:ℂ)).comp hf

theorem besselSmoothingIntegrand_reflected_integrable {α : Type*} [Countable α]
    (F : ℝ→ℂ) (r : α→ℝ) (hr : ∀i,0<r i) (a : α→ℂ)
    (q d Q : ℝ) (hq : 0<q) (hd : 0<d) (hQ : 0<Q) (A : ℂ)
    (hreflect : ∀v : ℝ,0<v→F v=
      A*((v:ℂ)^(-2:ℂ)*radialBesselProfile r a d ((Q*v)⁻¹)))
    (has : Summable (fun i=>‖a i‖*(r i)^(-(3/2:ℝ))))
    (V : ℝ→ℂ) (v0 v1 : ℝ) (hv0 : 0<v0)
    (hVs : Function.support V⊆Set.Icc v0 v1) (hV : ContDiff ℝ ∞ V)
    (X : ℝ) (hX : 0<X) :
    Integrable (fun t : ℝ=>besselSmoothingIntegrand F q V X ((-1:ℂ)+t*Complex.I)) := by
  let P : ℝ→ℂ := fun t=>
    A*(Q:ℂ)^(2-2*((-1:ℂ)+t*Complex.I))*
      besselReflectionFactor q d ((-1:ℂ)+t*Complex.I)*
        (X:ℂ)^(((-1:ℂ)+t*Complex.I)-1/2)
  let D : ℝ→ℂ := fun t=>∑'i,a i*(r i:ℂ)^(-((3/2:ℂ)+(-t)*Complex.I))
  let K : ℝ→ℂ := fun t=>CubicReflectionKernel.mellinEulerData V 0 ((3/2:ℂ)+(-t)*Complex.I)
  have hK : Integrable K := by
    have hh := CubicReflectionKernel.mellinEulerData_vertical_integrable V v0 v1 hv0 hVs hV
      2 0 (3/2) (by norm_num)
    simpa only [K,Complex.ofReal_div,Complex.ofReal_ofNat,Complex.ofReal_neg] using hh.comp_neg
  have hD : Continuous D := by
    have hh := (weighted_vertical_series_continuous r hr a (3/2) has).comp continuous_neg
    simpa only [D,Function.comp_def,Complex.ofReal_div,Complex.ofReal_ofNat,Complex.ofReal_neg] using hh
  have hDb (t : ℝ) : ‖D t‖≤∑'i,‖a i‖*(r i)^(-(3/2:ℝ)) := by
    simpa only [D,Complex.ofReal_div,Complex.ofReal_ofNat,Complex.ofReal_neg] using
      weighted_vertical_series_norm r hr a (3/2) has (-t)
  have hP : Continuous P := by
    have h1 := positive_cpow_comp_continuous Q hQ
      (fun t : ℝ=>2-2*((-1:ℂ)+t*Complex.I)) (by fun_prop)
    have h2 := positive_cpow_comp_continuous (4*Real.pi*q) (by positivity)
      (fun t : ℝ=>2*((-1:ℂ)+t*Complex.I)+1) (by fun_prop)
    have h3 := positive_cpow_comp_continuous 2 (by norm_num)
      (fun t : ℝ=>2-4*((-1:ℂ)+t*Complex.I)) (by fun_prop)
    have h4 := positive_cpow_comp_continuous (4*Real.pi*d) (by positivity)
      (fun t : ℝ=>3-2*((-1:ℂ)+t*Complex.I)) (by fun_prop)
    have h5 := positive_cpow_comp_continuous X hX
      (fun t : ℝ=>((-1:ℂ)+t*Complex.I)-1/2) (by fun_prop)
    have hn (t : ℝ) : (((4*Real.pi*d:ℝ):ℂ)^(3-2*((-1:ℂ)+t*Complex.I)))≠0 :=
      Complex.cpow_ne_zero_iff.mpr (Or.inl (Complex.ofReal_ne_zero.mpr (by positivity)))
    convert (((continuous_const (y:=A)).mul h1).mul ((h2.mul h3).div h4 hn)).mul h5 using 1 ;
      (ext t; simp only [P,besselReflectionFactor,Pi.mul_apply,Pi.div_apply,Complex.ofReal_ofNat])
  have hPn (t : ℝ) : ‖P t‖=‖P 0‖ := by
    simp only [P,norm_mul,besselReflectionFactor_norm q d hq hd,
      Complex.norm_cpow_eq_rpow_re_of_pos hQ,Complex.norm_cpow_eq_rpow_re_of_pos hX]
    norm_num
  have hi := (hK.mul_bdd hP.aestronglyMeasurable
    (Eventually.of_forall (fun t=>(hPn t).le))).mul_bdd hD.aestronglyMeasurable
      (Eventually.of_forall hDb)
  apply hi.congr
  filter_upwards with t
  have he : ((-1:ℂ)+t*Complex.I).re-1/2=-(3/2:ℝ) := by norm_num
  have hsum : Summable (fun i=>‖a i‖*(r i)^(((-1:ℂ)+t*Complex.I).re-1/2)) := by
    simpa only [he] using has
  have href := continuedBesselDirichlet_reflection F r hr a q d Q hd hQ A hreflect
    ((-1:ℂ)+t*Complex.I) (by norm_num) hsum
  change K t*P t*D t=besselSmoothingIntegrand F q V X ((-1:ℂ)+t*Complex.I)
  rw [besselSmoothingIntegrand,href]
  dsimp only [K,P,D]
  unfold CubicReflectionKernel.mellinEulerData CubicReflectionKernel.mellinData
  simp only [pow_zero,one_mul]
  have he1 : (1/2:ℂ)-((-1:ℂ)+t*Complex.I)=(3/2:ℂ)+(-t)*Complex.I := by ring
  have he2 : ((-1:ℂ)+t*Complex.I)-1/2=-((3/2:ℂ)+(-t)*Complex.I) := by ring
  rw [he1,he2]
  ring

end CompletedGauss

namespace CubicEisenstein

section
open scoped BigOperators Classical
open MeasureTheory
open Finset AddChar MulChar EisensteinEmbedding

section
local notation "Eis" => ActualEisensteinCubic.O

def finiteTranslationMultiplier {ι : Type*} [Fintype ι]
    (shift weight : ι→ℂ) (h : Eis) : ℂ :=
  ∑i,weight i*ShortDraftTrace.breveE (cuspFrequency h*shift i)

lemma finiteTranslationMultiplier_norm {ι : Type*} [Fintype ι]
    (shift weight : ι→ℂ) (h : Eis) :
    ‖finiteTranslationMultiplier shift weight h‖≤∑i,‖weight i‖ := by
  unfold finiteTranslationMultiplier
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i hi
  rw [norm_mul,breveE_norm,mul_one]

namespace SubexponentialBesselCoefficients

def finiteTranslate {ι : Type*} [Fintype ι] (coeff : SubexponentialBesselCoefficients)
    (shift weight : ι→ℂ) : SubexponentialBesselCoefficients where
  value h := finiteTranslationMultiplier shift weight h*coeff.value h
  growth epsilon he := by
    obtain ⟨C,hC,hbound⟩:=coeff.growth epsilon he
    refine ⟨(∑i,‖weight i‖)*C,by positivity,?_⟩
    intro h hh
    rw [norm_mul]
    calc
      _ ≤ (∑i,‖weight i‖)*(C*Real.exp (epsilon*‖cuspFrequency h‖)) :=
        mul_le_mul (finiteTranslationMultiplier_norm shift weight h) (hbound h hh)
          (norm_nonneg _) (Finset.sum_nonneg (fun _ _=>norm_nonneg _))
      _ = _ := by ring

lemma term_horizontal_translate (coeff : SubexponentialBesselCoefficients)
    (h : Eis) (v : ℝ) (z a : ℂ) :
    coeff.term h (v,z+a)=ShortDraftTrace.breveE (cuspFrequency h*a)*coeff.term h (v,z) := by
  by_cases hh:h=0
  · simp only [term,ite_eq_left hh,mul_zero]
  · simp only [term,ite_eq_right hh,mul_add,AddChar.map_add_eq_mul]
    ring

lemma finiteTranslate_term {ι : Type*} [Fintype ι]
    (coeff : SubexponentialBesselCoefficients) (shift weight : ι→ℂ)
    (h : Eis) (v : ℝ) (z : ℂ) :
    (coeff.finiteTranslate shift weight).term h (v,z)=
      ∑i,weight i*coeff.term h (v,z+shift i) := by
  simp_rw [term_horizontal_translate]
  rw [show (∑i,weight i*(ShortDraftTrace.breveE (cuspFrequency h*shift i)*coeff.term h (v,z)))=
      finiteTranslationMultiplier shift weight h*coeff.term h (v,z) by
    simp only [finiteTranslationMultiplier,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    ring]
  by_cases hh:h=0
  · simp only [term,ite_eq_left hh,mul_zero]
  · simp only [term,ite_eq_right hh,finiteTranslate]
    ring

theorem finiteTranslate_series {ι : Type*} [Fintype ι]
    (coeff : SubexponentialBesselCoefficients) (shift weight : ι→ℂ)
    (v : ℝ) (hv : 0<v) (z : ℂ) :
    (coeff.finiteTranslate shift weight).series (v,z)=
      ∑i,weight i*coeff.series (v,z+shift i) := by
  simp only [series,finiteTranslate_term]
  rw [Summable.tsum_finsetSum (fun i hi=>(coeff.summable (v,z+shift i) hv).mul_left (weight i))]
  apply Finset.sum_congr rfl
  intro i hi
  exact tsum_mul_left

theorem finiteTranslate_fullFunction {ι : Type*} [Fintype ι]
    (coeff : SubexponentialBesselCoefficients) (shift weight : ι→ℂ) (constant : ℂ)
    (v : ℝ) (hv : 0<v) (z : ℂ) :
    (coeff.finiteTranslate shift weight).fullFunction ((∑i,weight i)*constant) (upperPoint z v hv)=
      ∑i,weight i*coeff.fullFunction constant (upperPoint (z+shift i) v hv) := by
  simp only [fullFunction,function,hyperbolicHeight_upperPoint,hyperbolicHorizontal_upperPoint,
    finiteTranslate_series coeff shift weight v hv,Finset.sum_mul,mul_add,
    Finset.sum_add_distrib]
  have hconst : (∑i,weight i*constant*(v:ℂ)^(2/3:ℂ))=
      ∑i,constant*(v:ℂ)^(2/3:ℂ)*weight i := by
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hconst]
  ring_nf

end SubexponentialBesselCoefficients

theorem cubicSource_finite_translation {ι : Type*} [Fintype ι]
    (shift weight : ι→ℂ) (v : ℝ) (hv : 0<v) (z : ℂ) :
    (∑i,weight i*cubicSourceResidualFunction (upperPoint (z+shift i) v hv))=
      (sourceBesselCoefficients.finiteTranslate shift weight).fullFunction
        ((∑i,weight i)*((3*(Real.pi:ℂ))*constantArithmeticResidue)) (upperPoint z v hv) := by
  simp only [cubicSourceResidualFunction_eq_bessel,sourceBesselFunction]
  exact (sourceBesselCoefficients.finiteTranslate_fullFunction shift weight _ v hv z).symm

end

section
local notation "Eis" => ActualEisensteinCubic.O

def finiteAdditiveFourierCoeff {R : Type*} [CommRing R] [Fintype R]
    (ψ : AddChar R ℂ) (φ : R→ℂ) (h : R) : ℂ :=
  (∑x,φ x*ψ (-h*x))/(Fintype.card R:ℂ)

lemma finiteAdditiveFourier_inversion {R : Type*} [CommRing R] [Fintype R]
    (ψ : AddChar R ℂ) (hψ : ψ.IsPrimitive) (φ : R→ℂ) (x : R) :
    (∑h,finiteAdditiveFourierCoeff ψ φ h*ψ (h*x))=φ x := by
  have hN : (Fintype.card R:ℂ)≠0:=by exact_mod_cast Fintype.card_ne_zero
  calc
    _ = (∑h,∑y,φ y*ψ (-h*y)*ψ (h*x))/(Fintype.card R:ℂ) := by
      simp only [finiteAdditiveFourierCoeff,div_mul_eq_mul_div,Finset.sum_mul,Finset.sum_div]
    _ = (∑y,φ y*∑h,ψ (h*(x-y)))/(Fintype.card R:ℂ) := by
      rw [Finset.sum_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro y hy
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro h hh
      rw [mul_assoc,←AddChar.map_add_eq_mul]
      congr 2
      ring
    _ = (∑y,φ y*(if x-y=0 then (Fintype.card R:ℂ) else 0))/(Fintype.card R:ℂ) := by
      simp only [AddChar.sum_mulShift _ hψ,apply_ite,Nat.cast_zero]
    _ = φ x := by
      have he : (∑y,φ y*(if x-y=0 then (Fintype.card R:ℂ) else 0))=
          φ x*(Fintype.card R:ℂ) := by
        simp [sub_eq_zero]
      rw [he,mul_div_cancel_right₀ _ hN]

lemma finiteAdditiveFourierCoeff_norm {R : Type*} [CommRing R] [Fintype R]
    (ψ : AddChar R ℂ) (φ : R→ℂ) (hφ : ∀x,‖φ x‖≤1) (h : R) :
    ‖finiteAdditiveFourierCoeff ψ φ h‖≤1 := by
  have hN : (0:ℝ)<Fintype.card R:=by exact_mod_cast Fintype.card_pos
  rw [finiteAdditiveFourierCoeff,norm_div,Complex.norm_natCast]
  apply (div_le_one hN).mpr
  calc
    _ ≤ ∑x,‖φ x*ψ (-h*x)‖ := norm_sum_le _ _
    _ ≤ ∑_x : R,(1:ℝ) := by
      apply Finset.sum_le_sum
      intro x hx
      simpa only [norm_mul,AddChar.norm_apply,mul_one] using hφ x
    _ = _ := by simp

def thetaFourierTranslation (c : Eis) (h : Eis⧸Ideal.span {c}) : ℂ :=
  ConcreteTraceCRT.eisLam^2*ConcreteTraceCRT.eisEmbedding (Quotient.out h)/
    ConcreteTraceCRT.eisEmbedding c

lemma thetaFourierTranslation_phase (c : Eis) (hc : c≠0)
    (h : Eis⧸Ideal.span {c}) (x : Eis) :
    ShortDraftTrace.breveE (-cuspFrequency x*thetaFourierTranslation c h)=
      quotientTrace c hc (h*Ideal.Quotient.mk _ x) := by
  have hm : h*Ideal.Quotient.mk _ x=Ideal.Quotient.mk _ (Quotient.out h*x) := by
    rw [map_mul,Ideal.Quotient.mk_out]
  rw [hm]
  simp only [quotientTrace,ConcreteTraceCRT.eisTraceModChar,IdealGaussCRT.traceModChar_mk]
  congr 1
  unfold cuspFrequency thetaFourierTranslation
  rw [map_mul]
  have hc0:=ConcreteTraceCRT.eisEmbedding_ne_zero hc
  have hl:=ConcreteTraceCRT.eisLam_ne_zero
  field_simp
  linear_combination -(ConcreteTraceCRT.eisEmbedding x*
    ConcreteTraceCRT.eisEmbedding (Quotient.out h))*TraceLambdaPhase.eisLam_sq

lemma thetaFourierTranslation_inversion (c : Eis) (hc : c≠0)
    [Fintype (Eis⧸Ideal.span {c})] (φ : (Eis⧸Ideal.span {c})→ℂ) (x : Eis) :
    (∑h,finiteAdditiveFourierCoeff (quotientTrace c hc) φ h*
      ShortDraftTrace.breveE (-cuspFrequency x*thetaFourierTranslation c h))=
      φ (Ideal.Quotient.mk _ x) := by
  simp only [thetaFourierTranslation_phase c hc]
  exact finiteAdditiveFourier_inversion (quotientTrace c hc)
    (GeneralPrimitiveTrace.eisTraceModChar_breveE_primitive c hc) φ _

end

section
local notation "Eis" => ActualEisensteinCubic.O

lemma breveE_star (z : ℂ) : star (ShortDraftTrace.breveE z)=ShortDraftTrace.breveE (-z) := by
  change (starRingEnd ℂ) (Complex.exp (2*Real.pi*Complex.I*(z+starRingEnd ℂ z)))=
    Complex.exp (2*Real.pi*Complex.I*((-z)+starRingEnd ℂ (-z)))
  rw [←Complex.exp_conj]
  congr 1
  simp only [map_mul,map_add,map_neg,map_ofNat,Complex.conj_ofReal,Complex.conj_I,
    starRingEnd_self_apply]
  ring

lemma finiteTranslationMultiplier_star {ι : Type*} [Fintype ι]
    (shift weight : ι→ℂ) (h : Eis) :
    star (finiteTranslationMultiplier shift (fun i=>star (weight i)) h)=
      ∑i,weight i*ShortDraftTrace.breveE (-cuspFrequency h*shift i) := by
  simp only [finiteTranslationMultiplier,star_sum,star_mul,star_star,breveE_star,neg_mul]
  apply Finset.sum_congr rfl
  intro i hi
  ring

lemma finiteTranslate_term_multiplier {ι : Type*} [Fintype ι]
    (coeff : SubexponentialBesselCoefficients) (shift weight : ι→ℂ)
    (h : Eis) (v : ℝ) (z : ℂ) :
    (coeff.finiteTranslate shift weight).term h (v,z)=
      finiteTranslationMultiplier shift weight h*coeff.term h (v,z) := by
  by_cases hh:h=0
  · simp only [SubexponentialBesselCoefficients.term,ite_eq_left hh,mul_zero]
  · simp only [SubexponentialBesselCoefficients.term,ite_eq_right hh,
      SubexponentialBesselCoefficients.finiteTranslate]
    ring

def finiteConjugateSource {ι : Type*} [Fintype ι]
    (shift weight : ι→ℂ) (v : ℝ) (hv : 0<v) (z : ℂ) : ℂ :=
  ∑i,weight i*cubicSourceConjugateFunction (upperPoint (z+shift i) v hv)

lemma finiteConjugateSource_eq_bessel {ι : Type*} [Fintype ι]
    (shift weight : ι→ℂ) (v : ℝ) (hv : 0<v) (z : ℂ) :
    finiteConjugateSource shift weight v hv z=
      star ((sourceBesselCoefficients.finiteTranslate shift (fun i=>star (weight i))).fullFunction
        ((∑i,star (weight i))*((3*(Real.pi:ℂ))*constantArithmeticResidue)) (upperPoint z v hv)) := by
  rw [sourceBesselCoefficients.finiteTranslate_fullFunction]
  simp only [star_sum,star_mul,star_star,finiteConjugateSource,cubicSourceConjugateFunction,
    cubicSourceResidualFunction_eq_bessel,sourceBesselFunction]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem finiteConjugateSource_wirtingerBar {ι : Type*} [Fintype ι]
    (shift weight : ι→ℂ) (v : ℝ) (hv : 0<v) (z : ℂ) :
    horizontalWirtingerBar (finiteConjugateSource shift weight v hv) z=
      ∑'h : Eis,(-2*Real.pi*Complex.I*star (cuspFrequency h))*
        (∑i,weight i*ShortDraftTrace.breveE (-cuspFrequency h*shift i))*
          star (sourceBesselCoefficients.term h (v,z)) := by
  have hf : finiteConjugateSource shift weight v hv = fun z=>
      star ((sourceBesselCoefficients.finiteTranslate shift (fun i=>star (weight i))).fullFunction
        ((∑i,star (weight i))*((3*(Real.pi:ℂ))*constantArithmeticResidue)) (upperPoint z v hv)) :=
    funext (finiteConjugateSource_eq_bessel shift weight v hv)
  rw [hf,horizontalWirtingerBar_star,
    SubexponentialBesselCoefficients.fullFunction_wirtingerZ,tsum_star]
  apply tsum_congr
  intro h
  rw [finiteTranslate_term_multiplier,star_mul,star_mul,finiteTranslationMultiplier_star]
  have hphase : star (2*Real.pi*Complex.I*cuspFrequency h)=
      -2*Real.pi*Complex.I*star (cuspFrequency h) := by
    simp only [star_mul,Complex.star_def,map_ofNat,Complex.conj_ofReal,Complex.conj_I]
    ring
  rw [hphase]
  ring

def traceTwistedConjugateSource (c : Eis) (hc : c≠0)
    [Fintype (Eis⧸Ideal.span {c})] (φ : (Eis⧸Ideal.span {c})→ℂ)
    (v : ℝ) (hv : 0<v) (z : ℂ) : ℂ :=
  finiteConjugateSource (thetaFourierTranslation c)
    (finiteAdditiveFourierCoeff (quotientTrace c hc) φ) v hv z

theorem traceTwistedConjugateSource_wirtingerBar (c : Eis) (hc : c≠0)
    [Fintype (Eis⧸Ideal.span {c})] (φ : (Eis⧸Ideal.span {c})→ℂ)
    (v : ℝ) (hv : 0<v) (z : ℂ) :
    horizontalWirtingerBar (traceTwistedConjugateSource c hc φ v hv) z=
      ∑'h : Eis,(-2*Real.pi*Complex.I*star (cuspFrequency h))*
        φ (Ideal.Quotient.mk _ h)*star (sourceBesselCoefficients.term h (v,z)) := by
  change horizontalWirtingerBar (finiteConjugateSource (thetaFourierTranslation c)
    (finiteAdditiveFourierCoeff (quotientTrace c hc) φ) v hv) z = _
  rw [finiteConjugateSource_wirtingerBar]
  simp only [thetaFourierTranslation_inversion c hc]

theorem traceTwistedConjugateSource_wirtingerBar_zero (c : Eis) (hc : c≠0)
    [Fintype (Eis⧸Ideal.span {c})] (φ : (Eis⧸Ideal.span {c})→ℂ)
    (v : ℝ) (hv : 0<v) :
    horizontalWirtingerBar (traceTwistedConjugateSource c hc φ v hv) 0=
      ∑'h : Eis,(-2*Real.pi*Complex.I*star (cuspFrequency h))*
        φ (Ideal.Quotient.mk _ h)*star (sourceResidualFourierCoefficient h)*
          (v:ℂ)*schlafliBesselK (1/3) (4*Real.pi*‖cuspFrequency h‖*v) := by
  rw [traceTwistedConjugateSource_wirtingerBar]
  apply tsum_congr
  intro h
  by_cases hh:h=0
  · subst h
    simp [cuspFrequency]
  · rw [sourceBesselCoefficients.term_bessel h hh v hv]
    have hx : 0<4*Real.pi*‖cuspFrequency h‖*v :=
      mul_pos (mul_pos (mul_pos (by norm_num) Real.pi_pos)
        (norm_pos_iff.mpr (cuspFrequency_ne_zero h hh))) hv
    rw [schlafliBesselK_cubic_real _ hx]
    have he0 : ShortDraftTrace.breveE (0:ℂ)=1 := by
      simp [ShortDraftTrace.breveE]
    simp only [mul_zero,he0,mul_one,star_mul,
      Complex.star_def,Complex.conj_ofReal,sourceBesselCoefficients]
    ring

end

open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CompletedGauss
local notation "Eis" => ActualEisensteinCubic.O

def fixedThetaTwist (Ψ : Eis→*ℂ) (x : Eis) : ℂ :=
  if lambda^2∣x-1 then eisEmbedding (symbol ramifiedTraceLambda x)*Ψ x else 0

lemma fixedThetaTwist_primary (Ψ : Eis→*ℂ) (x : Eis) (hx : lambda^2∣x-1) :
    fixedThetaTwist Ψ x=eisEmbedding (symbol ramifiedTraceLambda x)*Ψ x := by
  simp only [fixedThetaTwist,ite_eq_left hx]

lemma fixedThetaTwist_not_primary (Ψ : Eis→*ℂ) (x : Eis) (hx : ¬lambda^2∣x-1) :
    fixedThetaTwist Ψ x=0 := by
  simp only [fixedThetaTwist,ite_eq_right hx]

lemma paperLambda_symbol_cube (x : Eis) (hx : lambda^2∣x-1) :
    (eisEmbedding (symbol ramifiedTraceLambda x))^3=1 := by
  rw [←map_pow,symbol_cube_of_isCoprime _ _ hx
    (ramified_character_coprime 0 1 _ x (Or.inl (by simp)) hx),map_one]

lemma paperLambda_symbol_norm (x : Eis) (hx : lambda^2∣x-1) :
    ‖eisEmbedding (symbol ramifiedTraceLambda x)‖=1 := by
  apply (pow_left_inj₀ (norm_nonneg _) zero_le_one (by decide : (3:ℕ)≠0)).mp
  simpa only [norm_pow,norm_one,one_pow] using congrArg norm (paperLambda_symbol_cube x hx)

lemma fixedThetaTwist_norm_le_one (Ψ : Eis→*ℂ) (hΨ : ∀x,‖Ψ x‖≤1) (x : Eis) :
    ‖fixedThetaTwist Ψ x‖≤1 := by
  by_cases hx : lambda^2∣x-1
  · rw [fixedThetaTwist_primary Ψ x hx,norm_mul,paperLambda_symbol_norm x hx,one_mul]
    exact hΨ x
  · rw [fixedThetaTwist_not_primary Ψ x hx,norm_zero]
    norm_num

theorem fixedThetaTwist_periodic (Ψ : Eis→*ℂ) (Q : Ideal Eis)
    (hΨ : CanonicalCoefficientClass.FactorsModulo Q Ψ) (x y : Eis)
    (hxy : x-y∈Ideal.span {(9:Eis)}*Q) : fixedThetaTwist Ψ x=fixedThetaTwist Ψ y := by
  have h9 : (9:Eis)∣x-y := Ideal.mem_span_singleton.mp (Ideal.mul_le_left hxy)
  have hd : lambda^2∣x-y := lambda_sq_dvd_three.trans ((show (3:Eis)∣9 from ⟨3,by norm_num⟩).trans h9)
  have hp : lambda^2∣x-1 ↔ lambda^2∣y-1 := by
    constructor
    · intro hx
      convert dvd_sub hx hd using 1 ; ring
    · intro hy
      convert dvd_add hd hy using 1 ; ring
  by_cases hx : lambda^2∣x-1
  · have hy := hp.mp hx
    rw [fixedThetaTwist_primary Ψ x hx,fixedThetaTwist_primary Ψ y hy,
      hΨ x y (Ideal.mul_le_right hxy)]
    congr 2
    exact CubicRamified.symbol_traceLambda_congr_mod_nine x y hx hy h9
  · rw [fixedThetaTwist_not_primary Ψ x hx,
      fixedThetaTwist_not_primary Ψ y (fun hy=>hx (hp.mpr hy))]

def fixedThetaQuotient (Ψ : Eis→*ℂ) (c : Eis) (x : Eis⧸Ideal.span {c}) : ℂ :=
  fixedThetaTwist Ψ (Quotient.out x)

lemma fixedThetaQuotient_mk (Ψ : Eis→*ℂ) (Q : Ideal Eis)
    (hΨ : CanonicalCoefficientClass.FactorsModulo Q Ψ) (c : Eis)
    (hc : Ideal.span {c}≤Ideal.span {(9:Eis)}*Q) (x : Eis) :
    fixedThetaQuotient Ψ c (Ideal.Quotient.mk _ x)=fixedThetaTwist Ψ x := by
  apply fixedThetaTwist_periodic Ψ Q hΨ
  exact hc (Ideal.Quotient.eq.mp (Ideal.Quotient.mk_out (Ideal.Quotient.mk (Ideal.span {c}) x)))

lemma fixedThetaQuotient_norm_le_one (Ψ : Eis→*ℂ) (hΨ : ∀x,‖Ψ x‖≤1)
    (c : Eis) (x : Eis⧸Ideal.span {c}) : ‖fixedThetaQuotient Ψ c x‖≤1 :=
  fixedThetaTwist_norm_le_one Ψ hΨ _

lemma paperLambda_symbol_squarefree_cube (n b : Eis) (hb : lambda^2∣b-1) :
    eisEmbedding (symbol ramifiedTraceLambda (n*b^3))=
      eisEmbedding (symbol ramifiedTraceLambda n) := by
  rw [symbol_mul_denominator,cubicSymbol_pow_denominator,map_mul,map_pow,
    paperLambda_symbol_cube b hb,mul_one]

theorem fixedThetaTwist_infinity_coefficient (Ψ : Eis→*ℂ) (I J : Ideal Eis)
    (hI : primaryGenerator I≠0) (hJ : primaryGenerator J≠0) (hsq : Squarefree I) :
    infinityCoefficientScalar⁻¹ *
      star (sourceResidualFourierCoefficient (primaryGenerator I*(primaryGenerator J)^3))*
        fixedThetaTwist Ψ (primaryGenerator I*(primaryGenerator J)^3)=
      (‖eisEmbedding (primaryGenerator J)‖:ℂ)*gaussTwo I hI*
        Ψ (primaryGenerator I)*(Ψ (primaryGenerator J))^3 := by
  have hn := (primaryGenerator_spec I hI).2
  have hb := (primaryGenerator_spec J hJ).2
  have hnb : lambda^2∣primaryGenerator I*(primaryGenerator J)^3-1 :=
    CubicJacobiGlobal.primary_mul _ _ hn (primary_pow_congruence _ hb 3)
  rw [normalized_infinityCoefficient_squarefree_cube I J hI hJ hsq,
    fixedThetaTwist_primary Ψ _ hnb,paperLambda_symbol_squarefree_cube _ _ hb,map_mul,map_pow]
  have hunit : star (eisEmbedding (symbol ramifiedTraceLambda (primaryGenerator I)))*
      eisEmbedding (symbol ramifiedTraceLambda (primaryGenerator I))=1 := by
    simpa only [Complex.star_def,paperLambda_symbol_norm _ hn,one_pow,
      Complex.ofReal_one] using Complex.conj_mul' (eisEmbedding (symbol ramifiedTraceLambda (primaryGenerator I)))
  calc
    _ = (star (eisEmbedding (symbol ramifiedTraceLambda (primaryGenerator I)))*
        eisEmbedding (symbol ramifiedTraceLambda (primaryGenerator I)))*
        ((‖eisEmbedding (primaryGenerator J)‖:ℂ)*gaussTwo I hI*
          Ψ (primaryGenerator I)*(Ψ (primaryGenerator J))^3) := by ring
    _ = _ := by rw [hunit,one_mul]

end

open ActualEisensteinCubic CompletedGauss CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O

lemma sourceFourier_primary_squarefree_cube_preimage (x:Eis)
    (hx:lambda^2∣x-1) (hT:sourceResidualFourierCoefficient x≠0) :
    ∃p:({I:Ideal Eis // Squarefree I ∧ primaryGenerator I≠0} ×
      {J:Ideal Eis // primaryGenerator J≠0}),
      primaryGenerator p.1.val*(primaryGenerator p.2.val)^3=x := by
  have hx0:x≠0:=primary_ne_zero x hx
  have hgen:primaryGenerator (Ideal.span {x})=x:=primaryGenerator_span x hx0 hx
  have hg:primaryGenerator (Ideal.span {x})≠0:=by rwa [hgen]
  have ht:sourceResidualFourierCoefficient (primaryGenerator (Ideal.span {x}))≠0:=by
    rwa [hgen]
  obtain ⟨I,J,hI,hgI,hgJ,hIJ⟩:=sourceFourier_squarefree_cube_support (Ideal.span {x}) hg ht
  refine ⟨(⟨I,hI,hgI⟩,⟨J,hgJ⟩),?_⟩
  have he:=congrArg primaryGenerator hIJ
  simpa only [primaryGenerator_mul,primaryGenerator_pow,hgen] using he

theorem sourceFourier_tsum_primary_pairs (w:Eis→ℂ)
    (hw:∀x:Eis,w x≠0→lambda^2∣x-1) :
    (∑'x:Eis,w x*star (sourceResidualFourierCoefficient x))=
      ∑'p:({I:Ideal Eis // Squarefree I ∧ primaryGenerator I≠0} ×
        {J:Ideal Eis // primaryGenerator J≠0}),
        w (primaryGenerator p.1.val*(primaryGenerator p.2.val)^3)*
          star (sourceResidualFourierCoefficient
            (primaryGenerator p.1.val*(primaryGenerator p.2.val)^3)) := by
  let P:=({I:Ideal Eis // Squarefree I ∧ primaryGenerator I≠0} ×
    {J:Ideal Eis // primaryGenerator J≠0})
  let phi:P→Eis:=fun p=>primaryGenerator p.1.val*(primaryGenerator p.2.val)^3
  let f:Eis→ℂ:=fun x=>w x*star (sourceResidualFourierCoefficient x)
  change (∑'x:Eis,f x)=∑'p:P,f (phi p)
  apply tsum_eq_tsum_of_ne_zero_bij
    (fun p:Function.support (fun p:P=>f (phi p))=>phi p.val)
  · exact primary_squarefree_cube_injective.comp Subtype.val_injective
  · intro x hx
    have hwx:w x≠0:=by
      intro hz
      exact hx (by simp only [f,hz,zero_mul])
    have hTx:sourceResidualFourierCoefficient x≠0:=by
      intro hz
      exact hx (by simp only [f,hz,star_zero,mul_zero])
    obtain ⟨p,hp⟩:=sourceFourier_primary_squarefree_cube_preimage x (hw x hwx) hTx
    have hphi:phi p=x:=hp
    have hfp:f (phi p)≠0:=by rwa [hphi]
    exact ⟨⟨p,hfp⟩,hphi⟩
  · intro p
    rfl

end CubicEisenstein

end

end OAI
