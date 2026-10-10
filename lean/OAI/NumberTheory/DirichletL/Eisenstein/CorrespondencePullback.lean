import OAI.NumberTheory.DirichletL.Eisenstein.CorrespondenceTests

namespace OAI

noncomputable section

namespace CubicEisenstein

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
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups Pointwise Manifold ContDiff ENNReal InnerProductSpace
open Finset AddChar MulChar EisensteinEmbedding

section
local notation "O" => ActualEisensteinCubic.O

lemma integralCoverMap_quasiMeasurePreserving {H K : Subgroup (SL(2,ActualEisensteinCubic.O))}
    (hHK : H≤K) (hK : K≤CubicKubota.levelThree) [H.IsFiniteRelIndex K] :
    Measure.QuasiMeasurePreserving (integralCoverMap hHK)
      (integralQuotientVolume H) (integralQuotientVolume K) := by
  refine ⟨integralCoverMap_measurable hHK,?_⟩
  rw [integralCoverMap_measure hHK hK]
  exact Measure.smul_absolutelyContinuous

variable {H J : Subgroup (SL(2,ActualEisensteinCubic.O))}
    (hHK : H≤globalKubotaKernel) (hJK : J≤globalKubotaKernel)
    [H.IsFiniteRelIndex globalKubotaKernel] [J.IsFiniteRelIndex globalKubotaKernel]
    (e : H≃*J) (g : SL(2,ℂ)) (he : IntegralCoverIntertwines e g)

def kernelCorrespondenceL2 : KernelQuotientL2→L[ℂ]KernelQuotientL2 :=
  (integralCoverTrace hHK globalKubotaKernel_le_levelThree).comp
    ((integralConjugatePullback e g he
      (hHK.trans globalKubotaKernel_le_levelThree)
      (hJK.trans globalKubotaKernel_le_levelThree)).toContinuousLinearMap.comp
      (integralCoverPullback hJK globalKubotaKernel_le_levelThree))

lemma kernelCorrespondenceL2_representative (F : KernelQuotientL2)
    (f : KernelQuotient→ℂ) (hf : Measurable f)
    (hrep : F=ᵐ[integralQuotientVolume globalKubotaKernel]f) :
    kernelCorrespondenceL2 hHK hJK e g he F=ᵐ[integralQuotientVolume globalKubotaKernel]
      kernelCorrespondenceFunction hJK e g he f := by
  have hcover := (integralCoverPullback_ae hJK globalKubotaKernel_le_levelThree F).trans
    ((integralCoverMap_quasiMeasurePreserving hJK
      globalKubotaKernel_le_levelThree).ae_eq_comp hrep)
  have hconj := (integralConjugatePullback_ae e g he
    (hHK.trans globalKubotaKernel_le_levelThree)
    (hJK.trans globalKubotaKernel_le_levelThree) _).trans
    ((integralConjugateMap_measurePreserving e g he
      (hHK.trans globalKubotaKernel_le_levelThree)
      (hJK.trans globalKubotaKernel_le_levelThree)).quasiMeasurePreserving.ae_eq_comp hcover)
  exact integralCoverTrace_representative hHK globalKubotaKernel_le_levelThree _ _
    ((hf.comp (integralCoverMap_measurable hJK)).comp (integralConjugateMap_measurable e g he)) hconj

lemma kernelCorrespondenceTest_mass (f : kernelSmoothTests) :
    kernelSmoothTestsToL2 (kernelCorrespondenceTest hHK hJK e g he f)=
      kernelCorrespondenceL2 hHK hJK e g he (kernelSmoothTestsToL2 f) := by
  apply Lp.ext
  exact (kernelSmoothTests_memLp (kernelCorrespondenceTest hHK hJK e g he f)).coeFn_toLp.trans
    (kernelCorrespondenceL2_representative hHK hJK e g he _ f.1
      f.2.1.continuous.measurable (kernelSmoothTests_memLp f).coeFn_toLp).symm

include hHK in
lemma kernelCorrespondenceFunction_integrable (f : KernelQuotient→ℂ) (hf : Measurable f)
    (hi : Integrable f (integralQuotientVolume globalKubotaKernel)) :
    Integrable (kernelCorrespondenceFunction hJK e g he f)
      (integralQuotientVolume globalKubotaKernel) := by
  have hcover := (integralCoverMap_measurePreserving hJK
    globalKubotaKernel_le_levelThree).integrable_comp_of_integrable
    (hi.smul_measure (c:=(J.relIndex globalKubotaKernel:ℝ≥0∞)) (by simp))
  have hconj := (integralConjugateMap_measurePreserving e g he
    (hHK.trans globalKubotaKernel_le_levelThree)
    (hJK.trans globalKubotaKernel_le_levelThree)).integrable_comp_of_integrable hcover
  exact integralCoverTraceFunction_integrable hHK globalKubotaKernel_le_levelThree _
    ((hf.comp (integralCoverMap_measurable hJK)).comp (integralConjugateMap_measurable e g he)) hconj

include hHK in
lemma kernelCorrespondenceFunction_integral (f : KernelQuotient→ℂ) (hf : Measurable f)
    (hi : Integrable f (integralQuotientVolume globalKubotaKernel)) :
    (∫q,kernelCorrespondenceFunction hJK e g he f q∂integralQuotientVolume globalKubotaKernel)=
      (J.relIndex globalKubotaKernel:ℂ)*(∫q,f q∂integralQuotientVolume globalKubotaKernel) := by
  have hcover := (integralCoverMap_measurePreserving hJK
    globalKubotaKernel_le_levelThree).integrable_comp_of_integrable
    (hi.smul_measure (c:=(J.relIndex globalKubotaKernel:ℝ≥0∞)) (by simp))
  have hconj := (integralConjugateMap_measurePreserving e g he
    (hHK.trans globalKubotaKernel_le_levelThree)
    (hJK.trans globalKubotaKernel_le_levelThree)).integrable_comp_of_integrable hcover
  have hm := integralConjugateMap_measurePreserving e g he
    (hHK.trans globalKubotaKernel_le_levelThree)
    (hJK.trans globalKubotaKernel_le_levelThree)
  change Integrable (fun q=>f (integralCoverMap hJK (integralConjugateMap e g he q))) _ at hconj
  calc
    _ = ∫q,f (integralCoverMap hJK (integralConjugateMap e g he q))∂integralQuotientVolume H :=
      integralCoverTraceFunction_integral hHK globalKubotaKernel_le_levelThree _
        ((hf.comp (integralCoverMap_measurable hJK)).comp (integralConjugateMap_measurable e g he)) hconj
    _ = ∫q,f (integralCoverMap hJK q)∂integralQuotientVolume J := by
      have hh := integral_map («μ»:=integralQuotientVolume H) hm.measurable.aemeasurable
        (hf.comp (integralCoverMap_measurable hJK)).aestronglyMeasurable
      rw [hm.map_eq] at hh
      exact hh.symm
    _ = ∫q,f q∂Measure.map (integralCoverMap hJK) (integralQuotientVolume J) :=
      (integral_map (integralCoverMap_measurable hJK).aemeasurable hf.aestronglyMeasurable).symm
    _ = _ := by
      rw [integralCoverMap_measure hJK globalKubotaKernel_le_levelThree,
        integral_smul_measure]
      simp only [ENNReal.toReal_natCast,Complex.real_smul,Complex.ofReal_natCast]

end

def coverEnergyDensity (F : EuclideanSpatial→ℂ) (p : EuclideanSpatial) : ℝ :=
  euclideanScalarDirichletDensity (fun x=>(F x).re) p+
    euclideanScalarDirichletDensity (fun x=>(F x).im) p

def coverGradientAt (F : EuclideanSpatial→ℂ) (p : EuclideanSpatial) :
    EuclideanSpace ℂ (Fin 3) :=
  WithLp.toLp 2 (fun j=>(p 2:ℂ)*fderiv ℝ F p (EuclideanSpace.basisFun (Fin 3) ℝ j))

lemma coverEnergyDensity_nonneg (F : EuclideanSpatial→ℂ) (p : EuclideanSpatial) :
    0≤coverEnergyDensity F p := by
  unfold coverEnergyDensity euclideanScalarDirichletDensity
  positivity

lemma coverGradientAt_norm_sq (F : EuclideanSpatial→ℂ) (p : EuclideanSpatial)
    (hF : DifferentiableAt ℝ F p) :
    ‖coverGradientAt F p‖^2=coverEnergyDensity F p := by
  have hr := (Complex.reCLM.hasFDerivAt.comp p hF.hasFDerivAt).fderiv
  have hi := (Complex.imCLM.hasFDerivAt.comp p hF.hasFDerivAt).fderiv
  change fderiv ℝ (fun x=>(F x).re) p=_ at hr
  change fderiv ℝ (fun x=>(F x).im) p=_ at hi
  unfold coverEnergyDensity euclideanScalarDirichletDensity
  rw [hr,hi,(EuclideanSpace.basisFun (Fin 3) ℝ).norm_dual,
    (EuclideanSpace.basisFun (Fin 3) ℝ).norm_dual,←mul_add,←Finset.sum_add_distrib]
  rw [PiLp.norm_sq_eq_of_L2]
  change (∑j:Fin 3,‖(p 2:ℂ)*fderiv ℝ F p (EuclideanSpace.basisFun (Fin 3) ℝ j)‖^2)=_
  simp only [norm_mul,mul_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  change ‖fderiv ℝ F p (EuclideanSpace.basisFun (Fin 3) ℝ j)‖^2=
    (fderiv ℝ F p (EuclideanSpace.basisFun (Fin 3) ℝ j)).re^2+
      (fderiv ℝ F p (EuclideanSpace.basisFun (Fin 3) ℝ j)).im^2
  simpa only [Complex.normSq_apply,pow_two] using
    (Complex.normSq_eq_norm_sq (fderiv ℝ F p (EuclideanSpace.basisFun (Fin 3) ℝ j))).symm

lemma coverEnergyDensity_comp (g : SL(2,ℂ)) (F : EuclideanSpatial→ℂ)
    (p : EuclideanSpatial) (hp : 0<p 2)
    (hF : DifferentiableAt ℝ F (euclideanAction g p)) :
    coverEnergyDensity (F ∘ euclideanAction g) p=coverEnergyDensity F (euclideanAction g p) := by
  have hr := hyperbolic_cotangent_energy_comp g (fun p=>(F p).re) p hp
    (Complex.reCLM.differentiableAt.comp _ hF)
  have hi := hyperbolic_cotangent_energy_comp g (fun p=>(F p).im) p hp
    (Complex.imCLM.differentiableAt.comp _ hF)
  exact congrArg₂ (fun x y : ℝ=>x+y) hr hi

lemma coverGradientAt_sum {ι : Type*} (s : Finset ι) (F : ι→EuclideanSpatial→ℂ)
    (p : EuclideanSpatial) (hF : ∀i∈s,DifferentiableAt ℝ (F i) p) :
    coverGradientAt (fun x=>∑i∈s,F i x) p=∑i∈s,coverGradientAt (F i) p := by
  apply (WithLp.equiv 2 (Fin 3→ℂ)).injective
  funext j
  simp only [coverGradientAt,fderiv_fun_sum hF,_root_.sum_apply,
    WithLp.equiv_apply,Finset.mul_sum,WithLp.ofLp_sum,Finset.sum_apply]

lemma norm_sum_sq_le_card {ι E : Type*} [NormedAddCommGroup E]
    (s : Finset ι) (f : ι→E) :
    ‖∑i∈s,f i‖^2≤(s.card:ℝ)*∑i∈s,‖f i‖^2 := by
  calc
    _ ≤ (∑i∈s,‖f i‖)^2 := (sq_le_sq₀ (norm_nonneg _) (Finset.sum_nonneg (fun _ _=>norm_nonneg _))).mpr
      (norm_sum_le _ _)
    _ ≤ _ := by
      simpa only [one_mul,one_pow,Finset.sum_const,nsmul_eq_mul,mul_one] using
        (Finset.sum_mul_sq_le_sq_mul_sq s (fun _=> (1:ℝ)) (fun i=>‖f i‖))

lemma coverEnergyDensity_sum_le {ι : Type*} (s : Finset ι) (F : ι→EuclideanSpatial→ℂ)
    (p : EuclideanSpatial) (hF : ∀i∈s,DifferentiableAt ℝ (F i) p) :
    coverEnergyDensity (fun x=>∑i∈s,F i x) p≤(s.card:ℝ)*∑i∈s,coverEnergyDensity (F i) p := by
  rw [←coverGradientAt_norm_sq _ _ (DifferentiableAt.fun_sum hF),coverGradientAt_sum s F p hF]
  have hh := norm_sum_sq_le_card s (fun i=>coverGradientAt (F i) p)
  calc
    _ ≤ _ := hh
    _ = _ := by
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      exact coverGradientAt_norm_sq (F i) p (hF i hi)

lemma kernelTestEnergyDensity_eq_cover (f : kernelSmoothTests) (w : HyperbolicSpace) :
    kernelTestEnergyDensity f w=coverEnergyDensity (kernelTestField f) (hyperbolicEuclideanCoordinates w) := rfl

end

section
open Filter MeasureTheory
open scoped BigOperators Classical MatrixGroups Matrix

open ActualEisensteinCubic CubicKubota ConcreteTraceCRT
local notation "Eis" => ActualEisensteinCubic.O

lemma rational_unipotent_upper (n:ℕ) :
    rationalEmbedding (ModularGroup.T^n)=unitCuspUpper (n:Eis) := by
  rw [←rationalUnipotent_nat]
  apply Subtype.ext
  change ( !![(1 : ℤ), (n : ℤ); 0, 1]).map (Int.castRingHom Eis) =
    !![1, (n : Eis); 0, 1]
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp

lemma rational_cusp_lower_section (u:Eisˣ) (n:ℕ) (z:ℂ) (v:ℝ) (hv:0<v) :
    rationalComplex ModularGroup.S*rationalComplex (ModularGroup.T^n)*
      integralComplexMatrix (lowerCuspMatrix (u:Eis))*upperSection z v hv=
      integralComplexMatrix (unitCuspDiagonal (-u))*
        integralComplexMatrix (lowerCuspMatrix (-(u:Eis)*(1+(n:Eis)*(u:Eis))))*
          upperSection (z+eisEmbedding (↑u⁻¹:Eis)) v hv := by
  have hm:=congrArg integralComplexMatrix (rational_cusp_lower_factor u (n:ℤ))
  simp only [map_mul,Int.cast_natCast] at hm
  have hu:integralComplexMatrix (unitCuspUpper (n:Eis))=rationalComplex (ModularGroup.T^n):=by
    rw [←rational_unipotent_upper]
    rfl
  rw [hu] at hm
  change rationalComplex ModularGroup.S*rationalComplex (ModularGroup.T^n)*
    integralComplexMatrix (lowerCuspMatrix (u:Eis))=_ at hm
  rw [hm,mul_assoc,unitCuspUpper_section]

lemma hyperbolicEisenstein_fixed_upper (g:SL(2,ℂ)) (z:ℂ) (v:ℝ) (hv:0<v) (s:ℂ) :
    hyperbolicEisenstein s (g • upperPoint z v hv)=eisenstein (g*upperSection z v hv) s:=rfl

theorem sourceEisenstein_unit_lower (u:Eisˣ) (z:ℂ) (v:ℝ) (hv:0<v) (s:ℂ) :
    sourceEisenstein s (integralComplexMatrix (lowerCuspMatrix (u:Eis)) • upperPoint z v hv)=
      (4:ℂ)⁻¹*(eisenstein (integralComplexMatrix (lowerCuspMatrix (u:Eis))*upperSection z v hv) s+
        ∑n:Fin 3,eisenstein (integralComplexMatrix (unitCuspDiagonal (-u))*
          integralComplexMatrix (lowerCuspMatrix (-(u:Eis)*(1+(n.val:Eis)*(u:Eis))))*
            upperSection (z+eisEmbedding (↑u⁻¹:Eis)) v hv) s) := by
  rw [sourceEisenstein_four_cusps]
  simp only [←mul_smul,hyperbolicEisenstein_fixed_upper]
  apply congrArg (fun c:ℂ=>(4:ℂ)⁻¹*(eisenstein
    (integralComplexMatrix (lowerCuspMatrix (u:Eis))*upperSection z v hv) s+c))
  apply Finset.sum_congr rfl
  intro n hn
  rw [←mul_assoc,rational_cusp_lower_section]

theorem sourceEisenstein_primitive_lower_four (u t:Eisˣ)
    (hu:(u:Eis)^2+(u:Eis)+1=0)
    (ht:-(u:Eis)*(1+2*(u:Eis))=onceCuspScale t)
    (z:ℂ) (v:ℝ) (hv:0<v) (s:ℂ) :
    sourceEisenstein s (integralComplexMatrix (lowerCuspMatrix (u:Eis)) • upperPoint z v hv)=
      (4:ℂ)⁻¹*(eisenstein (integralComplexMatrix (lowerCuspMatrix (u:Eis))*upperSection z v hv) s+
        eisenstein (integralComplexMatrix (unitCuspDiagonal (-u))*
          integralComplexMatrix (lowerCuspMatrix (-(u:Eis)))*upperSection (z+eisEmbedding (↑u⁻¹:Eis)) v hv) s+
        eisenstein (integralComplexMatrix (unitCuspDiagonal (-u))*
          integralComplexMatrix (lowerCuspMatrix 1)*upperSection (z+eisEmbedding (↑u⁻¹:Eis)) v hv) s+
        eisenstein (integralComplexMatrix (unitCuspDiagonal (-u))*
          integralComplexMatrix (lowerCuspMatrix (onceCuspScale t))*
            upperSection (z+eisEmbedding (↑u⁻¹:Eis)) v hv) s) := by
  rw [sourceEisenstein_unit_lower,Fin.sum_univ_three]
  have h1:-(u:Eis)*(1+1*(u:Eis))=1:=by linear_combination -hu
  simp only [Fin.val_zero,Fin.val_one,Fin.val_two,Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat,
    zero_mul,add_zero,mul_one,h1,ht]
  ring

lemma continuous_fixed_left_Eisenstein (g:SL(2,ℂ)) (v:ℝ) (hv:0<v) (s:ℂ) (hs:2<s.re) (b:ℂ) :
    Continuous (fun z:ℂ=>eisenstein (g*upperSection (z+b) v hv) s) := by
  have hc:Continuous (fun z:ℂ=>(⟨(z+b,v),hv⟩:UpperCoordinates)):=by fun_prop
  have he : Continuous (fun z:ℂ=>hyperbolicEisenstein s (g • upperPoint (z+b) v hv)) := by
    simpa only [Function.comp_def] using
      ((hyperbolicEisenstein_continuous s hs).comp (continuous_translatedUpperCoordinates g)).comp hc
  simpa only [hyperbolicEisenstein_fixed_upper] using he

lemma integrable_fixed_left_Eisenstein_fourier (g:SL(2,ℂ)) (v:ℝ) (hv:0<v) (s:ℂ) (hs:2<s.re) (b freq:ℂ) :
    IntegrableOn (fun z:ℂ=>eisenstein (g*upperSection (z+b) v hv) s*ShortDraftTrace.breveE (-freq*z)) periodDomain := by
  apply periodDomain_integrable_of_continuous
  apply (continuous_fixed_left_Eisenstein g v hv s hs b).mul
  change Continuous (fun z:ℂ=>Complex.exp (2*Real.pi*Complex.I*((-freq*z)+starRingEnd ℂ (-freq*z))))
  fun_prop

end

section
open Filter MeasureTheory
open scoped BigOperators Classical MatrixGroups

open ActualEisensteinCubic ConcreteTraceCRT CubicKubota
local notation "Eis" => ActualEisensteinCubic.O

def ramifiedCuspGaussSeries (b:Bool) (h:Eis)
    (hf:(3:Eis)∣h-onceCuspScale (ramifiedCuspScaleUnit b)) (s:ℂ) : ℂ :=
  (4:ℂ)⁻¹*(unitCuspGaussSeries 1 (ramifiedCuspRoot b) h s+
    ShortDraftTrace.breveE (ninthCuspFrequency h*eisEmbedding (↑(ramifiedCuspRoot b)⁻¹:Eis))*
      (unitCuspGaussSeries (-(ramifiedCuspRoot b)) (-(ramifiedCuspRoot b)) h s+
        unitCuspGaussSeries (-(ramifiedCuspRoot b)) 1 h s+
          onceCuspGaussSeries (-(ramifiedCuspRoot b)) (ramifiedCuspScaleUnit b) h hf s))

theorem ramifiedSourceEisenstein_fourier (b:Bool) (h:Eis)
    (hf:(3:Eis)∣h-onceCuspScale (ramifiedCuspScaleUnit b))
    (v:ℝ) (hv:0<v) (s:ℂ) (hs:2<s.re) :
    (∫z in periodDomain,sourceEisenstein s
      (integralComplexMatrix (lowerCuspMatrix (ramifiedCuspRoot b:Eis)) • upperPoint z v hv)*
        ShortDraftTrace.breveE (-ninthCuspFrequency h*z))=
      ((v:ℂ)^(2-s)*sourceFourierKernel s (ninthCuspFrequency h*v))*ramifiedCuspGaussSeries b h hf s := by
  let t:=ramifiedCuspRoot b
  let shift:=eisEmbedding (↑t⁻¹:Eis)
  let arch:=(v:ℂ)^(2-s)*sourceFourierKernel s (ninthCuspFrequency h*v)
  let f0:ℂ→ℂ:=fun z=>eisenstein (integralComplexMatrix (lowerCuspMatrix (t:Eis))*upperSection z v hv) s*
    ShortDraftTrace.breveE (-ninthCuspFrequency h*z)
  let f1:ℂ→ℂ:=fun z=>eisenstein (integralComplexMatrix (unitCuspDiagonal (-t))*
    integralComplexMatrix (lowerCuspMatrix (-(t:Eis)))*upperSection (z+shift) v hv) s*
      ShortDraftTrace.breveE (-ninthCuspFrequency h*z)
  let f2:ℂ→ℂ:=fun z=>eisenstein (integralComplexMatrix (unitCuspDiagonal (-t))*
    integralComplexMatrix (lowerCuspMatrix 1)*upperSection (z+shift) v hv) s*
      ShortDraftTrace.breveE (-ninthCuspFrequency h*z)
  let f3:ℂ→ℂ:=fun z=>eisenstein (integralComplexMatrix (unitCuspDiagonal (-t))*
    integralComplexMatrix (lowerCuspMatrix (onceCuspScale (ramifiedCuspScaleUnit b)))*upperSection (z+shift) v hv) s*
      ShortDraftTrace.breveE (-ninthCuspFrequency h*z)
  have hi0:IntegrableOn f0 periodDomain:=by
    simpa only [f0,add_zero] using integrable_fixed_left_Eisenstein_fourier
      (integralComplexMatrix (lowerCuspMatrix (t:Eis))) v hv s hs 0 (ninthCuspFrequency h)
  have hi1:IntegrableOn f1 periodDomain:=integrable_fixed_left_Eisenstein_fourier _ v hv s hs shift _
  have hi2:IntegrableOn f2 periodDomain:=integrable_fixed_left_Eisenstein_fourier _ v hv s hs shift _
  have hi3:IntegrableOn f3 periodDomain:=integrable_fixed_left_Eisenstein_fourier _ v hv s hs shift _
  have heq:(∫z in periodDomain,sourceEisenstein s
      (integralComplexMatrix (lowerCuspMatrix (t:Eis)) • upperPoint z v hv)*ShortDraftTrace.breveE (-ninthCuspFrequency h*z))=
      (4:ℂ)⁻¹*((∫z in periodDomain,f0 z)+(∫z in periodDomain,f1 z)+
        (∫z in periodDomain,f2 z)+(∫z in periodDomain,f3 z)):=by
    calc
      _ = ∫z in periodDomain,(4:ℂ)⁻¹*(f0 z+f1 z+f2 z+f3 z) := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun z=>by
          dsimp only
          rw [sourceEisenstein_primitive_lower_four t (ramifiedCuspScaleUnit b)
            (ramifiedCuspRoot_primitive b) (ramifiedCuspScaleUnit_spec b)]
          dsimp only [f0,f1,f2,f3,shift]
          ring)
      _ = _ := by
        rw [integral_const_mul]
        rw [integral_add (f:=fun z=>f0 z+f1 z+f2 z) (g:=f3) ((hi0.add hi1).add hi2) hi3,
          integral_add (f:=fun z=>f0 z+f1 z) (g:=f2) (hi0.add hi1) hi2,
          integral_add (f:=f0) (g:=f1) hi0 hi1]
  have hr0:(↑(1:Eisˣ)⁻¹:Eis)^2*(t:Eis)=omega^(ramifiedCuspDirectIndex b):=by
    simpa [t] using ramifiedCuspRoot_val b
  have hr1:(↑(-t)⁻¹:Eis)^2*((-t:Eisˣ):Eis)=-(omega^(ramifiedCuspOppositeIndex b)):=
    ramifiedCusp_opposite_character b
  have hr2:(↑(-t)⁻¹:Eis)^2*((1:Eisˣ):Eis)=omega^(ramifiedCuspDirectIndex b):=by
    rw [Units.val_one,mul_one,ramifiedCusp_neg_inv_square,ramifiedCuspRoot_val]
  have hb2:(3:Eis)∣h+ramifiedAffineParameter (ramifiedCuspDirectIndex b) 0*((1:Eisˣ):Eis):=by
    simpa using ramifiedCusp_unit_base b h hf
  have h0:(∫z in periodDomain,f0 z)=arch*unitCuspGaussSeries 1 t h s:=by
    simpa only [unitCuspDiagonal_one,map_one,one_mul,f0,arch] using
      unitCusp_eisenstein_fourier_base 1 t (ramifiedCuspDirectIndex b) h (Or.inl hr0)
        (ramifiedCusp_direct_base b h hf) v hv s hs
  have h1:(∫z in periodDomain,f1 z)=ShortDraftTrace.breveE (ninthCuspFrequency h*shift)*
      (arch*unitCuspGaussSeries (-t) (-t) h s):=by
    have he:=diagonal_unit_fourier_shift (-t) (-t) (ramifiedCuspOppositeIndex b) h (Or.inr hr1)
      (ramifiedCusp_opposite_base b h hf) v hv s shift
    rw [unitCusp_eisenstein_fourier_base (-t) (-t) (ramifiedCuspOppositeIndex b) h (Or.inr hr1)
        (ramifiedCusp_opposite_base b h hf) v hv s hs] at he
    simpa only [f1,Units.val_neg,arch] using he
  have h2:(∫z in periodDomain,f2 z)=ShortDraftTrace.breveE (ninthCuspFrequency h*shift)*
      (arch*unitCuspGaussSeries (-t) 1 h s):=by
    have he:=diagonal_unit_fourier_shift (-t) 1 (ramifiedCuspDirectIndex b) h (Or.inl hr2)
      hb2 v hv s shift
    rw [unitCusp_eisenstein_fourier_base (-t) 1 (ramifiedCuspDirectIndex b) h (Or.inl hr2)
        hb2 v hv s hs] at he
    simpa only [f2,Units.val_one,arch] using he
  have h3:(∫z in periodDomain,f3 z)=ShortDraftTrace.breveE (ninthCuspFrequency h*shift)*
      (arch*onceCuspGaussSeries (-t) (ramifiedCuspScaleUnit b) h hf s):=by
    dsimp only [f3]
    rw [diagonal_once_fourier_shift (-t) (ramifiedCuspScaleUnit b) h hf v hv s shift hs,
      onceCusp_eisenstein_fourier (-t) (ramifiedCuspScaleUnit b) h hf v hv s hs]
  rw [heq,h0,h1,h2,h3]
  dsimp only [ramifiedCuspGaussSeries,arch,shift,t]
  ring

end

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups

local notation "Eis" => ActualEisensteinCubic.O

theorem finite_unramified_residue {ι:Type*} [Fintype ι] [DecidableEq ι]
    (index:ι→Eis) (coefficient:ι→ℂ→ℂ)
    (hc:∀i s,1<s.re→AnalyticAt ℂ (coefficient i) s)
    (f:ℂ→ℂ) (R:ℂ)
    (hf:∀s,1<s.re→0<s.im→AnalyticAt ℂ f s)
    (hlim:Tendsto (fun s:ℂ=>(s-4/3)*f s) (𝓝[≠] (4/3:ℂ)) (𝓝 R))
    (hinit:∀s:ℂ,4<s.re→0<s.im→
      f s=∑i,coefficient i s*unramifiedCubicGaussSeries s (index i)) :
    R=∑i,coefficient i (4/3)*unramifiedGaussResidue (index i) := by
  let H:ι→ℂ→ℂ:=fun i s=>cuspWhittakerHeightFactor s (3*index i)
  let G:ι→ℂ→ℂ:=fun i s=>translatedCuspFamily (3*index i) oppositeSource 2 3
    (by norm_num) (by norm_num) s
  let D:ℂ→ℂ:=fun s=>∏i,H i s
  let E:ι→ℂ→ℂ:=fun i s=>∏j∈Finset.univ.erase i,H j s
  have hH:∀i s,1<s.re→AnalyticAt ℂ (H i) s:=fun i s hs=>
    cuspWhittakerHeightFactor_analyticAt (3*index i) s hs
  have hD:∀s,1<s.re→AnalyticAt ℂ D s:=fun s hs=>
    Finset.analyticAt_fun_prod _ (fun i hi=>hH i s hs)
  have hE:∀i s,1<s.re→AnalyticAt ℂ (E i) s:=fun i s hs=>
    Finset.analyticAt_fun_prod _ (fun j hj=>hH j s hs)
  have hprod (i:ι) (s:ℂ):H i s*E i s=D s:=by
    exact Finset.mul_prod_erase Finset.univ (fun j=>H j s) (Finset.mem_univ i)
  let domain:Set ℂ:={s|1<s.re∧0<s.im}
  have hconvex:Convex ℝ domain:=
    ((convex_Ioi (1:ℝ)).linear_preimage Complex.reCLM.toLinearMap).inter
      ((convex_Ioi (0:ℝ)).linear_preimage Complex.imCLM.toLinearMap)
  have ha:AnalyticOnNhd ℂ (fun s=>f s*D s) domain:=fun s hs=>(hf s hs.1 hs.2).mul (hD s hs.1)
  have hb:AnalyticOnNhd ℂ (fun s=>∑i,coefficient i s*G i s*E i s) domain:=by
    intro s hs
    apply Finset.analyticAt_fun_sum
    intro i hi
    exact ((hc i s hs.1).mul (translatedCuspFamily_analyticAt_nonreal (3*index i)
      oppositeSource 2 3 (by norm_num) (by norm_num) s hs.1.ne' hs.2.ne')).mul (hE i s hs.1)
  have hopen:IsOpen {s:ℂ|4<s.re∧0<s.im}:=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt continuous_const Complex.continuous_im)
  have hev:(fun s=>f s*D s)=ᶠ[𝓝 (5+Complex.I:ℂ)]
      (fun s=>∑i,coefficient i s*G i s*E i s):=by
    filter_upwards [hopen.mem_nhds (by norm_num)] with s hs
    rw [hinit s hs.1 hs.2,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    dsimp only [G]
    rw [translatedCuspFamily_opposite_initial (index i) s hs.1 hs.2]
    change coefficient i s*unramifiedCubicGaussSeries s (index i)*D s=
      coefficient i s*(unramifiedCubicGaussSeries s (index i)*H i s)*E i s
    rw [←hprod i s]
    ring
  have heq:=ha.eqOn_of_preconnected_of_eventuallyEq hb hconvex.isPreconnected
    (show (5+Complex.I:ℂ)∈domain by norm_num [domain]) hev
  have hDc:Tendsto D (𝓝[≠] (4/3:ℂ)) (𝓝 (D (4/3))):=
    (hD (4/3) (by norm_num)).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hl:=(hlim.mul hDc).comp upperVertical_tendsto_cubic_punctured
  have hg:∀i,Tendsto (fun s:ℂ=>coefficient i s*((s-4/3)*G i s)*E i s)
      (𝓝[≠] (4/3:ℂ))
      (𝓝 (coefficient i (4/3)*translatedCuspFourier (3*index i) oppositeSource
        cubicEisensteinResidue*E i (4/3))):=by
    intro i
    exact (((hc i (4/3) (by norm_num)).continuousAt.tendsto.mono_left nhdsWithin_le_nhds).mul
      (translatedCuspFamily_residue_limit (3*index i) oppositeSource 2 3
        (by norm_num) (by norm_num))).mul
          ((hE i (4/3) (by norm_num)).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
  have hr:=(tendsto_finsetSum Finset.univ (fun i hi=>hg i)).comp upperVertical_tendsto_cubic_punctured
  have hel:(fun t:ℝ=>((((4/3:ℂ)+(t:ℂ)*Complex.I)-4/3)*f ((4/3:ℂ)+(t:ℂ)*Complex.I))*
      D ((4/3:ℂ)+(t:ℂ)*Complex.I))=ᶠ[𝓝[>] (0:ℝ)]
      (fun t:ℝ=>∑i,coefficient i ((4/3:ℂ)+(t:ℂ)*Complex.I)*
        ((((4/3:ℂ)+(t:ℂ)*Complex.I)-4/3)*G i ((4/3:ℂ)+(t:ℂ)*Complex.I))*
          E i ((4/3:ℂ)+(t:ℂ)*Complex.I)):=by
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht0:0<t:=ht
    have he:=heq (show (4/3:ℂ)+(t:ℂ)*Complex.I∈domain by
      constructor
      · norm_num
      · simpa using ht0)
    dsimp only at he
    rw [mul_assoc,he,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hres:=tendsto_nhds_unique_of_eventuallyEq hl hr hel
  have hDn:D (4/3)≠0:=Finset.prod_ne_zero_iff.mpr (fun i hi=>
    cuspWhittakerHeightFactor_center_ne_zero (3*index i))
  apply mul_right_cancel₀ hDn
  rw [Finset.sum_mul]
  refine hres.trans ?_
  apply Finset.sum_congr rfl
  intro i hi
  change coefficient i (4/3)*translatedCuspFourier (3*index i) oppositeSource
    cubicEisensteinResidue*E i (4/3)=coefficient i (4/3)*
      (translatedCuspFourier (3*index i) oppositeSource cubicEisensteinResidue/H i (4/3))*D (4/3)
  rw [←hprod i (4/3)]
  field_simp [show H i (4/3)≠0 from cuspWhittakerHeightFactor_center_ne_zero (3*index i)]

end

open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups

open CubicKubota

lemma cuspStrip_integrable_continuous (a b:ℝ) (ha:0<a)
    (f:HyperbolicSpace→ℂ) (hf:Continuous f) :
    IntegrableOn f (cuspPeriodStrip a b) hyperbolicVolume :=
  (hf.continuousOn.integrableOn_compact (cuspHeightCompact_isCompact a b ha)).mono_set
    (cuspPeriodStrip_subset_heightCompact a b ha)

def sourceArbitraryHeightFamily (M:SL(2,ℂ)) (a b:ℝ) (ha:0<a)
    (ρ:BoundedContinuousFunction ℝ ℂ) (freq s:ℂ) :ℂ :=
  (24:ℂ)⁻¹*∑i:RationalBruhatIndex,arbitraryCuspHeightFamily
    (rationalComplex (rationalBruhatRep i)*M) a b ha ρ freq s

def sourceArbitraryHeightFourier (M:SL(2,ℂ)) (a b:ℝ) (ha:0<a)
    (ρ:BoundedContinuousFunction ℝ ℂ) (freq:ℂ) : KernelQuotientL2→L[ℂ]ℂ :=
  (24:ℂ)⁻¹ • ∑i:RationalBruhatIndex,arbitraryCuspHeightFourier
    (rationalComplex (rationalBruhatRep i)*M) a b ha ρ freq

lemma sourceArbitraryHeightFamily_analyticAt (M:SL(2,ℂ)) (a b:ℝ) (ha:0<a)
    (ρ:BoundedContinuousFunction ℝ ℂ) (freq s:ℂ) (hs:1<s.re) (hi:0<s.im) :
    AnalyticAt ℂ (sourceArbitraryHeightFamily M a b ha ρ freq) s := by
  apply analyticAt_const.mul
  apply Finset.analyticAt_fun_sum
  intro i hi'
  exact arbitraryCuspHeightFamily_analyticAt _ a b ha ρ freq s hs.ne' hi.ne'

lemma sourceArbitraryHeightFamily_residue_limit (M:SL(2,ℂ)) (a b:ℝ) (ha:0<a)
    (ρ:BoundedContinuousFunction ℝ ℂ) (freq:ℂ) :
    Tendsto (fun s:ℂ=>(s-4/3)*sourceArbitraryHeightFamily M a b ha ρ freq s)
      (𝓝[≠] (4/3:ℂ)) (𝓝 (sourceArbitraryHeightFourier M a b ha ρ freq cubicEisensteinResidue)) := by
  have he:=(tendsto_finsetSum Finset.univ (fun i hi=>
    arbitraryCuspHeightFamily_residue_limit (rationalComplex (rationalBruhatRep i)*M) a b ha ρ freq)).const_mul ((24:ℂ)⁻¹)
  convert he using 1
  · funext s
    rw [sourceArbitraryHeightFamily,←Finset.mul_sum]
    ring
  · simp only [sourceArbitraryHeightFourier,_root_.smul_apply,
      _root_.sum_apply,smul_eq_mul]

lemma sourceProjection_integral (f:HyperbolicSpace→ℂ) (hf:Continuous f)
    (M:SL(2,ℂ)) (a b:ℝ) (ha:0<a) (ρ:BoundedContinuousFunction ℝ ℂ) (freq:ℂ) :
    (∫w in cuspPeriodStrip a b,sourceProjection f (M•w)*arbitraryCuspWeightedPhase ρ freq w∂hyperbolicVolume)=
      (24:ℂ)⁻¹*∑i:RationalBruhatIndex,∫w in cuspPeriodStrip a b,
        f ((rationalComplex (rationalBruhatRep i)*M)•w)*arbitraryCuspWeightedPhase ρ freq w∂hyperbolicVolume := by
  have hi (i:RationalBruhatIndex) : IntegrableOn
      (fun w=>f ((rationalComplex (rationalBruhatRep i)*M)•w)*arbitraryCuspWeightedPhase ρ freq w)
      (cuspPeriodStrip a b) hyperbolicVolume :=
    cuspStrip_integrable_continuous a b ha _ ((hf.comp (continuous_hyperbolic_action _)).mul
      (arbitraryCuspWeightedPhase_continuous ρ freq))
  calc
    _ = ∫w in cuspPeriodStrip a b,(24:ℂ)⁻¹*∑i:RationalBruhatIndex,
        f ((rationalComplex (rationalBruhatRep i)*M)•w)*arbitraryCuspWeightedPhase ρ freq w∂hyperbolicVolume := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun w=>by
        dsimp only
        rw [sourceProjection_eq_twentyFour]
        simp only [rationalComplex,MonoidHom.comp_apply,mul_smul]
        rw [←Finset.sum_mul]
        ring)
    _ = _ := by rw [integral_const_mul,integral_finsetSum _ (fun i hi'=>hi i)]

lemma sourceArbitraryHeightFamily_initial (M:SL(2,ℂ)) (a b:ℝ) (ha:0<a)
    (ρ:BoundedContinuousFunction ℝ ℂ) (freq s:ℂ) (hs:4<s.re) (hi:0<s.im) :
    sourceArbitraryHeightFamily M a b ha ρ freq s=
      ∫w in cuspPeriodStrip a b,sourceEisenstein s (M•w)*arbitraryCuspWeightedPhase ρ freq w∂hyperbolicVolume := by
  rw [sourceEisenstein,sourceProjection_integral _ (hyperbolicEisenstein_continuous s (by linarith)) M a b ha ρ freq]
  unfold sourceArbitraryHeightFamily
  congr 1
  apply Finset.sum_congr rfl
  intro i hi'
  exact arbitraryCuspHeightFamily_initial _ a b ha ρ freq s hs hi

lemma arbitraryCuspHeightFourier_residue_integral (M:SL(2,ℂ)) (a b:ℝ) (ha:0<a)
    (ρ:BoundedContinuousFunction ℝ ℂ) (freq:ℂ) :
    arbitraryCuspHeightFourier M a b ha ρ freq cubicEisensteinResidue=
      ∫w in cuspPeriodStrip a b,cubicResidualFunction (M•w)*arbitraryCuspWeightedPhase ρ freq w∂hyperbolicVolume := by
  rw [arbitraryCuspHeightFourier_integral]
  have he:=(measurePreserving_smul M hyperbolicVolume).quasiMeasurePreserving.ae_eq_comp
    cubicEisensteinResidue_continuous_representative
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae he] with w hw
  exact congrArg (fun c:ℂ=>c*arbitraryCuspWeightedPhase ρ freq w) hw

lemma sourceArbitraryHeightFourier_residue_integral (M:SL(2,ℂ)) (a b:ℝ) (ha:0<a)
    (ρ:BoundedContinuousFunction ℝ ℂ) (freq:ℂ) :
    sourceArbitraryHeightFourier M a b ha ρ freq cubicEisensteinResidue=
      ∫w in cuspPeriodStrip a b,cubicSourceResidualFunction (M•w)*arbitraryCuspWeightedPhase ρ freq w∂hyperbolicVolume := by
  rw [cubicSourceResidualFunction,sourceProjection_integral _ cubicResidualFunction_continuous M a b ha ρ freq]
  simp only [sourceArbitraryHeightFourier,_root_.smul_apply,
    _root_.sum_apply,smul_eq_mul,arbitraryCuspHeightFourier_residue_integral]

end CubicEisenstein

end

end OAI
