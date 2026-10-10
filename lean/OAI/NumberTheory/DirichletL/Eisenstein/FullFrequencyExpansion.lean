import OAI.NumberTheory.DirichletL.Eisenstein.SourceCuspKernels

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
open scoped Classical BigOperators

open ActualEisensteinCubic CompletedGauss
local notation "Eis" => ActualEisensteinCubic.O

theorem thetaFullFrequency_tsum (c w : Eis→ℂ)
    (hsupp : ∀h:Eis,h≠0→c h≠0→∃p:ThetaFullIndex,thetaFullFrequency p=h) :
    (∑'h:{h:Eis // h≠0},w h.val*c h.val)=
      ∑'p:ThetaFullIndex,w (thetaFullFrequency p)*c (thetaFullFrequency p) := by
  let phi : ThetaFullIndex→{h:Eis // h≠0} := fun p=>⟨thetaFullFrequency p,thetaFullFrequency_ne_zero p⟩
  let f : {h:Eis // h≠0}→ℂ := fun h=>w h.val*c h.val
  have hinj : Function.Injective phi := by
    intro p q hpq
    exact thetaFullFrequency_injective (congrArg Subtype.val hpq)
  change (∑'h:{h:Eis // h≠0},f h)=∑'p:ThetaFullIndex,f (phi p)
  apply tsum_eq_tsum_of_ne_zero_bij
    (fun p:Function.support (fun p:ThetaFullIndex=>f (phi p))=>phi p.val)
  · exact hinj.comp Subtype.val_injective
  · intro h hh
    have hc : c h.val≠0 := by
      intro hz
      exact hh (by simp only [f,hz,mul_zero])
    obtain ⟨p,hp⟩:=hsupp h.val h.property hc
    have hphi : phi p=h := Subtype.ext hp
    have hfp : f (phi p)≠0 := by rwa [hphi]
    exact ⟨⟨p,hfp⟩,hphi⟩
  · intro p
    rfl

theorem sourceFourier_tsum_full_index (w : Eis→ℂ) :
    (∑'h:{h:Eis // h≠0},w h.val*star (sourceResidualFourierCoefficient h.val))=
      ∑'p:ThetaFullIndex,w (thetaFullFrequency p)*
        star (sourceResidualFourierCoefficient (thetaFullFrequency p)) := by
  apply thetaFullFrequency_tsum (fun h => star (sourceResidualFourierCoefficient h)) w
  intro h hh hc
  have hn : sourceResidualFourierCoefficient h≠0 := by
    intro hz
    exact hc (by rw [hz,star_zero])
  obtain ⟨u,m,I,J,hsq,hI,hJ,hfactor⟩:=
    sourceResidualFourierCoefficient_full_squarefree_cube_support h hh hn
  refine ⟨(u,m,(⟨I,hsq,hI⟩,⟨J,hJ⟩)),?_⟩
  exact hfactor.symm

theorem ramifiedFourier_tsum_full_index (side : Bool) (w : Eis→ℂ) :
    (∑'h:{h:Eis // h≠0},w h.val*star (ramifiedBesselValue side h.val))=
      ∑'p:ThetaFullIndex,w (thetaFullFrequency p)*
        star (ramifiedBesselValue side (thetaFullFrequency p)) := by
  apply thetaFullFrequency_tsum (fun h => star (ramifiedBesselValue side h)) w
  intro h hh hc
  have hn : ramifiedBesselValue side h≠0 := by
    intro hz
    exact hc (by rw [hz,star_zero])
  obtain ⟨u,m,I,J,hsq,hI,hJ,hfactor⟩:=ramifiedBesselValue_squarefree_cube_support side h hh hn
  refine ⟨(u,m,(⟨I,hsq,hI⟩,⟨J,hJ⟩)),?_⟩
  exact hfactor.symm

end

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups

section
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CompletedGauss
local notation "Eis" => ActualEisensteinCubic.O

lemma squarefreeCube_scale_le_norm_third (I J:Ideal Eis)
    (hI:primaryGenerator I≠0) (u:Eisˣ) (m:ℕ) :
    (3:ℝ)^((m:ℝ)/6)*‖eisEmbedding (primaryGenerator J)‖≤
      ‖eisEmbedding ((u.val*lambda^m)*primaryGenerator I*(primaryGenerator J)^3)‖^(1/3:ℝ) := by
  have hn:1≤‖eisEmbedding (primaryGenerator I)‖:=cubePrime_norm_ge_one _ hI
  have hn':1≤‖eisEmbedding (primaryGenerator I)‖^(1/3:ℝ):=
    Real.one_le_rpow hn (by norm_num)
  have hb:(‖eisEmbedding (primaryGenerator J)‖^3)^(1/3:ℝ)=‖eisEmbedding (primaryGenerator J)‖:=by
    rw [←Real.rpow_natCast_mul (norm_nonneg _)]
    norm_num
  have he:‖eisEmbedding ((u.val*lambda^m)*primaryGenerator I*(primaryGenerator J)^3)‖^(1/3:ℝ)=
      (3:ℝ)^((m:ℝ)/6)*‖eisEmbedding (primaryGenerator I)‖^(1/3:ℝ)*
        ‖eisEmbedding (primaryGenerator J)‖:=by
    rw [map_mul,map_mul,map_pow,norm_mul,norm_mul,norm_pow,
      Real.mul_rpow (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (pow_nonneg (norm_nonneg _) _),
      Real.mul_rpow (norm_nonneg _) (norm_nonneg _),ramified_norm_third,hb]
  rw [he]
  have hscale:0≤(3:ℝ)^((m:ℝ)/6):=Real.rpow_nonneg (by norm_num) _
  have hbn:0≤‖eisEmbedding (primaryGenerator J)‖:=norm_nonneg _
  exact mul_le_mul_of_nonneg_right (le_mul_of_one_le_right hscale hn') hbn

lemma coefficient_polynomial_of_squarefree_cube_support (F:Eis→ℂ) (C:ℝ) (hC:0≤C)
    (hsupport:∀h:Eis,h≠0→F h≠0→∃(u:Eisˣ) (m:ℕ) (I J:Ideal Eis),Squarefree I ∧
      primaryGenerator I≠0 ∧ primaryGenerator J≠0 ∧
      h=(u.val*lambda^m)*primaryGenerator I*(primaryGenerator J)^3)
    (hbound:∀(I J:Ideal Eis),primaryGenerator I≠0→primaryGenerator J≠0→Squarefree I→
      ∀(u:Eisˣ) (m:ℕ),
      ‖F ((u.val*lambda^m)*primaryGenerator I*(primaryGenerator J)^3)‖≤
        C*(3:ℝ)^((m:ℝ)/6)*‖eisEmbedding (primaryGenerator J)‖)
    (h:Eis) (hh:h≠0) : ‖F h‖≤C*‖eisEmbedding h‖^(1/3:ℝ) := by
  by_cases hz:F h=0
  · rw [hz,norm_zero]
    positivity
  obtain ⟨u,m,I,J,hsq,hI,hJ,rfl⟩:=hsupport h hh hz
  refine (hbound I J hI hJ hsq u m).trans ?_
  have hb:=mul_le_mul_of_nonneg_left (squarefreeCube_scale_le_norm_third I J hI u m) hC
  exact (by simpa only [mul_assoc] using hb)

theorem three_cusp_coefficients_polynomial_bound :
    ∃C:ℝ,0<C ∧ ∀h:Eis,h≠0→
      ‖sourceResidualFourierCoefficient h‖≤C*‖eisEmbedding h‖^(1/3:ℝ) ∧
      ∀side:Bool,‖ramifiedBesselValue side h‖≤C*‖eisEmbedding h‖^(1/3:ℝ) := by
  obtain ⟨C,hC,hbound⟩:=three_cusp_coefficients_squarefree_cube_bound
  refine ⟨C,hC,?_⟩
  intro h hh
  constructor
  · exact coefficient_polynomial_of_squarefree_cube_support sourceResidualFourierCoefficient C hC.le
      sourceResidualFourierCoefficient_full_squarefree_cube_support
      (fun I J hI hJ hsq u m=>(hbound I J hI hJ hsq u m).1) h hh
  · intro side
    exact coefficient_polynomial_of_squarefree_cube_support (ramifiedBesselValue side) C hC.le
      (ramifiedBesselValue_squarefree_cube_support side)
      (fun I J hI hJ hsq u m=>(hbound I J hI hJ hsq u m).2 side) h hh

end

section
open ActualEisensteinCubic ConcreteTraceCRT
local notation "Eis" => ActualEisensteinCubic.O

lemma coefficient_weighted_summable_of_polynomial (F:Eis→ℂ) (C:ℝ) (hC:0≤C)
    (hF:∀h:Eis,h≠0→‖F h‖≤C*‖eisEmbedding h‖^(1/3:ℝ)) :
    Summable (fun h:Eis=>if h=0 then (0:ℝ) else ‖F h‖*‖cuspFrequency h‖^(-4:ℝ)) := by
  let D:ℝ:=‖(3:ℂ)*eisLam‖
  have hD:0<D:=norm_pos_iff.mpr (mul_ne_zero (by norm_num) eisLam_ne_zero)
  have hDp:0<D^(-4:ℝ):=Real.rpow_pos_of_pos hD _
  have hs:Summable (fun h:Eis=>(C/D^(-4:ℝ))*‖eisEmbedding h‖^(-(11/3):ℝ)):=
    (summable_embedding_rpow (-(11/3):ℝ) (by norm_num)).mul_left _
  apply Summable.of_nonneg_of_le (fun h=>by split_ifs <;> positivity) _ hs
  intro h
  split_ifs with hh
  · exact mul_nonneg (div_nonneg hC hDp.le) (Real.rpow_nonneg (norm_nonneg _) _)
  · have hx:0<‖eisEmbedding h‖:=norm_pos_iff.mpr (eisEmbedding_ne_zero hh)
    have he:‖eisEmbedding h‖^(1/3:ℝ)*‖eisEmbedding h‖^(-4:ℝ)=
        ‖eisEmbedding h‖^(-(11/3):ℝ):=by
      rw [←Real.rpow_add hx]
      congr 1
      norm_num
    calc
      _≤(C*‖eisEmbedding h‖^(1/3:ℝ))*‖cuspFrequency h‖^(-4:ℝ):=
        mul_le_mul_of_nonneg_right (hF h hh) (Real.rpow_nonneg (norm_nonneg _) _)
      _=(C/D^(-4:ℝ))*(‖eisEmbedding h‖^(1/3:ℝ)*‖eisEmbedding h‖^(-4:ℝ)):=by
        rw [cuspFrequency,norm_div,Real.div_rpow (norm_nonneg _) (norm_nonneg _)]
        change (C*‖eisEmbedding h‖^(1/3:ℝ))*(‖eisEmbedding h‖^(-4:ℝ)/D^(-4:ℝ))=_
        ring
      _=_:=by rw [he]

theorem three_cusp_coefficients_weighted_summable :
    Summable (fun h:Eis=>if h=0 then (0:ℝ) else
      ‖sourceResidualFourierCoefficient h‖*‖cuspFrequency h‖^(-4:ℝ)) ∧
    ∀side:Bool,Summable (fun h:Eis=>if h=0 then (0:ℝ) else
      ‖ramifiedBesselValue side h‖*‖cuspFrequency h‖^(-4:ℝ)) := by
  obtain ⟨C,hC,hbound⟩:=three_cusp_coefficients_polynomial_bound
  constructor
  · exact coefficient_weighted_summable_of_polynomial _ C hC.le (fun h hh=>(hbound h hh).1)
  · intro side
    exact coefficient_weighted_summable_of_polynomial _ C hC.le (fun h hh=>(hbound h hh).2 side)

lemma derivative_coefficient_weighted_summable (F:Eis→ℂ) (A:ℂ)
    (hF:Summable (fun h:Eis=>if h=0 then (0:ℝ) else ‖F h‖*‖cuspFrequency h‖^(-4:ℝ))) :
    Summable (fun h:Eis=>if h=0 then (0:ℝ) else
      ‖A*cuspFrequency h*star (F h)‖*‖cuspFrequency h‖^(-5:ℝ)) := by
  apply (hF.mul_left ‖A‖).congr
  intro h
  split_ifs with hh
  · simp
  · have hx:0<‖cuspFrequency h‖:=norm_pos_iff.mpr (cuspFrequency_ne_zero h hh)
    have hp:‖cuspFrequency h‖*‖cuspFrequency h‖^(-5:ℝ)=‖cuspFrequency h‖^(-4:ℝ):=by
      conv_lhs => lhs; rw [←Real.rpow_one ‖cuspFrequency h‖]
      rw [←Real.rpow_add hx]
      norm_num
    rw [norm_mul,norm_mul,norm_star]
    calc
      _=‖A‖*‖F h‖*(‖cuspFrequency h‖*‖cuspFrequency h‖^(-5:ℝ)):=by rw [hp];ring
      _=_:=by ring

theorem three_cusp_derivative_coefficients_weighted_summable (A:ℂ) :
    Summable (fun h:Eis=>if h=0 then (0:ℝ) else
      ‖A*cuspFrequency h*star (sourceResidualFourierCoefficient h)‖*‖cuspFrequency h‖^(-5:ℝ)) ∧
    ∀side:Bool,Summable (fun h:Eis=>if h=0 then (0:ℝ) else
      ‖A*cuspFrequency h*star (ramifiedBesselValue side h)‖*‖cuspFrequency h‖^(-5:ℝ)) :=
  ⟨derivative_coefficient_weighted_summable _ A three_cusp_coefficients_weighted_summable.1,
    fun side=>derivative_coefficient_weighted_summable _ A (three_cusp_coefficients_weighted_summable.2 side)⟩

end

section
open ActualEisensteinCubic ConcreteTraceCRT
local notation "Eis" => ActualEisensteinCubic.O

lemma radial_inverse_weight (x:ℝ) (hx:0<x) :
    (x^2)^(-(3/2):ℝ)/x^2=x^(-5:ℝ) := by
  calc
    _=(x^2)^(-(3/2):ℝ)*(x^2)^(-1:ℝ):=by rw [Real.rpow_neg_one];rfl
    _=(x^2)^(-(5/2):ℝ):=by
      rw [←Real.rpow_add (sq_pos_of_pos hx)]
      congr 1
      norm_num
    _=x^(-5:ℝ):=by
      rw [←Real.rpow_natCast_mul hx.le]
      congr 1
      norm_num

lemma radialCoefficient_weighted_summable_of_fourth (F:Eis→ℂ) (A:ℂ)
    (hF:Summable (fun h:Eis=>if h=0 then (0:ℝ) else ‖F h‖*‖cuspFrequency h‖^(-4:ℝ))) :
    Summable (fun h:Eis=>if h=0 then (0:ℝ) else
      ‖A*cuspFrequency h*star (F h)/((‖eisEmbedding h‖^2:ℝ):ℂ)‖*
        (‖eisEmbedding h‖^2)^(-(3/2):ℝ)) := by
  let D:ℝ:=‖(3:ℂ)*eisLam‖
  have hD:0<D:=norm_pos_iff.mpr (mul_ne_zero (by norm_num) eisLam_ne_zero)
  have hDp:D^(-5:ℝ)≠0:=(Real.rpow_pos_of_pos hD _).ne'
  apply ((derivative_coefficient_weighted_summable F A hF).mul_left (D^(-5:ℝ))).congr
  intro h
  split_ifs with hh
  · simp
  · have hx:0<‖eisEmbedding h‖:=norm_pos_iff.mpr (eisEmbedding_ne_zero hh)
    have hf:‖cuspFrequency h‖=‖eisEmbedding h‖/D:=by rw [cuspFrequency,norm_div]
    have hw:D^(-5:ℝ)*(‖eisEmbedding h‖/D)^(-5:ℝ)=‖eisEmbedding h‖^(-5:ℝ):=by
      rw [Real.div_rpow hx.le hD.le]
      field_simp [hDp]
    rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    calc
      _=‖A*cuspFrequency h*star (F h)‖*(D^(-5:ℝ)*(‖eisEmbedding h‖/D)^(-5:ℝ)):=by rw [hf];ring
      _=‖A*cuspFrequency h*star (F h)‖*‖eisEmbedding h‖^(-5:ℝ):=by rw [hw]
      _=_:=by rw [←radial_inverse_weight _ hx];ring

theorem three_cusp_radial_coefficients_weighted_summable (A:ℂ) :
    Summable (fun h:Eis=>if h=0 then (0:ℝ) else
      ‖A*cuspFrequency h*star (sourceResidualFourierCoefficient h)/((‖eisEmbedding h‖^2:ℝ):ℂ)‖*
        (‖eisEmbedding h‖^2)^(-(3/2):ℝ)) ∧
    ∀side:Bool,Summable (fun h:Eis=>if h=0 then (0:ℝ) else
      ‖A*cuspFrequency h*star (ramifiedBesselValue side h)/((‖eisEmbedding h‖^2:ℝ):ℂ)‖*
        (‖eisEmbedding h‖^2)^(-(3/2):ℝ)) :=
  ⟨radialCoefficient_weighted_summable_of_fourth _ A three_cusp_coefficients_weighted_summable.1,
    fun side=>radialCoefficient_weighted_summable_of_fourth _ A (three_cusp_coefficients_weighted_summable.2 side)⟩

end

open ActualEisensteinCubic ConcreteTraceCRT
local notation "Eis" => ActualEisensteinCubic.O

lemma sourceCuspCoefficients_weighted_summable (j:Fin 3) :
    Summable (fun h:Eis=>if h=0 then (0:ℝ) else
      ‖(sourceCuspCoefficients j).value h‖*‖cuspFrequency h‖^(-4:ℝ)) := by
  fin_cases j
  · exact three_cusp_coefficients_weighted_summable.1
  · exact three_cusp_coefficients_weighted_summable.2 false
  · exact three_cusp_coefficients_weighted_summable.2 true

theorem sourceCuspRadialCoefficient_weighted_summable (j:Fin 3) (z:ℂ) :
    Summable (fun h:Eis=>‖sourceCuspRadialCoefficient j z h‖*
      (sourceCuspRadialLength h)^(-(3/2):ℝ)) := by
  let A:ℂ:=(-2*Real.pi*Complex.I)/(sourceCuspScale j:ℂ)^2
  have hs:=radialCoefficient_weighted_summable_of_fourth (sourceCuspCoefficients j).value A
    (sourceCuspCoefficients_weighted_summable j)
  apply hs.congr
  intro h
  by_cases hh:h=0
  · subst h
    simp only [ite_true,sourceCuspRadialCoefficient_zero,norm_zero,zero_mul]
  · rw [ite_eq_right hh,sourceCuspRadialCoefficient_norm,sourceCuspRadialBaseCoefficient,
      sourceCuspRadialLength,ite_eq_right hh]
    congr 1
    apply congrArg norm
    dsimp only [A]
    simp only [div_eq_mul_inv,mul_inv_rev]
    ring

end

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff MatrixGroups

section
open CompletedGauss ConcreteTraceCRT
local notation "Eis" => ActualEisensteinCubic.O

lemma SourceCuspDatum.cuspBarProfile_mellin_entire (d : SourceCuspDatum) :
    (∀s:ℂ,MellinConvergent (cuspBarProfile cubicSourceConjugateFunction d.point) s) ∧
      Differentiable ℂ (mellin (cuspBarProfile cubicSourceConjugateFunction d.point)) :=
  (conjugateSource_levelTwo_three_cusp_mellin_entire d.gamma d.index d.matrix rfl d.lower_ne_zero).1

lemma SourceCuspDatum.reflection_radial (d : SourceCuspDatum) (v:ℝ) (hv:0<v) :
    cuspBarProfile cubicSourceConjugateFunction d.point v=
      d.multiplier*((v:ℂ)^(-2:ℂ)*
        radialBesselProfile sourceCuspRadialLength
          (sourceCuspRadialCoefficient d.index d.dualPoint)
          (sourceCuspRadialScale d.index) ((d.heightScale*v)⁻¹)) := by
  rw [d.reflection v hv,sourceCuspZFamily_eq_radialBesselProfile _ _ _
    (inv_pos.mpr (mul_pos d.heightScale_pos hv)),Complex.cpow_neg,Complex.cpow_ofNat]
  ring

theorem completedBesselProfile_eq_finite_cuspProfiles
    (Ψ:Eis→*ℂ) (Q:Ideal Eis) (hperiod:CanonicalCoefficientClass.FactorsModulo Q Ψ)
    (c:Eis) (hc:c≠0) [Fintype (Eis⧸Ideal.span {c})]
    (hcQ:Ideal.span {c}≤Ideal.span {(9:Eis)}*Q)
    (d:(Eis⧸Ideal.span {c})→SourceCuspDatum)
    (hd:∀h,(d h).point=thetaFourierTranslation c h) (v:ℝ) (hv:0<v) :
    completedBesselProfile Ψ thetaBesselScale v=
      ∑h:Eis⧸Ideal.span {c},
        (thetaDerivativeScalar⁻¹*
          finiteAdditiveFourierCoeff (quotientTrace c hc) (fixedThetaQuotient Ψ c) h)*
        cuspBarProfile cubicSourceConjugateFunction (d h).point v := by
  calc
    _=thetaDerivativeScalar⁻¹*thetaTwistedCuspProfile Ψ c hc v:=by
      rw [thetaTwistedCuspProfile_eq_completedBesselProfile Ψ Q hperiod c hc hcQ v hv,
        ←mul_assoc,inv_mul_cancel₀ thetaDerivativeScalar_ne_zero,one_mul]
    _=_:=by
      simp only [thetaTwistedCuspProfile,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro h hh
      rw [hd h]
      ring

def SourceCuspDatum.smoothedKernel (d:SourceCuspDatum) (W:ℝ→ℂ) (X:ℝ) : ℂ :=
  (d.multiplier*(d.heightScale:ℂ)*
      ((thetaBesselScale/sourceCuspRadialScale d.index:ℝ):ℂ)^2)*
    ∑'n:Eis,sourceCuspRadialCoefficient d.index d.dualPoint n*
      CubicReflectionKernel.paperKernel (Vstar W)
        (27*thetaBesselScale^2*(sourceCuspRadialScale d.index)^2*X*
          sourceCuspRadialLength n/d.heightScale^2)

end

section
open CompletedGauss ConcreteTraceCRT
local notation "Eis" => ActualEisensteinCubic.O

lemma thetaBesselScale_square : thetaBesselScale^2=(1/27:ℝ) := by
  rw [thetaBesselScale_eq,div_pow,one_pow,Real.sq_sqrt (by norm_num)]

lemma sourceCuspRadialScale_ratio (j:Fin 3) :
    thetaBesselScale/sourceCuspRadialScale j=sourceCuspScale j := by
  rw [sourceCuspRadialScale]
  field_simp [thetaBesselScale_pos.ne']

lemma sourceCuspKernel_argument (j:Fin 3) (X r Q:ℝ) :
    27*thetaBesselScale^2*(sourceCuspRadialScale j)^2*X*r/Q^2=
      X*r/(27*(sourceCuspScale j)^2*Q^2) := by
  rw [sourceCuspRadialScale,div_pow,thetaBesselScale_square]
  ring

lemma SourceCuspDatum.smoothedKernel_eq (d:SourceCuspDatum) (W:ℝ→ℂ) (X:ℝ) :
    d.smoothedKernel W X=
      (d.multiplier*(d.heightScale:ℂ)*(sourceCuspScale d.index:ℂ)^2)*
        ∑'n:Eis,sourceCuspRadialCoefficient d.index d.dualPoint n*
          CubicReflectionKernel.paperKernel (Vstar W)
            (X*sourceCuspRadialLength n/(27*(sourceCuspScale d.index)^2*d.heightScale^2)) := by
  simp only [SourceCuspDatum.smoothedKernel,sourceCuspRadialScale_ratio,sourceCuspKernel_argument]

lemma SourceCuspDatum.smoothedKernel_prefactor_norm (d:SourceCuspDatum) :
    ‖d.multiplier*(d.heightScale:ℂ)*(sourceCuspScale d.index:ℂ)^2‖=
      (sourceCuspScale d.index)^2 := by
  rw [norm_mul,norm_mul,norm_pow,d.multiplier_norm,Complex.norm_real,Complex.norm_real,
    Real.norm_eq_abs,Real.norm_eq_abs,abs_of_pos d.heightScale_pos,abs_of_pos (sourceCuspScale_pos _)]
  rw [inv_mul_cancel₀ d.heightScale_pos.ne',one_mul]

lemma SourceCuspDatum.smoothedKernel_prefactor_norm_le (d:SourceCuspDatum) :
    ‖d.multiplier*(d.heightScale:ℂ)*(sourceCuspScale d.index:ℂ)^2‖≤9 := by
  rw [d.smoothedKernel_prefactor_norm]
  rcases d with ⟨G,j,hj⟩
  fin_cases j <;> norm_num [sourceCuspScale]

end

open CompletedGauss ConcreteTraceCRT
local notation "Eis" => ActualEisensteinCubic.O

theorem completedT_finite_smoothed_reflection
    (Ψ:Eis→*ℂ) (hΨ:∀x,‖Ψ x‖≤1)
    (Q:Ideal Eis) (hperiod:CanonicalCoefficientClass.FactorsModulo Q Ψ)
    (c:Eis) (hc:c≠0) [Fintype (Eis⧸Ideal.span {c})]
    (hcQ:Ideal.span {c}≤Ideal.span {(9:Eis)}*Q)
    (d:(Eis⧸Ideal.span {c})→SourceCuspDatum)
    (hd:∀h,(d h).point=thetaFourierTranslation c h)
    (W:ℝ→ℂ) (v0 v1:ℝ) (hv0:0<v0)
    (hWs:Function.support W⊆Set.Icc v0 v1) (hW:ContDiff ℝ ∞ W)
    (X:ℝ) (hX:0<X) :
    completedT Ψ W X=thetaDerivativeScalar⁻¹*
      ∑h:Eis⧸Ideal.span {c},
        finiteAdditiveFourierCoeff (quotientTrace c hc) (fixedThetaQuotient Ψ c) h*
          (d h).smoothedKernel W X := by
  let : Countable Eis := ActualEisensteinCubic.latticeCoordEquiv.injective.countable
  let G:(Eis⧸Ideal.span {c})→ℝ→ℂ:=fun h=>
    cuspBarProfile cubicSourceConjugateFunction (d h).point
  let w:(Eis⧸Ideal.span {c})→ℂ:=fun h=>thetaDerivativeScalar⁻¹*
    finiteAdditiveFourierCoeff (quotientTrace c hc) (fixedThetaQuotient Ψ c) h
  have hFG:∀v:ℝ,0<v→completedBesselProfile Ψ thetaBesselScale v=∑h,w h*G h v:=
    completedBesselProfile_eq_finite_cuspProfiles Ψ Q hperiod c hc hcQ d hd
  have hG (h:Eis⧸Ideal.span {c}) : ∀s:ℂ,MellinConvergent (G h) s:=
    (d h).cuspBarProfile_mellin_entire.1
  have hF:=completedBesselProfile_mellin_entire_of_periodic Ψ Q hperiod c hc hcQ
  have hVs:=Vstar_support W v0 v1 hWs
  have hV:=Vstar_contDiff W v0 v1 hv0 hWs hW
  let J:(Eis⧸Ideal.span {c})→ℝ→ℂ:=fun h t=>
    besselSmoothingIntegrand (G h) thetaBesselScale (Vstar W) X ((-1:ℂ)+t*Complex.I)
  have hi (h:Eis⧸Ideal.span {c}) : Integrable (J h):=
    besselSmoothingIntegrand_reflected_integrable (G h) sourceCuspRadialLength
      sourceCuspRadialLength_pos (sourceCuspRadialCoefficient (d h).index (d h).dualPoint)
      thetaBesselScale (sourceCuspRadialScale (d h).index) (d h).heightScale
      thetaBesselScale_pos (sourceCuspRadialScale_pos _) (d h).heightScale_pos
      (d h).multiplier (d h).reflection_radial
      (sourceCuspRadialCoefficient_weighted_summable _ _) (Vstar W) v0 v1 hv0 hVs hV X hX
  have hireal (h:Eis⧸Ideal.span {c}) : Integrable (fun t:ℝ=>
      besselSmoothingIntegrand (G h) thetaBesselScale (Vstar W) X (((-1:ℝ):ℂ)+t*Complex.I)):=by
    simpa only [Complex.ofReal_neg,Complex.ofReal_one,J] using hi h
  have hleft:=besselSmoothingIntegrand_finite_integrable
    (completedBesselProfile Ψ thetaBesselScale) G w hFG thetaBesselScale (Vstar W) X (-1)
    (fun h t=>hG h _) hireal
  have hshift:=completedT_mellin_shift Ψ hΨ thetaBesselScale thetaBesselScale_pos hF.1 hF.2
    W v0 v1 hv0 hWs hW X hX (-1) (by norm_num) hleft
  have hline (h:Eis⧸Ideal.span {c}) : (1/(2*Real.pi):ℂ)*(∫t:ℝ,J h t)=(d h).smoothedKernel W X:=by
    exact besselSmoothingIntegral_reflected_kernel (G h) sourceCuspRadialLength
      sourceCuspRadialLength_pos (sourceCuspRadialCoefficient (d h).index (d h).dualPoint)
      thetaBesselScale (sourceCuspRadialScale (d h).index) (d h).heightScale
      thetaBesselScale_pos (sourceCuspRadialScale_pos _) (d h).heightScale_pos
      (d h).multiplier (d h).reflection_radial
      (sourceCuspRadialCoefficient_weighted_summable _ _) (Vstar W) v0 v1 hv0 hVs hV X hX
  calc
    _=(1/(2*Real.pi):ℂ)*∫t:ℝ,
        besselSmoothingIntegrand (completedBesselProfile Ψ thetaBesselScale)
          thetaBesselScale (Vstar W) X ((-1:ℂ)+t*Complex.I):=by
      simpa only [Complex.ofReal_neg,Complex.ofReal_one] using hshift
    _=(1/(2*Real.pi):ℂ)*∫t:ℝ,∑h,w h*J h t:=by
      congr 1
      apply integral_congr_ae
      filter_upwards with t
      exact besselSmoothingIntegrand_finite_sum
        (completedBesselProfile Ψ thetaBesselScale) G w hFG thetaBesselScale (Vstar W) X _
        (fun h=>hG h _)
    _=∑h,w h*((1/(2*Real.pi):ℂ)*∫t:ℝ,J h t):=by
      rw [integral_finsetSum Finset.univ (fun h _=>(hi h).const_mul (w h)),Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro h hh
      rw [integral_const_mul]
      ring
    _=∑h,w h*(d h).smoothedKernel W X:=by simp_rw [hline]
    _=_:=by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro h hh
      dsimp only [w]
      ring

theorem completedT_canonical_smoothed_reflection
    (Ψ:Eis→*ℂ) (hΨ:∀x,‖Ψ x‖≤1)
    (Q:Ideal Eis) (hperiod:CanonicalCoefficientClass.FactorsModulo Q Ψ)
    (c:Eis) (hc:c≠0) [Fintype (Eis⧸Ideal.span {c})]
    (hcQ:Ideal.span {c}≤Ideal.span {(9:Eis)}*Q)
    (W:ℝ→ℂ) (v0 v1:ℝ) (hv0:0<v0)
    (hWs:Function.support W⊆Set.Icc v0 v1) (hW:ContDiff ℝ ∞ W)
    (X:ℝ) (hX:0<X) :
    completedT Ψ W X=thetaDerivativeScalar⁻¹*
      ∑h:Eis⧸Ideal.span {c},
        finiteAdditiveFourierCoeff (quotientTrace c hc) (fixedThetaQuotient Ψ c) h*
          (finiteTwistCusp c hc h).smoothedKernel W X :=
  completedT_finite_smoothed_reflection Ψ hΨ Q hperiod c hc hcQ
    (finiteTwistCusp c hc) (finiteTwistCusp_point c hc) W v0 v1 hv0 hWs hW X hX

end

open scoped Classical MatrixGroups Matrix

open CubicKubota EisensteinCuspModThree ConcreteTraceCRT
local notation "Eis" => ActualEisensteinCubic.O

def fixedCuspReduction : SL(2,Eis) →* SL(2,Eis⧸Ideal.span {(3:Eis)}) :=
  Matrix.SpecialLinearGroup.map (n:=Fin 2) (Ideal.Quotient.mk (Ideal.span {(3:Eis)}))

abbrev FixedCuspSector := fixedCuspReduction.range

instance : Finite FixedCuspSector := by
  let : Finite (Eis⧸Ideal.span {(3:Eis)}) := finite_quotient_span (by norm_num : (3:Eis)≠0)
  infer_instance

def fixedCuspSector (M : SL(2,Eis)) : FixedCuspSector :=
  ⟨fixedCuspReduction M,⟨M,rfl⟩⟩

def fixedCuspRepresentative (s : FixedCuspSector) : SL(2,Eis) := s.property.choose

lemma fixedCuspRepresentative_reduction (s : FixedCuspSector) :
    fixedCuspReduction (fixedCuspRepresentative s)=s.val := s.property.choose_spec

lemma fixedCusp_difference_levelThree (M : SL(2,Eis)) :
    M*(fixedCuspRepresentative (fixedCuspSector M))⁻¹∈levelThree := by
  change fixedCuspReduction (M*(fixedCuspRepresentative (fixedCuspSector M))⁻¹)=1
  rw [map_mul,map_inv,fixedCuspRepresentative_reduction]
  change fixedCuspReduction M*(fixedCuspReduction M)⁻¹=1
  exact mul_inv_cancel _

theorem exists_fixed_cusp_decomposition :
    ∃(j:FixedCuspSector→Fin 3) (T:FixedCuspSector→SL(2,Eis))
      (G:SL(2,Eis)→levelTwo),
      (∀s,T s 1 0=0 ∧ IsUnit (T s 0 0) ∧ IsUnit (T s 1 1)) ∧
      ∀M:SL(2,Eis),M=(G M:SL(2,Eis))*cuspRepresentative (j (fixedCuspSector M))*
        T (fixedCuspSector M) := by
  have h (s:FixedCuspSector) := three_cusp_decomposition (fixedCuspRepresentative s)
  choose G0 j T hT hT0 hT1 he using h
  let D : SL(2,Eis)→levelTwo := fun M=>
    ⟨M*(fixedCuspRepresentative (fixedCuspSector M))⁻¹,
      levelThree_le_levelTwo (fixedCusp_difference_levelThree M)⟩
  refine ⟨j,T,fun M=>D M*G0 (fixedCuspSector M),fun s=>⟨hT s,hT0 s,hT1 s⟩,?_⟩
  intro M
  change M=(M*(fixedCuspRepresentative (fixedCuspSector M))⁻¹)*
    (G0 (fixedCuspSector M):SL(2,Eis))*cuspRepresentative (j (fixedCuspSector M))*T (fixedCuspSector M)
  rw [he (fixedCuspSector M)]
  group

end CubicEisenstein

end

end OAI
