import OAI.NumberTheory.DirichletL.Eisenstein.SourceQuotient

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

open scoped BigOperators Classical MatrixGroups Matrix
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CompletedGauss
open PrimaryIdealUnitReindex (GoodIdeal)
local notation "Eis" => ActualEisensteinCubic.O

abbrev PrimaryLower:={c:Eis//(3:Eis)∣c-1}
abbrev OppositeData:=Σc:PrimaryLower,{x:Eis//IsCoprime c.val x}

lemma primaryLower_primary (c:PrimaryLower):lambda^2∣c.val-1:=lambda_sq_dvd_three.trans c.2
lemma primaryLower_ne_zero (c:PrimaryLower):c.val≠0:=primary_ne_zero c.val (primaryLower_primary c)

def oppositeDataToPrimitive (p:OppositeData):PrimitiveRow:=
  ⟨![-3*p.2.val,p.1.val],by
    change IsCoprime (-3*p.2.val) p.1.val ∧ (3:Eis)∣-3*p.2.val ∧ (3:Eis)∣p.1.val-1
    refine ⟨?_,⟨-p.2.val,by ring⟩,p.1.2⟩
    simpa only [neg_mul] using
      ((primary_coprime_three p.1.val (primaryLower_primary p.1)).mul_right p.2.2).symm.neg_left⟩

lemma oppositeDataToPrimitive_bijective:Function.Bijective oppositeDataToPrimitive:=by
  constructor
  · rintro ⟨c,x,hx⟩ ⟨d,y,hy⟩ h
    have hrow:=congrArg Subtype.val h
    have hcd:c=d:=by
      apply Subtype.ext
      exact congrFun hrow 1
    subst d
    have hxy:x=y:=by
      have he:-(3:Eis)*x=-(3:Eis)*y:=congrFun hrow 0
      exact mul_left_cancel₀ (by norm_num : -(3:Eis)≠0) he
    subst y
    rfl
  · intro r
    obtain ⟨t,ht⟩:=r.2.2.1
    let c:PrimaryLower:=⟨r.1 1,r.2.2.2⟩
    have hx:IsCoprime c.val (-t):=by
      have hh:IsCoprime c.val (3*t):=by simpa only [c,ht] using r.2.1.symm
      exact (hh.of_isCoprime_of_dvd_right (dvd_mul_left t 3)).neg_right
    refine ⟨⟨c,-t,hx⟩,Subtype.ext ?_⟩
    funext i
    fin_cases i
    · change -3*(-t)=r.1 0
      rw [ht]
      ring
    · rfl

def oppositeDataEquiv:OppositeData≃PrimitiveRow:=
  Equiv.ofBijective oppositeDataToPrimitive oppositeDataToPrimitive_bijective

def oppositeMatrix:SL(2,ℂ):=⟨!![0,-1;1,0],by simp [Matrix.det_fin_two]⟩

lemma rowOperator_opposite (v:Fin 2→ℂ):rowOperator oppositeMatrix v=![v 1,-v 0]:=by
  rw [rowOperator_apply]
  funext i
  fin_cases i <;> simp [oppositeMatrix,Matrix.vecMul,dotProduct,Fin.sum_univ_two]

def oppositeEisenstein (z:ℂ) (v:ℝ) (hv:0<v) (s:ℂ):ℂ:=
  eisenstein (oppositeMatrix*upperSection z v hv) s

lemma rowHeight_eq_shiftedHeightKernel (z:ℂ) (v:ℝ) (hv:0<v) (s:ℂ)
    (c d:Eis) (hc:c≠0):
    ((v/(‖eisEmbedding c*z+eisEmbedding d‖^2+‖eisEmbedding c‖^2*v^2):ℝ):ℂ)^s=
      ((‖eisEmbedding c‖^2:ℝ):ℂ)^(-s)*
        shiftedHeightKernel v s (eisEmbedding d/eisEmbedding c) z:=by
  have hc':=eisEmbedding_ne_zero hc
  have hnorm:0<‖eisEmbedding c‖^2:=sq_pos_of_pos (norm_pos_iff.mpr hc')
  have hfac:eisEmbedding c*z+eisEmbedding d=eisEmbedding c*(z+eisEmbedding d/eisEmbedding c):=by field_simp
  have heq:v/(‖eisEmbedding c*z+eisEmbedding d‖^2+‖eisEmbedding c‖^2*v^2)=
      ((‖eisEmbedding c‖^2*v)*(1+‖(z+eisEmbedding d/eisEmbedding c)/(v:ℂ)‖^2))⁻¹:=by
    rw [hfac,norm_mul,mul_pow,norm_div,Complex.norm_real,Real.norm_of_nonneg hv.le]
    field_simp
    ;ring
  unfold shiftedHeightKernel hyperbolicKernel
  rw [heq,Complex.ofReal_inv,Complex.inv_cpow_ofReal_nonneg (by positivity),←Complex.cpow_neg]
  rw [Complex.ofReal_mul,Complex.mul_cpow_ofReal_nonneg (mul_nonneg hnorm.le hv.le) (by positivity),
    Complex.ofReal_mul,Complex.mul_cpow_ofReal_nonneg hnorm.le hv.le]
  ring

def oppositeTerm (z:ℂ) (v:ℝ) (s:ℂ) (c x:Eis):ℂ:=
  eisEmbedding (symbol (3*x) c)*
    ((v/(‖eisEmbedding c*z+eisEmbedding (3*x)‖^2+‖eisEmbedding c‖^2*v^2):ℝ):ℂ)^s

lemma oppositeTerm_eq_shifted (z:ℂ) (v:ℝ) (hv:0<v) (s:ℂ)
    (c x:Eis) (hc:c≠0):
    oppositeTerm z v s c x=
      (eisEmbedding (symbol (3*x) c)*((‖eisEmbedding c‖^2:ℝ):ℂ)^(-s))*
        shiftedHeightKernel v s (eisEmbedding (3*x)/eisEmbedding c) z:=by
  rw [oppositeTerm,rowHeight_eq_shiftedHeightKernel z v hv s c (3*x) hc]
  ring

lemma opposite_summand (z:ℂ) (v:ℝ) (hv:0<v) (s:ℂ) (p:OppositeData):
    summand (oppositeMatrix*upperSection z v hv) s
      (primitiveRowEquiv.symm (oppositeDataEquiv p))=
      oppositeTerm z v s p.1.val p.2.val:=by
  let r:Fin 2→ℂ:=![eisEmbedding p.1.val,eisEmbedding (3*p.2.val)]
  have hr:rowOperator oppositeMatrix
      (embeddedRow (primitiveRowEquiv.symm (oppositeDataEquiv p)))=r:=by
    rw [embeddedRow, primitiveRowEquiv_symm_row, rowOperator_opposite]
    funext i
    fin_cases i <;>
      simp [oppositeDataEquiv, Equiv.ofBijective_apply, oppositeDataToPrimitive, r, map_mul]
  have hr0:r≠0:=by
    intro hh
    have he:=congrFun hh 0
    exact eisEmbedding_ne_zero (primaryLower_ne_zero p.1) he
  have hp:0<heightDenominator z v r:=heightDenominator_pos z v hv r hr0
  have hphase:(cosetCharacter (primitiveRowEquiv.symm (oppositeDataEquiv p)))⁻¹=
      eisEmbedding (symbol (3*p.2.val) p.1.val):=by
    rw [inverse_cosetCharacter_eq_row_symbol,primitiveRowEquiv_symm_row]
    change eisEmbedding (symbol (-3*p.2.val) p.1.val)=_
    rw [neg_mul,symbol_neg_numerator _ _ (primaryLower_primary p.1)]
  rw [summand,←rowOperator_mul,hr,rowEnergy_upperSection,hphase]
  change _=eisEmbedding (symbol (3*p.2.val) p.1.val)*
    ((v/heightDenominator z v r:ℝ):ℂ)^s
  have hi:((v/heightDenominator z v r:ℝ):ℂ)=
      (((heightDenominator z v r/v:ℝ):ℂ))⁻¹:=by
    simp only [Complex.ofReal_div,inv_div]
  rw [hi,Complex.inv_cpow_ofReal_nonneg (div_nonneg hp.le hv.le),Complex.cpow_neg]

theorem oppositeEisenstein_eq_rows (z:ℂ) (v:ℝ) (hv:0<v) (s:ℂ):
    oppositeEisenstein z v hv s=∑'p:OppositeData,oppositeTerm z v s p.1.val p.2.val:=by
  rw [oppositeEisenstein,eisenstein,←primitiveRowEquiv.symm.tsum_eq,
    ←oppositeDataEquiv.tsum_eq]
  exact tsum_congr (opposite_summand z v hv s)

theorem opposite_rows_summable_norm (z:ℂ) (v:ℝ) (hv:0<v) (s:ℂ) (hs:2<s.re):
    Summable (fun p:OppositeData=>‖oppositeTerm z v s p.1.val p.2.val‖):=by
  have hh:=(oppositeDataEquiv.trans primitiveRowEquiv.symm).summable_iff.mpr
    (summable_norm_summand (oppositeMatrix*upperSection z v hv) s hs)
  exact hh.congr (fun p=>congrArg norm (opposite_summand z v hv s p))

def primaryLowerIdealEquiv:PrimaryLower≃GoodIdeal where
  toFun c:=⟨Ideal.span {c.val},by rw [primaryGenerator_span c.val (primaryLower_ne_zero c) (primaryLower_primary c)];exact primaryLower_ne_zero c⟩
  invFun I:=⟨primaryGenerator I.val,three_dvd_primary_sub_one _ (primaryGenerator_spec I.val I.2).2⟩
  left_inv c:=Subtype.ext (primaryGenerator_span c.val (primaryLower_ne_zero c) (primaryLower_primary c))
  right_inv I:=Subtype.ext (primaryGenerator_spec I.val I.2).1

end

section

open scoped BigOperators Classical
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CompletedGauss
open PrimaryIdealUnitReindex (GoodIdeal)
local notation "Eis" => ActualEisensteinCubic.O

abbrev CoprimeElement (c:Eis):={x:Eis//IsCoprime c x}

def cubicResidueElementMap (c:Eis) (p:CubicUnitResidue c×Eis):CoprimeElement c:=
  ⟨GaussianShiftedPartition.representative c p.1.val+c*p.2,by
    apply (isUnit_quotient_span_iff c _).mp
    have hc:Ideal.Quotient.mk (Ideal.span {c}) c=0:=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
    simpa only [map_add,map_mul,hc,zero_mul,add_zero,
      GaussianShiftedPartition.representative_spec] using p.1.2⟩

lemma cubicResidueElementMap_bijective (c:Eis) (hc:c≠0):
    Function.Bijective (cubicResidueElementMap c):=by
  have hmod (r:CubicUnitResidue c) (n:Eis):
      Ideal.Quotient.mk (Ideal.span {c})
        (GaussianShiftedPartition.representative c r.val+c*n)=r.val:=by
    have hzero:Ideal.Quotient.mk (Ideal.span {c}) c=0:=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
    rw [map_add,map_mul,hzero,zero_mul,add_zero,GaussianShiftedPartition.representative_spec]
  constructor
  · rintro ⟨r,n⟩ ⟨t,m⟩ h
    have he:=congrArg Subtype.val h
    change GaussianShiftedPartition.representative c r.val+c*n=
      GaussianShiftedPartition.representative c t.val+c*m at he
    have hrt:r=t:=Subtype.ext (by
      simpa only [hmod] using congrArg (Ideal.Quotient.mk (Ideal.span {c})) he)
    subst t
    have hnm:n=m:=mul_left_cancel₀ hc (add_left_cancel he)
    subst m
    rfl
  · intro x
    let r:CubicUnitResidue c:=⟨Ideal.Quotient.mk (Ideal.span {c}) x.val,
      (isUnit_quotient_span_iff c x.val).mpr x.2⟩
    have hdiv:c∣x.val-GaussianShiftedPartition.representative c r.val:=by
      apply Ideal.mem_span_singleton.mp
      apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp
      exact (GaussianShiftedPartition.representative_spec c r.val).symm
    obtain ⟨n,hn⟩:=hdiv
    refine ⟨(r,n),Subtype.ext ?_⟩
    change GaussianShiftedPartition.representative c r.val+c*n=x.val
    linear_combination -hn

def cubicResidueElementEquiv (c:Eis) (hc:c≠0):
    CubicUnitResidue c×Eis≃CoprimeElement c:=
  Equiv.ofBijective (cubicResidueElementMap c) (cubicResidueElementMap_bijective c hc)

lemma oppositeTerm_shift (z:ℂ) (v:ℝ) (s:ℂ) (c x n:Eis):
    oppositeTerm z v s c (x+c*n)=oppositeTerm (z+3*eisEmbedding n) v s c x:=by
  have hsym:symbol (3*(x+c*n)) c=symbol (3*x) c:=symbol_congr ⟨3*n,by ring⟩
  have harg:eisEmbedding c*z+eisEmbedding (3*(x+c*n))=
      eisEmbedding c*(z+3*eisEmbedding n)+eisEmbedding (3*x):=by
    simp only [map_mul,map_add,map_ofNat]
    ring
  rw [oppositeTerm,oppositeTerm,hsym,harg]

def oppositeGaussSum (h c:Eis):ℂ:=
  ∑'r:CubicUnitResidue c,
    eisEmbedding (symbol (3*GaussianShiftedPartition.representative c r.val) c)*
      residueAdditive h c (3*GaussianShiftedPartition.representative c r.val)

theorem oppositeGaussSum_eq (h:Eis) (c:PrimaryLower):
    oppositeGaussSum h c.val=cubicUnitGaussSum (9*h) c.val:=by
  have hp:=primaryLower_primary c
  have hc:=primaryLower_ne_zero c
  have he:oppositeGaussSum h c.val=
      eisEmbedding (symbol 3 c.val)*cubicUnitGaussSum h c.val:=by
    rw [oppositeGaussSum,cubicUnitGaussSum,←tsum_mul_left]
    apply tsum_congr
    intro r
    rw [symbol_mul_numerator _ _ _ hp,map_mul]
    have hadd:residueAdditive h c.val (3*GaussianShiftedPartition.representative c.val r.val)=
        residueAdditive (3*h) c.val (GaussianShiftedPartition.representative c.val r.val):=by
      unfold residueAdditive cuspFrequency
      simp only [map_mul,map_ofNat]
      congr 1
      ring
    rw [hadd]
    ring
  rw [he]
  have hs:=cubicUnitGaussSum_phase_shift h 1 c.val hc hp (by
    simpa only [mul_one] using (primary_coprime_three c.val hp).symm)
  simpa only [symbol_one_numerator c.val hp,map_one,one_mul,mul_one,mul_comm h 9] using hs

def oppositeArithmeticSeries (s:ℂ) (h:Eis):ℂ:=
  ∑'c:PrimaryLower,((‖eisEmbedding c.val‖^2:ℝ):ℂ)^(-s)*oppositeGaussSum h c.val

theorem oppositeArithmeticSeries_eq (s:ℂ) (h:Eis):
    oppositeArithmeticSeries s h=unramifiedCubicGaussSeries s (9*h):=by
  rw [oppositeArithmeticSeries,←primaryLowerIdealEquiv.symm.tsum_eq,unramifiedCubicGaussSeries]
  apply tsum_congr
  intro I
  rw [oppositeGaussSum_eq]
  change ((‖eisEmbedding (primaryGenerator I.val)‖^2:ℝ):ℂ)^(-s)*
    cubicUnitGaussSum (9*h) (primaryGenerator I.val)=_
  rw [eisEmbedding_norm_sq_eq_absNorm_span,(primaryGenerator_spec I.val I.2).1,
    Complex.ofReal_natCast]

end

section

open MeasureTheory Set Filter Module
open scoped BigOperators Classical ENNReal MatrixGroups Matrix
open ActualEisensteinCubic ConcreteTraceCRT

lemma continuous_inverse_fixed_left_operator (a:SL(2,ℂ)) (v:ℝ) (hv:0<v):
    Continuous (fun z:ℂ=>rowOperator (a*upperSection z v hv)⁻¹):=by
  have he (z:ℂ):rowOperator (a*upperSection z v hv)⁻¹=
      (rowOperator a⁻¹).comp (rowOperator (upperSection z v hv)⁻¹):=by
    ext u
    simp only [mul_inv_rev,ContinuousLinearMap.comp_apply,rowOperator_mul]
  simp_rw [he]
  exact continuous_const.clm_comp (continuous_inverse_upper_operator v hv)

lemma exists_fixed_left_rowBound (a:SL(2,ℂ)) (v:ℝ) (hv:0<v):
    ∃C:ℝ,0<C ∧ ∀z∈periodDomain,rowBound (a*upperSection z v hv)≤C:=by
  have hc:Continuous (fun z:ℂ=>rowBound (a*upperSection z v hv)):=
    continuous_const.mul (continuous_const.add (continuous_inverse_fixed_left_operator a v hv).norm)
  let R:ℝ:=∑i:Fin 2,‖periodBasis i‖
  obtain ⟨C,hC⟩:=(isCompact_closedBall (0:ℂ) R).bddAbove_image hc.continuousOn
  refine ⟨max 1 C,lt_of_lt_of_le (by norm_num) (le_max_left _ _),?_⟩
  intro z hz
  apply (hC ?_).trans (le_max_right _ _)
  exact ⟨z,by simpa only [Metric.mem_closedBall,dist_zero_right] using norm_mem_periodDomain z hz,rfl⟩

lemma continuous_fixed_left_summand (a:SL(2,ℂ)) (v:ℝ) (hv:0<v)
    (s:ℂ) (x:CuspCosets):
    Continuous (fun z:ℂ=>summand (a*upperSection z v hv) s x):=by
  simp_rw [summand,←rowOperator_mul,rowEnergy_upperSection]
  apply continuous_const.mul
  apply Continuous.cpow
  · apply Complex.continuous_ofReal.comp
    unfold heightDenominator
    fun_prop
  · exact continuous_const
  · intro z
    apply Complex.ofReal_mem_slitPlane.mpr
    exact div_pos (heightDenominator_pos z v hv _
      (rowOperator_ne_zero a _ (embeddedRow_ne_zero x))) hv

lemma fixed_left_summable_majorant (a:SL(2,ℂ)) (v:ℝ) (hv:0<v)
    (s:ℂ) (hs:2<s.re):
    ∃M:CuspCosets→ℝ,Summable M ∧ (∀x,0≤M x) ∧
      ∀z∈periodDomain,∀x,‖summand (a*upperSection z v hv) s x‖≤M x:=by
  obtain ⟨C,hC,hbound⟩:=exists_fixed_left_rowBound a v hv
  refine ⟨fun x=>C^(2*s.re)*‖rowCoordinates (cosetRow x)‖^(-(2*s.re)),?_,?_,?_⟩
  · have hsumm:=summable_integer_four_rpow (2*s.re) (by linarith)
    have hinj:Function.Injective (fun x:CuspCosets=>rowCoordinates (cosetRow x)):=
      rowCoordinates_injective.comp cosetRow_injective
    exact (hsumm.comp_injective hinj).mul_left _
  · intro x
    positivity
  · intro z hz x
    apply (norm_summand_bound (a*upperSection z v hv) s (by linarith) x).trans
    exact mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow (rowBound_pos _).le (hbound z hz) (by linarith)) (by positivity)

theorem hasSum_integral_fixed_left_Eisenstein (a:SL(2,ℂ)) (v:ℝ) (hv:0<v)
    (s freq:ℂ) (hs:2<s.re):
    HasSum (fun x:CuspCosets=>∫z in periodDomain,
      summand (a*upperSection z v hv) s x*ShortDraftTrace.breveE (-freq*z))
      (∫z in periodDomain,eisenstein (a*upperSection z v hv) s*ShortDraftTrace.breveE (-freq*z)):=by
  let:Countable CuspCosets:=(rowCoordinates_injective.comp cosetRow_injective).countable
  let:=periodDomain_finiteMeasure
  obtain ⟨M,hM,hMnonneg,hbound⟩:=fixed_left_summable_majorant a v hv s hs
  have hchar:Continuous (fun z:ℂ=>ShortDraftTrace.breveE (-freq*z)):=by
    change Continuous (fun z:ℂ=>Complex.exp (2*Real.pi*Complex.I*((-freq*z)+starRingEnd ℂ (-freq*z))))
    fun_prop
  exact hasSum_integral_of_dominated_convergence
    («μ»:=volume.restrict periodDomain)
    (fun (x:CuspCosets) (_:ℂ)=>M x)
    (fun x=>((continuous_fixed_left_summand a v hv s x).mul hchar).aestronglyMeasurable.restrict)
    (fun x=>(ae_restrict_mem periodDomain_measurable).mono fun z hz=>by
      simpa only [Pi.mul_apply,norm_mul,breveE_norm,mul_one] using hbound z hz x)
    (Eventually.of_forall fun _=>hM)
    (integrable_const (∑'x,M x))
    (Eventually.of_forall fun z=>(summable_summand (a*upperSection z v hv) s hs).hasSum.mul_right
      (ShortDraftTrace.breveE (-freq*z)))

end

section

open MeasureTheory Set Filter
open scoped BigOperators Classical ENNReal
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CompletedGauss
local notation "Eis" => ActualEisensteinCubic.O

def oppositeIntegral (v:ℝ) (s freq:ℂ) (c x:Eis):ℂ:=
  ∫z in periodDomain,oppositeTerm z v s c x*ShortDraftTrace.breveE (-freq*z)

theorem hasSum_oppositeIntegrals (v:ℝ) (hv:0<v) (s freq:ℂ) (hs:2<s.re):
    HasSum (fun p:OppositeData=>oppositeIntegral v s freq p.1.val p.2.val)
      (∫z in periodDomain,oppositeEisenstein z v hv s*ShortDraftTrace.breveE (-freq*z)):=by
  have hh:=(oppositeDataEquiv.trans primitiveRowEquiv.symm).hasSum_iff.mpr
    (hasSum_integral_fixed_left_Eisenstein oppositeMatrix v hv s freq hs)
  apply hh.congr_fun
  intro p
  apply integral_congr_ae
  exact Eventually.of_forall fun z=>by
    dsimp only [Equiv.trans_apply]
    rw [opposite_summand]

lemma oppositeTerm_integrable (v:ℝ) (hv:0<v) (s:ℂ) (hs:1<s.re)
    (c x:Eis) (hc:c≠0):Integrable (fun z=>oppositeTerm z v s c x):=by
  simp_rw [oppositeTerm_eq_shifted _ v hv s c x hc]
  exact (shiftedHeightKernel_integrable v hv s _ hs).const_mul _

lemma oppositeIntegral_sum_translate (v:ℝ) (hv:0<v) (s:ℂ) (hs:1<s.re)
    (h c x:Eis) (hc:c≠0):
    (∑'n:Eis,oppositeIntegral v s (cuspFrequency h) c (x+c*n))=
      ∫z:ℂ,oppositeTerm z v s c x*ShortDraftTrace.breveE (-cuspFrequency h*z):=by
  have hint:=trace_mul_integrable (fun z=>oppositeTerm z v s c x)
    (oppositeTerm_integrable v hv s hs c x hc) (cuspFrequency h)
  rw [integral_eq_period_integrals _ hint]
  apply tsum_congr
  intro n
  apply integral_congr_ae
  exact Eventually.of_forall fun z=>by
    dsimp only [oppositeIntegral]
    rw [oppositeTerm_shift,cuspFrequency_negative_period]

lemma oppositeTerm_fourier_integral (v:ℝ) (hv:0<v) (s freq:ℂ)
    (c x:Eis) (hc:c≠0):
    (∫z:ℂ,oppositeTerm z v s c x*ShortDraftTrace.breveE (-freq*z))=
      ((v:ℂ)^(2-s)*sourceFourierKernel s (freq*v))*
        ((‖eisEmbedding c‖^2:ℝ):ℂ)^(-s)*
        (eisEmbedding (symbol (3*x) c)*
          ShortDraftTrace.breveE (freq*eisEmbedding (3*x)/eisEmbedding c)):=by
  simp_rw [oppositeTerm_eq_shifted _ v hv s c x hc,mul_assoc]
  rw [integral_const_mul,integral_const_mul,
    traceIntegral_shiftedHeightKernel v hv s (eisEmbedding (3*x)/eisEmbedding c) freq]
  ring_nf

lemma oppositeDenominator_integral_formula (v:ℝ) (hv:0<v) (s:ℂ) (hs:2<s.re)
    (h:Eis) (c:PrimaryLower):
    (∑'x:CoprimeElement c.val,oppositeIntegral v s (cuspFrequency h) c.val x.val)=
      ((v:ℂ)^(2-s)*sourceFourierKernel s (cuspFrequency h*v))*
        ((‖eisEmbedding c.val‖^2:ℝ):ℂ)^(-s)*oppositeGaussSum h c.val:=by
  have hf:Summable (fun x:CoprimeElement c.val=>oppositeIntegral v s (cuspFrequency h) c.val x.val):=
    (hasSum_oppositeIntegrals v hv s (cuspFrequency h) hs).summable.sigma_factor c
  have hsum:=(cubicResidueElementEquiv c.val (primaryLower_ne_zero c)).summable_iff.mpr hf
  change Summable (fun q:CubicUnitResidue c.val×Eis=>
    oppositeIntegral v s (cuspFrequency h) c.val
      (GaussianShiftedPartition.representative c.val q.1.val+c.val*q.2)) at hsum
  rw [←(cubicResidueElementEquiv c.val (primaryLower_ne_zero c)).tsum_eq]
  change (∑'q:CubicUnitResidue c.val×Eis,
    oppositeIntegral v s (cuspFrequency h) c.val
      (GaussianShiftedPartition.representative c.val q.1.val+c.val*q.2))=_
  rw [hsum.tsum_prod]
  change (∑'r:CubicUnitResidue c.val,∑'n:Eis,
    oppositeIntegral v s (cuspFrequency h) c.val
      (GaussianShiftedPartition.representative c.val r.val+c.val*n))=_
  simp_rw [oppositeIntegral_sum_translate v hv s (by linarith) h c.val _ (primaryLower_ne_zero c),
    oppositeTerm_fourier_integral v hv s (cuspFrequency h) c.val _ (primaryLower_ne_zero c)]
  exact tsum_mul_left

lemma unramifiedCubicGaussSeries_twentySeven (s:ℂ) (h:Eis):
    unramifiedCubicGaussSeries s (27*h)=unramifiedCubicGaussSeries s h:=by
  apply tsum_congr
  intro I
  congr 1
  have hp:lambda^2∣primaryGenerator I.val-1:=(primaryGenerator_spec I.val I.2).2
  simpa only [show (3:Eis)^3=27 by norm_num,mul_comm h 27] using
    cubicUnitGaussSum_cube_shift h (primaryGenerator I.val) 3 I.2 hp
      (primary_coprime_three _ hp)

theorem oppositeEisenstein_fourier (v:ℝ) (hv:0<v) (s:ℂ) (hs:2<s.re) (h:Eis):
    (∫z in periodDomain,oppositeEisenstein z v hv s*
      ShortDraftTrace.breveE (-cuspFrequency h*z))=
      ((v:ℂ)^(2-s)*sourceFourierKernel s (cuspFrequency h*v))*
        unramifiedCubicGaussSeries s (9*h):=by
  have hh:=hasSum_oppositeIntegrals v hv s (cuspFrequency h) hs
  rw [←hh.tsum_eq,hh.summable.tsum_sigma]
  simp_rw [oppositeDenominator_integral_formula v hv s hs h]
  rw [←oppositeArithmeticSeries_eq s h,oppositeArithmeticSeries]
  have he (c:PrimaryLower):
      (v:ℂ)^(2-s)*sourceFourierKernel s (cuspFrequency h*v)*
        ((‖eisEmbedding c.val‖^2:ℝ):ℂ)^(-s)*oppositeGaussSum h c.val=
      ((v:ℂ)^(2-s)*sourceFourierKernel s (cuspFrequency h*v))*
        (((‖eisEmbedding c.val‖^2:ℝ):ℂ)^(-s)*oppositeGaussSum h c.val):=by ring
  simp_rw [he]
  exact tsum_mul_left

theorem oppositeEisenstein_fourier_unramified (v:ℝ) (hv:0<v) (s:ℂ) (hs:2<s.re) (h:Eis):
    (∫z in periodDomain,oppositeEisenstein z v hv s*
      ShortDraftTrace.breveE (-(eisEmbedding h/eisLam)*z))=
      ((v:ℂ)^(2-s)*sourceFourierKernel s ((eisEmbedding h/eisLam)*v))*
        unramifiedCubicGaussSeries s h:=by
  have hf:cuspFrequency (3*h)=eisEmbedding h/eisLam:=by
    unfold cuspFrequency
    rw [map_mul,map_ofNat]
    field_simp
  have hh:=oppositeEisenstein_fourier v hv s hs (3*h)
  rw [hf,show (9:Eis)*(3*h)=27*h by ring,unramifiedCubicGaussSeries_twentySeven] at hh
  exact hh

end

open Filter MeasureTheory
open scoped BigOperators Classical Topology ENNReal

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

abbrev PeriodTorusL2 := Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 2)))

def periodIocCube : Set (Fin 2→ℝ) := {x | ∀i,x i∈Set.Ioc 0 (0+1)}

def periodCovolumeDensity : ℝ≥0∞ := ENNReal.ofReal (2/(9*Real.sqrt 3))

lemma periodCovolumeDensity_ne_zero : periodCovolumeDensity≠0 := by
  exact ne_of_gt (ENNReal.ofReal_pos.mpr (by positivity))

lemma periodIocCube_measurable : MeasurableSet periodIocCube :=
  MeasurableSet.univ_pi' (fun _ => measurableSet_Ioc)

lemma periodIocCube_ae : periodCube=ᵐ[volume]periodIocCube := by
  simpa only [periodIocCube,zero_add] using periodCube_ae_Ioc

def periodSection (t : UnitAddTorus (Fin 2)) : ℂ :=
  periodVector ((UnitAddTorus.measurableEquivPiIoc (fun _ : Fin 2 => (0:ℝ)) t).val)

lemma periodSection_measurableEmbedding : MeasurableEmbedding periodSection :=
  periodVector.toHomeomorph.toMeasurableEquiv.measurableEmbedding.comp
    ((MeasurableEmbedding.subtype_coe periodIocCube_measurable).comp
      (UnitAddTorus.measurableEquivPiIoc (fun _ : Fin 2 => (0:ℝ))).measurableEmbedding)

lemma periodTorus_measurable : Measurable periodTorus := by
  apply Measurable.of_eval
  intro i
  exact AddCircle.measurable_mk'.comp
    ((measurable_pi_apply i).comp periodBasis.equivFunL.continuous.measurable)

lemma periodTorus_section (t : UnitAddTorus (Fin 2)) : periodTorus (periodSection t)=t := by
  rw [periodSection,periodTorus_periodVector]
  exact (UnitAddTorus.measurableEquivPiIoc (fun _ : Fin 2 => (0:ℝ))).symm_apply_apply t

lemma periodVector_Ioc_measurePreserving :
    MeasurePreserving periodVector (volume.restrict periodIocCube)
      (periodCovolumeDensity • volume.restrict periodDomain) := by
  refine ⟨periodVector.continuous.measurable,?_⟩
  rw [←Measure.restrict_congr_set periodIocCube_ae,←periodVector_preimage_domain,
    ←Measure.restrict_map periodVector.continuous.measurable periodDomain_measurable,
    periodVector_map_volume,Measure.restrict_smul]
  rfl

lemma periodSection_measurePreserving :
    MeasurePreserving periodSection volume
      (periodCovolumeDensity • volume.restrict periodDomain) :=
  periodVector_Ioc_measurePreserving.comp
    ((measurePreserving_subtype_coe periodIocCube_measurable).comp
      (UnitAddTorus.measurePreserving_equivPiIoc (fun _ : Fin 2 => (0:ℝ))))

lemma periodTorus_measurePreserving :
    MeasurePreserving periodTorus (periodCovolumeDensity • volume.restrict periodDomain) volume := by
  refine ⟨periodTorus_measurable,?_⟩
  rw [←periodSection_measurePreserving.map_eq,
    Measure.map_map periodTorus_measurable periodSection_measurableEmbedding.measurable]
  have he : periodTorus ∘ periodSection=id := funext periodTorus_section
  rw [he,Measure.map_id]

lemma periodSection_torus_ae :
    (fun z => periodSection (periodTorus z))=ᵐ[volume.restrict periodDomain] (fun z : ℂ => z) := by
  apply (Measure.ae_ennreal_smul_measure_iff periodCovolumeDensity_ne_zero).mp
  rw [←periodSection_measurePreserving.map_eq]
  apply periodSection_measurableEmbedding.ae_map_iff.mpr
  exact Eventually.of_forall (fun t => by dsimp only; rw [periodTorus_section])

lemma periodSection_memLp (f : ℂ→ℂ) (hf : MemLp f 2 (volume.restrict periodDomain)) :
    MemLp (f ∘ periodSection) 2 volume :=
  (hf.smul_measure (by simp [periodCovolumeDensity])).comp_measurePreserving
    periodSection_measurePreserving

def periodTorusL2Lift (f : ℂ→ℂ) (hf : MemLp f 2 (volume.restrict periodDomain)) : PeriodTorusL2 :=
  (periodSection_memLp f hf).toLp (f ∘ periodSection)

lemma periodTorusL2Lift_ae (f : ℂ→ℂ) (hf : MemLp f 2 (volume.restrict periodDomain)) :
    periodTorusL2Lift f hf=ᵐ[volume]f ∘ periodSection :=
  MemLp.coeFn_toLp (periodSection_memLp f hf)

lemma periodTorusL2Lift_pullback (f : ℂ→ℂ) (hf : MemLp f 2 (volume.restrict periodDomain)) :
    (fun z => periodTorusL2Lift f hf (periodTorus z))=ᵐ[volume.restrict periodDomain]f := by
  have he := periodTorus_measurePreserving.quasiMeasurePreserving.ae_eq_comp (periodTorusL2Lift_ae f hf)
  have he' := (Measure.ae_ennreal_smul_measure_iff periodCovolumeDensity_ne_zero).mp he
  filter_upwards [he',periodSection_torus_ae] with z hz hsec
  change periodTorusL2Lift f hf (periodTorus z)=f (periodSection (periodTorus z)) at hz
  rw [hsec] at hz
  exact hz

lemma periodTorusL2Lift_frequency_integral (f : ℂ→ℂ)
    (hf : MemLp f 2 (volume.restrict periodDomain)) (h : ActualEisensteinCubic.O) :
    (∫z in periodDomain,periodTorusL2Lift f hf (periodTorus z)*
      ShortDraftTrace.breveE (-cuspFrequency h*z))=
    ∫z in periodDomain,f z*ShortDraftTrace.breveE (-cuspFrequency h*z) := by
  apply integral_congr_ae
  filter_upwards [periodTorusL2Lift_pullback f hf] with z hz
  rw [hz]

lemma periodTorusL2Lift_fourierCoeff (f : ℂ→ℂ) (hf : MemLp f 2 (volume.restrict periodDomain))
    (n : Fin 2→ℤ) :
    UnitAddTorus.mFourierCoeff (periodTorusL2Lift f hf) n=(2/(9*Real.sqrt 3):ℝ) •
      (∫z in periodDomain,f z*ShortDraftTrace.breveE (-cuspFrequency (periodFrequencyEquiv n)*z)) := by
  rw [periodTorus_fourierCoeff]
  congr 1
  apply integral_congr_ae
  filter_upwards [periodTorusL2Lift_pullback f hf] with z hz
  rw [hz]

theorem periodDomain_L2_ext (f g : ℂ→ℂ)
    (hf : MemLp f 2 (volume.restrict periodDomain))
    (hg : MemLp g 2 (volume.restrict periodDomain))
    (h : ∀h : ActualEisensteinCubic.O,
      (∫z in periodDomain,f z*ShortDraftTrace.breveE (-cuspFrequency h*z))=
        ∫z in periodDomain,g z*ShortDraftTrace.breveE (-cuspFrequency h*z)) :
    f=ᵐ[volume.restrict periodDomain]g := by
  have he : periodTorusL2Lift f hf=periodTorusL2Lift g hg := by
    apply periodTorus_L2_ext
    intro hfreq
    rw [periodTorusL2Lift_frequency_integral,periodTorusL2Lift_frequency_integral,h]
  filter_upwards [periodTorusL2Lift_pullback f hf,periodTorusL2Lift_pullback g hg] with z hz hz'
  rw [←hz,←hz',he]

end CubicEisenstein

end

end OAI
