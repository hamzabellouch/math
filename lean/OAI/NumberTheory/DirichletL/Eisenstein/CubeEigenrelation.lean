import OAI.NumberTheory.DirichletL.Eisenstein.CorrespondenceEnergy

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

open scoped Classical MatrixGroups BigOperators
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CubicKubota
local notation "Eis" => ActualEisensteinCubic.O

lemma positive_cube_cpow_third (r:ℝ) (hr:0<r) :
    ((r^3:ℝ):ℂ)^(1/3:ℂ)=(r:ℂ) := by
  calc
    _=(((r^3)^(1/3:ℝ):ℝ):ℂ):=by
      simpa only [Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_ofNat] using
        (Complex.ofReal_cpow (pow_nonneg hr.le 3) (1/3)).symm
    _=_:=by
      congr 1
      rw [←Real.rpow_natCast_mul hr.le 3]
      norm_num

lemma cubicBesselNormalizer_mul_cube (h p:Eis) (hp:p≠0) :
    cubicBesselNormalizer (h*p^3)=(‖eisEmbedding p‖:ℂ)*cubicBesselNormalizer h := by
  have hr:0<‖eisEmbedding p‖:=norm_pos_iff.mpr (eisEmbedding_ne_zero hp)
  have hf:‖cuspFrequency (h*p^3)‖=‖cuspFrequency h‖*‖eisEmbedding p‖^3:=by
    rw [cuspFrequency_mul_right,norm_mul,map_pow,norm_pow]
  have ha:0≤2*Real.pi*‖cuspFrequency h‖:=by positivity
  have he:(2*Real.pi*‖cuspFrequency (h*p^3)‖:ℂ)=
      ((‖eisEmbedding p‖^3:ℝ):ℂ)*((2*Real.pi*‖cuspFrequency h‖:ℝ):ℂ):=by
    rw [hf]
    push_cast
    ring
  unfold cubicBesselNormalizer
  rw [he,Complex.mul_cpow_ofReal_nonneg (pow_nonneg hr.le 3) ha,
    positive_cube_cpow_third _ hr]
  push_cast
  ring

lemma eisenstein_norm_eq_sqrt_norm (p:Eis) :
    ‖eisEmbedding p‖=Real.sqrt (Ideal.absNorm (Ideal.span {p}):ℝ) := by
  rw [←eisEmbedding_norm_sq_eq_absNorm_span,Real.sqrt_sq (norm_nonneg _)]

theorem sourceResidualFourierCoefficient_cube_sqrt (p:Eis) (hp:p≠0)
    (hU:∀w:HyperbolicSpace,cubeAverage p hp cubicSourceResidualFunction w=
      (Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹*cubicSourceResidualFunction w)
    (h:Eis) (hh:h≠0) :
    sourceResidualFourierCoefficient (h*p^3)=
      (Real.sqrt (Ideal.absNorm (Ideal.span {p}):ℝ):ℂ)*sourceResidualFourierCoefficient h := by
  rw [sourceResidualFourierCoefficient_cube_of_eigenrelation p hp hU h hh,
    eisenstein_norm_eq_sqrt_norm]

theorem sourceArithmeticResidue_cube_of_eigenrelation (p:Eis) (hp:p≠0)
    (hU:∀w:HyperbolicSpace,cubeAverage p hp cubicSourceResidualFunction w=
      (Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹*cubicSourceResidualFunction w)
    (h:Eis) (hh:h≠0) : sourceArithmeticResidue (h*p^3)=sourceArithmeticResidue h := by
  have ht:=sourceResidualFourierCoefficient_cube_of_eigenrelation p hp hU h hh
  unfold sourceResidualFourierCoefficient at ht
  rw [cubicBesselNormalizer_mul_cube h p hp] at ht
  have hr:(‖eisEmbedding p‖:ℂ)≠0:=Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (eisEmbedding_ne_zero hp))
  apply mul_left_cancel₀ (mul_ne_zero hr (cubicBesselNormalizer_ne_zero h hh))
  simpa only [mul_assoc] using ht

end

open MeasureTheory
open scoped Classical MatrixGroups BigOperators
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CubicKubota EisensteinCuspModThree
local notation "Eis" => ActualEisensteinCubic.O

def cubeSourceDifference (p:Eis) (hp:p≠0) (w:HyperbolicSpace) : ℂ :=
  cubeAverage p hp cubicSourceResidualFunction w-
    (Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹*cubicSourceResidualFunction w

lemma cubeSourceDifference_continuous (p:Eis) (hp:p≠0) :
    Continuous (cubeSourceDifference p hp) :=
  (cubeAverage_continuous p hp cubicSourceResidualFunction cubicSourceResidualFunction_continuous).sub
    (continuous_const.mul cubicSourceResidualFunction_continuous)

lemma cubeSourceDifference_period_three (p:Eis) (hp:p≠0) (n:Eis) (w:HyperbolicSpace) :
    cubeSourceDifference p hp (complexTranslation (3*eisEmbedding n) • w)=cubeSourceDifference p hp w := by
  unfold cubeSourceDifference
  rw [cubeAverage_period_three p hp cubicSourceResidualFunction cubicSource_period_three,
    cubicSource_period_three]

lemma cubeSourceDifference_period_one (p:Eis) (hp:p≠0) (hprimary:lambda^2∣p-1) (w:HyperbolicSpace) :
    cubeSourceDifference p hp (complexTranslation 1 • w)=cubeSourceDifference p hp w := by
  unfold cubeSourceDifference
  rw [cubeAverage_period_one p hp hprimary cubicSourceResidualFunction cubicSource_period_three cubicSource_period_one,
    cubicSource_period_one]

lemma sourceCusp_period_nine (M:SL(2,Eis)) (z:ℂ) (v:ℝ) (hv:0<v) (n:Eis) :
    cubicSourceResidualFunction (integralComplexMatrix M • upperPoint (z+9*eisEmbedding n) v hv)=
      cubicSourceResidualFunction (integralComplexMatrix M • upperPoint z v hv) := by
  have h:=sourceCusp_scaled_periodic M v hv n (z/3)
  have h1:3*(z/3+3*eisEmbedding n)=z+9*eisEmbedding n:=by ring
  have h0:3*(z/3)=z:=by ring
  simpa only [h1,h0] using h

lemma cubeSource_summand_cusp_period {M:SL(2,Eis)} {p q:Eis}
    (d:CubeCuspData M p q) (hp:p≠0) (z:ℂ) (v:ℝ) (hv:0<v) (n:Eis) :
    cubicSourceResidualFunction (cubeAverageMatrix p hp q •
      (integralComplexMatrix M • upperPoint (z+9*eisEmbedding (p^3*n)) v hv))=
    cubicSourceResidualFunction (cubeAverageMatrix p hp q •
      (integralComplexMatrix M • upperPoint z v hv)) := by
  let T:=cubeCuspTriangular d hp
  let V:=v/‖T 1 1‖^2
  have hV:0<V:=div_pos hv (cubeCuspTriangular_norm_sq_pos d hp)
  have he (x:ℂ):cubicSourceResidualFunction (cubeAverageMatrix p hp q •
      (integralComplexMatrix M • upperPoint x v hv))=
    cubicSourceResidualFunction (integralComplexMatrix d.matrix •
      upperPoint ((T 0 0*x+T 0 1)/T 1 1) V hV):=by
    rw [←mul_smul,cubeCuspTriangular_factor d hp,mul_smul,
      complex_upper_triangular_action (cubeCuspTriangular d hp) (cubeCuspTriangular_entries d hp).2.1]
  have hx:(T 0 0*(z+9*eisEmbedding (p^3*n))+T 0 1)/T 1 1=
      (T 0 0*z+T 0 1)/T 1 1+9*eisEmbedding (p^(2*d.exponent.val)*n):=by
    calc
      _=(T 0 0*z+T 0 1)/T 1 1+9*((T 0 0/T 1 1)*eisEmbedding (p^3))*eisEmbedding n:=by
        rw [map_mul]
        ring
      _=_:=by rw [cubeCuspTriangular_integral_scale d hp,map_mul];ring
  calc
    _=cubicSourceResidualFunction (integralComplexMatrix d.matrix •
      upperPoint ((T 0 0*(z+9*eisEmbedding (p^3*n))+T 0 1)/T 1 1) V hV):=he _
    _=cubicSourceResidualFunction (integralComplexMatrix d.matrix •
      upperPoint ((T 0 0*z+T 0 1)/T 1 1+9*eisEmbedding (p^(2*d.exponent.val)*n)) V hV):=by rw [hx]
    _=cubicSourceResidualFunction (integralComplexMatrix d.matrix •
      upperPoint ((T 0 0*z+T 0 1)/T 1 1) V hV):=sourceCusp_period_nine d.matrix _ V hV _
    _=_:=(he z).symm

lemma cubeSourceDifference_cusp_period (M:SL(2,Eis)) (p:Eis) (hp:Prime p)
    (hprimary:lambda^2∣p-1) (z:ℂ) (v:ℝ) (hv:0<v) (n:Eis) :
    cubeSourceDifference p hp.ne_zero
      (integralComplexMatrix M • upperPoint (z+9*eisEmbedding (p^3*n)) v hv)=
    cubeSourceDifference p hp.ne_zero (integralComplexMatrix M • upperPoint z v hv) := by
  have hU:cubeAverage p hp.ne_zero cubicSourceResidualFunction
      (integralComplexMatrix M • upperPoint (z+9*eisEmbedding (p^3*n)) v hv)=
    cubeAverage p hp.ne_zero cubicSourceResidualFunction (integralComplexMatrix M • upperPoint z v hv):=by
    exact congrArg (fun t:ℂ=>(Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹^3*t)
      (tsum_congr (fun r:Eis⧸Ideal.span {p^3}=>cubeSource_summand_cusp_period
        (actualCubeCuspData M p (GaussianShiftedPartition.representative (p^3) r) hp hprimary) hp.ne_zero z v hv n))
  exact congrArg₂ (fun a b:ℂ=>a-(Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹*b)
    hU (sourceCusp_period_nine M z v hv (p^3*n))

lemma cubeSourceDifference_cusp_average_zero (M:SL(2,Eis)) (p:Eis) (hp:Prime p)
    (hprimary:lambda^2∣p-1) (v:ℝ) (hv:0<v) :
    (∫z in periodDomain,cubeSourceDifference p hp.ne_zero
      (integralComplexMatrix M • upperPoint (3*(eisEmbedding (p^3)*z)) v hv))=0 :=
  cubeSource_difference_average_zero M p hp hprimary v hv

lemma cubeSourceDifference_decay (p:Eis) (hp:Prime p) (hprimary:lambda^2∣p-1)
    (K:ℝ) (hK:0≤K)
    (hrep:∀j:Fin 3,∀z:ℂ,∀v:ℝ,∀hv:0<v,(‖eisEmbedding p‖^3)⁻¹≤v→
      ‖sourceCuspRemainder (cuspRepresentative j) z v hv‖≤K/v^3)
    (M:SL(2,Eis)) (z:ℂ) (v:ℝ) (hv:0<v) (hv1:1≤v) :
    ‖cubeSourceDifference p hp.ne_zero (integralComplexMatrix M • upperPoint z v hv)‖≤
      (K*(‖eisEmbedding p‖^9+(Ideal.absNorm (Ideal.span {p}):ℝ)⁻¹))/v^3 :=
  cubeSource_difference_decay_from_representatives p hp hprimary K hK hrep M z v hv hv1

end CubicEisenstein

open scoped Classical

namespace FiniteAutomorphismCover

variable {G : Type*} [Group G] {ι : Type*}

def common (K R : Subgroup G) (a : ι → G ≃* G) : Subgroup G :=
  K ⊓ ⨅i, R.comap (a i).toMonoidHom

lemma common_le (K R : Subgroup G) (a : ι → G ≃* G) : common K R a ≤ K :=
  inf_le_left

lemma common_le_preimage (K R : Subgroup G) (a : ι → G ≃* G) (i : ι) :
    common K R a ≤ R.comap (a i).toMonoidHom :=
  inf_le_right.trans (iInf_le _ i)

instance common_finiteIndex [Finite ι] (K R : Subgroup G) (a : ι → G ≃* G)
    [K.FiniteIndex] [R.FiniteIndex] : (common K R a).FiniteIndex := by
  let : (⨅i, R.comap (a i).toMonoidHom).FiniteIndex :=
    Subgroup.finiteIndex_iInf (fun i => inferInstance)
  unfold common
  infer_instance

def toSource (K R : Subgroup G) (a : ι → G ≃* G) (i : ι) : common K R a →* R where
  toFun h := ⟨a i (h : G), common_le_preimage K R a i h.property⟩
  map_one' := Subtype.ext (map_one (a i))
  map_mul' x y := Subtype.ext (map_mul (a i) (x : G) (y : G))

@[simp] lemma toSource_coe (K R : Subgroup G) (a : ι → G ≃* G) (i : ι)
    (h : common K R a) : (toSource K R a i h : G) = a i (h : G) := rfl

lemma toSource_injective (K R : Subgroup G) (a : ι → G ≃* G) (i : ι) :
    Function.Injective (toSource K R a i) := by
  intro x y hxy
  apply Subtype.ext
  exact (a i).injective (congrArg (fun r : R => (r : G)) hxy)

lemma toSource_range (K R : Subgroup G) (a : ι → G ≃* G) (i : ι) :
    (toSource K R a i).range =
      (common K R a).comap ((a i).symm.toMonoidHom.comp R.subtype) := by
  ext r
  constructor
  · rintro ⟨h,rfl⟩
    change (a i).symm (a i (h : G)) ∈ common K R a
    simpa only [MulEquiv.symm_apply_apply] using h.property
  · intro hr
    refine ⟨⟨(a i).symm (r : G),hr⟩,?_⟩
    apply Subtype.ext
    exact (a i).apply_symm_apply (r : G)

instance toSource_range_finiteIndex [Finite ι] (K R : Subgroup G) (a : ι → G ≃* G)
    [K.FiniteIndex] [R.FiniteIndex] (i : ι) : (toSource K R a i).range.FiniteIndex := by
  rw [toSource_range]
  infer_instance

def hom (K R lengthScale : Subgroup G) (a : ι → G ≃* G) (e : R ≃* lengthScale) (i : ι) :
    common K R a →* G :=
  lengthScale.subtype.comp (e.toMonoidHom.comp (toSource K R a i))

@[simp] lemma hom_apply (K R lengthScale : Subgroup G) (a : ι → G ≃* G) (e : R ≃* lengthScale)
    (i : ι) (h : common K R a) :
    hom K R lengthScale a e i h = (e (toSource K R a i h) : G) := rfl

lemma hom_injective (K R lengthScale : Subgroup G) (a : ι → G ≃* G) (e : R ≃* lengthScale) (i : ι) :
    Function.Injective (hom K R lengthScale a e i) :=
  lengthScale.subtype_injective.comp (e.injective.comp (toSource_injective K R a i))

def target (K R lengthScale : Subgroup G) (a : ι → G ≃* G) (e : R ≃* lengthScale) (i : ι) : Subgroup G :=
  (hom K R lengthScale a e i).range

lemma target_le (K R lengthScale : Subgroup G) (a : ι → G ≃* G) (e : R ≃* lengthScale) (i : ι) :
    target K R lengthScale a e i ≤ lengthScale := by
  rintro x ⟨h,rfl⟩
  exact (e (toSource K R a i h)).property

lemma target_le_common_ambient (K R lengthScale : Subgroup G) (a : ι → G ≃* G)
    (e : R ≃* lengthScale) (hLK : lengthScale ≤ K) (i : ι) : target K R lengthScale a e i ≤ K :=
  (target_le K R lengthScale a e i).trans hLK

lemma target_eq_map (K R lengthScale : Subgroup G) (a : ι → G ≃* G) (e : R ≃* lengthScale) (i : ι) :
    target K R lengthScale a e i = ((toSource K R a i).range.map e.toMonoidHom).map lengthScale.subtype := by
  rw [target,hom,MonoidHom.range_comp,MonoidHom.range_comp]

instance target_finiteIndex [Finite ι] (K R lengthScale : Subgroup G) (a : ι → G ≃* G)
    (e : R ≃* lengthScale) [K.FiniteIndex] [R.FiniteIndex] [lengthScale.FiniteIndex] (i : ι) :
    (target K R lengthScale a e i).FiniteIndex := by
  let : ((toSource K R a i).range.map e.toMonoidHom).FiniteIndex :=
    Subgroup.FiniteIndex.map_of_surjective _ e.surjective
  constructor
  rw [target_eq_map,Subgroup.index_map_subtype]
  exact mul_ne_zero Subgroup.FiniteIndex.index_ne_zero Subgroup.FiniteIndex.index_ne_zero

def equiv (K R lengthScale : Subgroup G) (a : ι → G ≃* G) (e : R ≃* lengthScale) (i : ι) :
    common K R a ≃* target K R lengthScale a e i :=
  MonoidHom.ofInjective (hom_injective K R lengthScale a e i)

@[simp] lemma equiv_coe (K R lengthScale : Subgroup G) (a : ι → G ≃* G) (e : R ≃* lengthScale)
    (i : ι) (h : common K R a) :
    (equiv K R lengthScale a e i h : G) = (e (toSource K R a i h) : G) := rfl

end FiniteAutomorphismCover

namespace CubicKubota
open scoped BigOperators Classical MatrixGroups

open CubicEisenstein ConcreteTraceCRT
local notation "O" => ActualEisensteinCubic.O

lemma literalCube_zero_pair (p : ActualEisensteinCubic.O) (hp : p≠0) (x : cubeKernelCorrespondence p) :
    cubeAverageMatrix p hp 0*integralComplexMatrix (cubeKernelRightGlobal p hp x)=
      integralComplexMatrix (cubeKernelLeftGlobal p x)*cubeAverageMatrix p hp 0 := by
  let M := cubeKernelLeftGlobal p x
  let N := cubeKernelRightGlobal p hp x
  let z := cubeDilationRoot p
  have hz : z^2=eisEmbedding p^3 := cubeDilationRoot_sq p
  have hz0 : z≠0 := cubeDilationRoot_ne_zero p hp
  have he := cubeCorrespondence_entries p x.1
  change p^3*M 0 0=N 0 0*p^3 ∧ p^3*M 0 1=N 0 1 ∧
    M 1 0=N 1 0*p^3 ∧ M 1 1=N 1 1 at he
  have h00 : eisEmbedding (M 0 0)=eisEmbedding (N 0 0) :=
    congrArg eisEmbedding (mul_left_cancel₀ (pow_ne_zero 3 hp) (he.1.trans (mul_comm _ _)))
  have h01 := congrArg eisEmbedding he.2.1
  have h10 := congrArg eisEmbedding he.2.2.1
  have h11 := congrArg eisEmbedding he.2.2.2
  simp only [map_mul,map_pow] at h01 h10
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.SpecialLinearGroup.coe_mul,Matrix.mul_apply,Fin.sum_univ_two,
      cubeAverageMatrix_entries,integralComplexMatrix_apply]
  · change z⁻¹*eisEmbedding (N 0 0)+(z⁻¹*(3*eisEmbedding 0))*eisEmbedding (N 1 0)=
      eisEmbedding (M 0 0)*z⁻¹+eisEmbedding (M 0 1)*0
    rw [h00,map_zero]
    ring
  · change z⁻¹*eisEmbedding (N 0 1)+(z⁻¹*(3*eisEmbedding 0))*eisEmbedding (N 1 1)=
      eisEmbedding (M 0 0)*(z⁻¹*(3*eisEmbedding 0))+eisEmbedding (M 0 1)*z
    rw [←h01,←hz,map_zero]
    field_simp [hz0]
    ; ring
  · change 0*eisEmbedding (N 0 0)+z*eisEmbedding (N 1 0)=
      eisEmbedding (M 1 0)*z⁻¹+eisEmbedding (M 1 1)*0
    rw [h10,←hz]
    field_simp [hz0]
    ; ring
  · change 0*eisEmbedding (N 0 1)+z*eisEmbedding (N 1 1)=
      eisEmbedding (M 1 0)*(z⁻¹*(3*eisEmbedding 0))+eisEmbedding (M 1 1)*z
    rw [h11,map_zero]
    ring

theorem literalCube_zero_intertwines (p : ActualEisensteinCubic.O) (hp : p≠0) :
    IntegralCoverIntertwines (cubeKernelRangeEquiv p hp).symm (cubeAverageMatrix p hp 0) := by
  intro r
  let x := (MonoidHom.ofInjective (cubeKernelRightGlobal_injective p hp)).symm r
  have hr : cubeKernelRightGlobal p hp x=(r:SL(2,ActualEisensteinCubic.O)) :=
    MonoidHom.apply_ofInjective_symm (cubeKernelRightGlobal_injective p hp) r
  change cubeAverageMatrix p hp 0*integralComplexMatrix (r:SL(2,ActualEisensteinCubic.O))=
    integralComplexMatrix (cubeKernelLeftGlobal p x)*cubeAverageMatrix p hp 0
  rw [←hr]
  exact literalCube_zero_pair p hp x

lemma cubeTranslation_complex (q : ActualEisensteinCubic.O) :
    integralComplexMatrix (upperTranslation q:SL(2,ActualEisensteinCubic.O))=complexTranslation (3*eisEmbedding q) := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  rw [integralComplexMatrix_apply]
  fin_cases i <;> fin_cases j <;> simp [upperTranslation, complexTranslation, map_ofNat]

lemma cubeAverageMatrix_factor_zero (p : ActualEisensteinCubic.O) (hp : p≠0) (q : ActualEisensteinCubic.O) :
    cubeAverageMatrix p hp q=cubeAverageMatrix p hp 0*
      integralComplexMatrix (upperTranslation q:SL(2,ActualEisensteinCubic.O)) := by
  rw [cubeTranslation_complex]
  have h0 : complexTranslation 0=1 := by
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j <;> simp [complexTranslation]
  simp only [cubeAverageMatrix,map_zero,mul_zero,h0,mul_one]

theorem literalCube_summand_intertwines (p : ActualEisensteinCubic.O) (hp : p≠0) (q : ActualEisensteinCubic.O)
    (A : SL(2,ActualEisensteinCubic.O)) (r : (cubeKernelRightGlobal p hp).range)
    (hA : (upperTranslation q:SL(2,ActualEisensteinCubic.O))*A=(r:SL(2,ActualEisensteinCubic.O))*(upperTranslation q:SL(2,ActualEisensteinCubic.O))) :
    cubeAverageMatrix p hp q*integralComplexMatrix A=
      integralComplexMatrix ((cubeKernelRangeEquiv p hp).symm r:SL(2,ActualEisensteinCubic.O))*cubeAverageMatrix p hp q := by
  have hAc := congrArg integralComplexMatrix hA
  simp only [map_mul] at hAc
  rw [cubeAverageMatrix_factor_zero,mul_assoc,hAc,←mul_assoc,
    literalCube_zero_intertwines p hp r,mul_assoc]

end CubicKubota

namespace CubicEisenstein
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups InnerProductSpace
open Finset AddChar MulChar EisensteinEmbedding

local notation "O" => ActualEisensteinCubic.O

lemma integralCoverIntertwines_trans {H J K : Subgroup (SL(2,ActualEisensteinCubic.O))}
    (e : H≃*J) (f : J≃*K) (g h : SL(2,ℂ))
    (he : IntegralCoverIntertwines e g) (hf : IntegralCoverIntertwines f h) :
    IntegralCoverIntertwines (e.trans f) (h*g) := by
  intro x
  change (h*g)*integralComplexMatrix (x:SL(2,ActualEisensteinCubic.O))=
    integralComplexMatrix (f (e x):SL(2,ActualEisensteinCubic.O))*(h*g)
  rw [mul_assoc,he x,←mul_assoc,hf (e x),mul_assoc]

lemma integralConjugateMap_trans {H J K : Subgroup (SL(2,ActualEisensteinCubic.O))}
    (e : H≃*J) (f : J≃*K) (g h : SL(2,ℂ))
    (he : IntegralCoverIntertwines e g) (hf : IntegralCoverIntertwines f h)
    (q : IntegralOrbitQuotient H) :
    integralConjugateMap f h hf (integralConjugateMap e g he q)=
      integralConjugateMap (e.trans f) (h*g) (integralCoverIntertwines_trans e f g h he hf) q := by
  induction q using Quotient.inductionOn with
  | _ w =>
    change integralOrbitProjection K (h•(g•w))=integralOrbitProjection K ((h*g)•w)
    rw [mul_smul]

lemma integralConjugatePullback_trans {H J K : Subgroup (SL(2,ActualEisensteinCubic.O))}
    (e : H≃*J) (f : J≃*K) (g h : SL(2,ℂ))
    (he : IntegralCoverIntertwines e g) (hf : IntegralCoverIntertwines f h)
    (hH : H≤CubicKubota.levelThree) (hJ : J≤CubicKubota.levelThree)
    (hK : K≤CubicKubota.levelThree) (F : IntegralQuotientL2 K) :
    integralConjugatePullback e g he hH hJ (integralConjugatePullback f h hf hJ hK F)=
      integralConjugatePullback (e.trans f) (h*g) (integralCoverIntertwines_trans e f g h he hf) hH hK F := by
  apply Lp.ext
  have hinner := (integralConjugateMap_measurePreserving e g he hH hJ).quasiMeasurePreserving.ae_eq_comp
    (integralConjugatePullback_ae f h hf hJ hK F)
  filter_upwards [integralConjugatePullback_ae e g he hH hJ (integralConjugatePullback f h hf hJ hK F),
    hinner,integralConjugatePullback_ae (e.trans f) (h*g)
      (integralCoverIntertwines_trans e f g h he hf) hH hK F] with q ho hi ht
  dsimp only [Function.comp_def] at hi
  rw [ho,hi,ht,integralConjugateMap_trans]

def kernelCoverLeg {H J : Subgroup (SL(2,ActualEisensteinCubic.O))}
    (hHK : H≤globalKubotaKernel) (hJK : J≤globalKubotaKernel)
    [J.IsFiniteRelIndex globalKubotaKernel]
    (e : H≃*J) (g : SL(2,ℂ)) (he : IntegralCoverIntertwines e g) :
    KernelQuotientL2→L[ℂ]IntegralQuotientL2 H :=
  (integralConjugatePullback e g he (hHK.trans globalKubotaKernel_le_levelThree)
    (hJK.trans globalKubotaKernel_le_levelThree)).toContinuousLinearMap.comp
      (integralCoverPullback hJK globalKubotaKernel_le_levelThree)

lemma kernelCoverLeg_representative {H J : Subgroup (SL(2,ActualEisensteinCubic.O))}
    (hHK : H≤globalKubotaKernel) (hJK : J≤globalKubotaKernel)
    [J.IsFiniteRelIndex globalKubotaKernel]
    (e : H≃*J) (g : SL(2,ℂ)) (he : IntegralCoverIntertwines e g)
    (F : KernelQuotientL2) (f : KernelQuotient→ℂ)
    (hrep : F=ᵐ[integralQuotientVolume globalKubotaKernel]f) :
    kernelCoverLeg hHK hJK e g he F=ᵐ[integralQuotientVolume H]
      fun q=>f (integralCoverMap hJK (integralConjugateMap e g he q)) := by
  have hc := (integralCoverPullback_ae hJK globalKubotaKernel_le_levelThree F).trans
    ((integralCoverMap_quasiMeasurePreserving hJK globalKubotaKernel_le_levelThree).ae_eq_comp hrep)
  exact (integralConjugatePullback_ae e g he
    (hHK.trans globalKubotaKernel_le_levelThree) (hJK.trans globalKubotaKernel_le_levelThree) _).trans
    ((integralConjugateMap_measurePreserving e g he
      (hHK.trans globalKubotaKernel_le_levelThree)
      (hJK.trans globalKubotaKernel_le_levelThree)).quasiMeasurePreserving.ae_eq_comp hc)

lemma kernelCoverLeg_adjoint_apply {H J : Subgroup (SL(2,ActualEisensteinCubic.O))}
    (hHK : H≤globalKubotaKernel) (hJK : J≤globalKubotaKernel)
    [J.IsFiniteRelIndex globalKubotaKernel]
    (e : H≃*J) (g : SL(2,ℂ)) (he : IntegralCoverIntertwines e g)
    (F : IntegralQuotientL2 H) :
    ContinuousLinearMap.adjoint (kernelCoverLeg hHK hJK e g he) F=
      integralCoverTrace hJK globalKubotaKernel_le_levelThree
        (integralConjugatePullback e.symm g⁻¹ (integralCoverIntertwines_inverse e g he)
          (hJK.trans globalKubotaKernel_le_levelThree) (hHK.trans globalKubotaKernel_le_levelThree) F) := by
  apply ext_inner_right ℂ
  intro G
  rw [ContinuousLinearMap.adjoint_inner_left]
  change inner ℂ F (integralConjugatePullback e g he
    (hHK.trans globalKubotaKernel_le_levelThree) (hJK.trans globalKubotaKernel_le_levelThree)
    (integralCoverPullback hJK globalKubotaKernel_le_levelThree G))=_
  rw [integralConjugatePullback_pairing]
  exact (ContinuousLinearMap.adjoint_inner_left (integralCoverPullback hJK globalKubotaKernel_le_levelThree) G _).symm

theorem kernelCoverLeg_adjoint_comp {H Ji Jj : Subgroup (SL(2,ActualEisensteinCubic.O))}
    (hHK : H≤globalKubotaKernel) (hiK : Ji≤globalKubotaKernel) (hjK : Jj≤globalKubotaKernel)
    [Ji.IsFiniteRelIndex globalKubotaKernel] [Jj.IsFiniteRelIndex globalKubotaKernel]
    (ei : H≃*Ji) (ej : H≃*Jj) (gi gj : SL(2,ℂ))
    (hei : IntegralCoverIntertwines ei gi) (hej : IntegralCoverIntertwines ej gj) :
    (ContinuousLinearMap.adjoint (kernelCoverLeg hHK hjK ej gj hej)).comp
      (kernelCoverLeg hHK hiK ei gi hei)=
        kernelCorrespondenceL2 hjK hiK (ej.symm.trans ei) (gi*gj⁻¹)
          (integralCoverIntertwines_trans ej.symm ei gj⁻¹ gi
            (integralCoverIntertwines_inverse ej gj hej) hei) := by
  apply ContinuousLinearMap.ext
  intro F
  change ContinuousLinearMap.adjoint (kernelCoverLeg hHK hjK ej gj hej)
    (kernelCoverLeg hHK hiK ei gi hei F)=_
  rw [kernelCoverLeg_adjoint_apply]
  change integralCoverTrace hjK globalKubotaKernel_le_levelThree
    (integralConjugatePullback ej.symm gj⁻¹ (integralCoverIntertwines_inverse ej gj hej)
      (hjK.trans globalKubotaKernel_le_levelThree) (hHK.trans globalKubotaKernel_le_levelThree)
      (integralConjugatePullback ei gi hei
        (hHK.trans globalKubotaKernel_le_levelThree) (hiK.trans globalKubotaKernel_le_levelThree)
        (integralCoverPullback hiK globalKubotaKernel_le_levelThree F)))=_
  rw [integralConjugatePullback_trans]
  rfl

end CubicEisenstein

open scoped Classical MatrixGroups BigOperators

namespace CubicKubota
open CubicEisenstein ConcreteTraceCRT
local notation "O" => ActualEisensteinCubic.O

abbrev CubeResidues (p : ActualEisensteinCubic.O) := ActualEisensteinCubic.O ⧸ Ideal.span {p^3}

def cubeCommonAutomorphism (p : ActualEisensteinCubic.O) (r : CubeResidues p) : SL(2,ActualEisensteinCubic.O) ≃* SL(2,ActualEisensteinCubic.O) :=
  MulAut.conj (upperTranslation (GaussianShiftedPartition.representative (p^3) r):SL(2,ActualEisensteinCubic.O))

def cubeCommonCover (p : ActualEisensteinCubic.O) (hp : p≠0) : Subgroup (SL(2,ActualEisensteinCubic.O)) :=
  FiniteAutomorphismCover.common globalKubotaKernel
    (cubeKernelRightGlobal p hp).range (cubeCommonAutomorphism p)

lemma cubeCommonCover_le (p : ActualEisensteinCubic.O) (hp : p≠0) : cubeCommonCover p hp≤globalKubotaKernel :=
  FiniteAutomorphismCover.common_le _ _ _

lemma cubeCommonCover_finiteIndex (p : ActualEisensteinCubic.O) (hp : p≠0) : (cubeCommonCover p hp).FiniteIndex := by
  let : globalKubotaKernel.FiniteIndex := globalKubotaKernel_finiteIndex
  let : Finite (CubeResidues p) := finite_quotient_span (pow_ne_zero 3 hp)
  let := (cubeKernelGlobal_finite_covers p hp).2
  exact FiniteAutomorphismCover.common_finiteIndex _ _ _

def cubeCommonTarget (p : ActualEisensteinCubic.O) (hp : p≠0) (r : CubeResidues p) : Subgroup (SL(2,ActualEisensteinCubic.O)) :=
  FiniteAutomorphismCover.target globalKubotaKernel
    (cubeKernelRightGlobal p hp).range (cubeKernelLeftGlobal p).range
    (cubeCommonAutomorphism p) (cubeKernelRangeEquiv p hp).symm r

lemma cubeCommonTarget_le (p : ActualEisensteinCubic.O) (hp : p≠0) (r : CubeResidues p) :
    cubeCommonTarget p hp r≤globalKubotaKernel :=
  FiniteAutomorphismCover.target_le_common_ambient _ _ _ _ _ (cubeKernelLeftGlobal_le p) r

lemma cubeCommonTarget_finiteIndex (p : ActualEisensteinCubic.O) (hp : p≠0) (r : CubeResidues p) :
    (cubeCommonTarget p hp r).FiniteIndex := by
  let : globalKubotaKernel.FiniteIndex := globalKubotaKernel_finiteIndex
  let : Finite (CubeResidues p) := finite_quotient_span (pow_ne_zero 3 hp)
  let := (cubeKernelGlobal_finite_covers p hp).1
  let := (cubeKernelGlobal_finite_covers p hp).2
  exact FiniteAutomorphismCover.target_finiteIndex _ _ _ _ _ r

def cubeCommonEquiv (p : ActualEisensteinCubic.O) (hp : p≠0) (r : CubeResidues p) :
    cubeCommonCover p hp≃*cubeCommonTarget p hp r :=
  FiniteAutomorphismCover.equiv globalKubotaKernel
    (cubeKernelRightGlobal p hp).range (cubeKernelLeftGlobal p).range
    (cubeCommonAutomorphism p) (cubeKernelRangeEquiv p hp).symm r

lemma cubeCommon_intertwines (p : ActualEisensteinCubic.O) (hp : p≠0) (r : CubeResidues p) :
    IntegralCoverIntertwines (cubeCommonEquiv p hp r)
      (cubeAverageMatrix p hp (GaussianShiftedPartition.representative (p^3) r)) := by
  intro h
  let q := GaussianShiftedPartition.representative (p^3) r
  let rh := FiniteAutomorphismCover.toSource globalKubotaKernel
    (cubeKernelRightGlobal p hp).range (cubeCommonAutomorphism p) r h
  have hA : (upperTranslation q:SL(2,ActualEisensteinCubic.O))*(h:SL(2,ActualEisensteinCubic.O))=
      (rh:SL(2,ActualEisensteinCubic.O))*(upperTranslation q:SL(2,ActualEisensteinCubic.O)) := by
    change (upperTranslation q:SL(2,ActualEisensteinCubic.O))*(h:SL(2,ActualEisensteinCubic.O))=
      ((upperTranslation q:SL(2,ActualEisensteinCubic.O))*(h:SL(2,ActualEisensteinCubic.O))*(upperTranslation q:SL(2,ActualEisensteinCubic.O))⁻¹)*
        (upperTranslation q:SL(2,ActualEisensteinCubic.O))
    simp only [mul_assoc,inv_mul_cancel,mul_one]
  exact literalCube_summand_intertwines p hp q (h:SL(2,ActualEisensteinCubic.O)) rh hA

def cubeCommonLeg (p : ActualEisensteinCubic.O) (hp : p≠0) (r : CubeResidues p) :
    KernelQuotientL2→L[ℂ]IntegralQuotientL2 (cubeCommonCover p hp) := by
  letI := cubeCommonTarget_finiteIndex p hp r
  letI : (cubeCommonTarget p hp r).IsFiniteRelIndex globalKubotaKernel :=
    Subgroup.isFiniteRelIndex_of_finiteIndex
  exact kernelCoverLeg (cubeCommonCover_le p hp) (cubeCommonTarget_le p hp r)
    (cubeCommonEquiv p hp r)
    (cubeAverageMatrix p hp (GaussianShiftedPartition.representative (p^3) r))
    (cubeCommon_intertwines p hp r)

end CubicKubota

end

end OAI
