import OAI.NumberTheory.DirichletL.Eisenstein.CubeEigenrelation

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
open Filter MeasureTheory
open scoped Classical MatrixGroups BigOperators

namespace CubicEisenstein
open CubicKubota
local notation "O" => ActualEisensteinCubic.O

lemma cubicSourceResidualFunction_kernel_invariant (M : globalKubotaKernel)
    (w : HyperbolicSpace) :
    cubicSourceResidualFunction (integralComplexMatrix (M:SL(2,ActualEisensteinCubic.O)) • w)=
      cubicSourceResidualFunction w := by
  obtain ⟨hM,hchar⟩ := (globalKubotaKernel_mem (M:SL(2,ActualEisensteinCubic.O))).mp M.property
  have h := cubicSourceResidualFunction_automorphy
    ⟨(M:SL(2,ActualEisensteinCubic.O)),levelThree_le_levelTwo hM⟩ w
  rw [levelTwoComplexCharacter_restrict ⟨(M:SL(2,ActualEisensteinCubic.O)),hM⟩,hchar,one_mul] at h
  exact h

def cubicSourceQuotientFunction : KernelQuotient→ℂ :=
  Quotient.lift cubicSourceResidualFunction (by
    rintro w u ⟨h,rfl⟩
    exact (cubicSourceResidualFunction_kernel_invariant h w).symm)

lemma cubicSourceQuotientFunction_projection (w : HyperbolicSpace) :
    cubicSourceQuotientFunction (integralOrbitProjection globalKubotaKernel w)=
      cubicSourceResidualFunction w := rfl

lemma cubicSourceQuotientFunction_measurable : Measurable cubicSourceQuotientFunction := by
  apply measurable_from_quotient.mpr
  exact cubicSourceResidualFunction_continuous.measurable

lemma cubicSourceQuotientFunction_represents :
    kernelSourceProjection cubicEisensteinResidue=ᵐ[integralQuotientVolume globalKubotaKernel]
      cubicSourceQuotientFunction := by
  unfold integralQuotientVolume
  apply (ae_map_iff (measurable_integralOrbitProjection _).aemeasurable
    (measurableSet_eq_fun (Lp.stronglyMeasurable _).measurable
      cubicSourceQuotientFunction_measurable)).mpr
  exact ae_restrict_of_ae cubicSourceResidualFunction_represents_projection

end CubicEisenstein

namespace CubicKubota
open CubicEisenstein ConcreteTraceCRT
local notation "O" => ActualEisensteinCubic.O

abbrev CubeLegIndex (p : ActualEisensteinCubic.O) := Option (CubeResidues p)

def cubeLegTarget (p : ActualEisensteinCubic.O) (hp : p≠0) : CubeLegIndex p→Subgroup (SL(2,ActualEisensteinCubic.O))
  | none => cubeCommonCover p hp
  | some r => cubeCommonTarget p hp r

lemma cubeLegTarget_le (p : ActualEisensteinCubic.O) (hp : p≠0) (i : CubeLegIndex p) :
    cubeLegTarget p hp i≤globalKubotaKernel := by
  cases i with
  | none => exact cubeCommonCover_le p hp
  | some r => exact cubeCommonTarget_le p hp r

lemma cubeLegTarget_finiteIndex (p : ActualEisensteinCubic.O) (hp : p≠0) (i : CubeLegIndex p) :
    (cubeLegTarget p hp i).FiniteIndex := by
  cases i with
  | none => exact cubeCommonCover_finiteIndex p hp
  | some r => exact cubeCommonTarget_finiteIndex p hp r

def cubeLegEquiv (p : ActualEisensteinCubic.O) (hp : p≠0) : (i : CubeLegIndex p)→
    cubeCommonCover p hp≃*cubeLegTarget p hp i
  | none => MulEquiv.refl _
  | some r => cubeCommonEquiv p hp r

def cubeLegMatrix (p : ActualEisensteinCubic.O) (hp : p≠0) : CubeLegIndex p→SL(2,ℂ)
  | none => 1
  | some r => cubeAverageMatrix p hp (GaussianShiftedPartition.representative (p^3) r)

lemma cubeLeg_intertwines (p : ActualEisensteinCubic.O) (hp : p≠0) (i : CubeLegIndex p) :
    IntegralCoverIntertwines (cubeLegEquiv p hp i) (cubeLegMatrix p hp i) := by
  cases i with
  | none =>
    intro h
    change 1*integralComplexMatrix (h:SL(2,ActualEisensteinCubic.O))=integralComplexMatrix (h:SL(2,ActualEisensteinCubic.O))*1
    simp only [one_mul,mul_one]
  | some r => exact cubeCommon_intertwines p hp r

def cubeLeg (p : ActualEisensteinCubic.O) (hp : p≠0) (i : CubeLegIndex p) :
    KernelQuotientL2→L[ℂ]IntegralQuotientL2 (cubeCommonCover p hp) := by
  letI := cubeLegTarget_finiteIndex p hp i
  letI : (cubeLegTarget p hp i).IsFiniteRelIndex globalKubotaKernel :=
    Subgroup.isFiniteRelIndex_of_finiteIndex
  exact kernelCoverLeg (cubeCommonCover_le p hp) (cubeLegTarget_le p hp i)
    (cubeLegEquiv p hp i) (cubeLegMatrix p hp i) (cubeLeg_intertwines p hp i)

def cubeLegCoefficient (p : ActualEisensteinCubic.O) : CubeLegIndex p→ℂ
  | none => -(Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹
  | some _ => (Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹^3

def cubeLegQuotientFunction (p : ActualEisensteinCubic.O) (hp : p≠0) (i : CubeLegIndex p) :
    IntegralOrbitQuotient (cubeCommonCover p hp)→ℂ :=
  fun q=>cubicSourceQuotientFunction
    (integralCoverMap (cubeLegTarget_le p hp i)
      (integralConjugateMap (cubeLegEquiv p hp i) (cubeLegMatrix p hp i)
        (cubeLeg_intertwines p hp i) q))

lemma cubeLegQuotientFunction_projection (p : ActualEisensteinCubic.O) (hp : p≠0) (i : CubeLegIndex p)
    (w : HyperbolicSpace) :
    cubeLegQuotientFunction p hp i (integralOrbitProjection (cubeCommonCover p hp) w)=
      cubicSourceResidualFunction (cubeLegMatrix p hp i • w) := rfl

lemma cubeLegQuotientFunction_measurable (p : ActualEisensteinCubic.O) (hp : p≠0) (i : CubeLegIndex p) :
    Measurable (cubeLegQuotientFunction p hp i) :=
  cubicSourceQuotientFunction_measurable.comp
    ((integralCoverMap_measurable (cubeLegTarget_le p hp i)).comp
      (integralConjugateMap_measurable _ _ _))

lemma cubeLeg_representative (p : ActualEisensteinCubic.O) (hp : p≠0) (i : CubeLegIndex p) :
    cubeLeg p hp i (kernelSourceProjection cubicEisensteinResidue)
      =ᵐ[integralQuotientVolume (cubeCommonCover p hp)]cubeLegQuotientFunction p hp i := by
  let := cubeLegTarget_finiteIndex p hp i
  let : (cubeLegTarget p hp i).IsFiniteRelIndex globalKubotaKernel :=
    Subgroup.isFiniteRelIndex_of_finiteIndex
  exact kernelCoverLeg_representative (cubeCommonCover_le p hp) (cubeLegTarget_le p hp i)
    (cubeLegEquiv p hp i) (cubeLegMatrix p hp i) (cubeLeg_intertwines p hp i)
    _ _ cubicSourceQuotientFunction_represents

def cubeDifferenceL2 (p : ActualEisensteinCubic.O) (hp : p≠0) : IntegralQuotientL2 (cubeCommonCover p hp) :=
  ∑' i:CubeLegIndex p,cubeLegCoefficient p i •
    cubeLeg p hp i (kernelSourceProjection cubicEisensteinResidue)

def cubeDifferenceQuotientFunction (p : ActualEisensteinCubic.O) (hp : p≠0) :
    IntegralOrbitQuotient (cubeCommonCover p hp)→ℂ :=
  fun q=>∑' i:CubeLegIndex p,cubeLegCoefficient p i*cubeLegQuotientFunction p hp i q

lemma cubeDifferenceQuotientFunction_projection (p : ActualEisensteinCubic.O) (hp : p≠0)
    (w : HyperbolicSpace) :
    cubeDifferenceQuotientFunction p hp (integralOrbitProjection (cubeCommonCover p hp) w)=
      cubeSourceDifference p hp w := by
  let : Finite (CubeResidues p) := finite_quotient_span (pow_ne_zero 3 hp)
  let : Fintype (CubeResidues p) := Fintype.ofFinite _
  simp only [cubeDifferenceQuotientFunction,tsum_fintype,Fintype.sum_option,
    cubeLegCoefficient,cubeLegQuotientFunction_projection,cubeLegMatrix,one_smul,
    cubeSourceDifference,cubeAverage,Finset.mul_sum]
  ring

lemma cubeDifferenceQuotientFunction_measurable (p : ActualEisensteinCubic.O) (hp : p≠0) :
    Measurable (cubeDifferenceQuotientFunction p hp) := by
  let : Finite (CubeResidues p) := finite_quotient_span (pow_ne_zero 3 hp)
  let : Fintype (CubeResidues p) := Fintype.ofFinite _
  unfold cubeDifferenceQuotientFunction
  simp only [tsum_fintype]
  exact Finset.measurable_sum _ (fun i _=>measurable_const.mul (cubeLegQuotientFunction_measurable p hp i))

lemma cubeDifferenceL2_representative (p : ActualEisensteinCubic.O) (hp : p≠0) :
    cubeDifferenceL2 p hp=ᵐ[integralQuotientVolume (cubeCommonCover p hp)]
      cubeDifferenceQuotientFunction p hp := by
  let : Finite (CubeResidues p) := finite_quotient_span (pow_ne_zero 3 hp)
  let : Fintype (CubeResidues p) := Fintype.ofFinite _
  unfold cubeDifferenceL2 cubeDifferenceQuotientFunction
  simp only [tsum_fintype]
  apply (Lp.coeFn_finsetSum _ _).trans
  have hh (i : CubeLegIndex p) :
      ((cubeLegCoefficient p i • cubeLeg p hp i (kernelSourceProjection cubicEisensteinResidue) :
        IntegralQuotientL2 (cubeCommonCover p hp)) : IntegralOrbitQuotient (cubeCommonCover p hp)→ℂ)
      =ᵐ[integralQuotientVolume (cubeCommonCover p hp)]
      (fun q=>cubeLegCoefficient p i*cubeLegQuotientFunction p hp i q) :=
    by
      filter_upwards [Lp.coeFn_smul (cubeLegCoefficient p i)
        (cubeLeg p hp i (kernelSourceProjection cubicEisensteinResidue)),
        cubeLeg_representative p hp i] with q hq hr
      simpa only [Pi.smul_apply,smul_eq_mul,hr] using hq
  filter_upwards [eventuallyEq_sum (fun i (_ : i∈Finset.univ)=>hh i)] with q hq
  simpa only [Finset.sum_apply] using hq

end CubicKubota
end

namespace CubicEisenstein

open MeasureTheory
open scoped Classical MatrixGroups BigOperators

section
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CubicKubota EisensteinCuspModThree
local notation "Eis" => ActualEisensteinCubic.O

lemma sourceCuspLeadingCoefficient_ramified (j:Fin 3) (hj:j≠0) :
    sourceCuspLeadingCoefficient (cuspRepresentative j)=0 := by
  unfold sourceCuspLeadingCoefficient sourceCuspConstant
  rw [sourceCuspRepresentative_average]
  simp only [ite_eq_right hj,zero_mul,zero_div]

theorem sourceCuspRemainder_representatives_decay (a:ℝ) (ha:0<a) :
    ∃K:ℝ,0≤K∧∀j:Fin 3,∀z:ℂ,∀v:ℝ,∀hv:0<v,a≤v→
      ‖sourceCuspRemainder (cuspRepresentative j) z v hv‖≤K/v^3 := by
  obtain ⟨K0,hK0,h0⟩:=sourceCuspRemainder_principal_cubic_decay a ha
  obtain ⟨K1,hK1,h1⟩:=ramifiedSource_cubic_decay false a ha
  obtain ⟨K2,hK2,h2⟩:=ramifiedSource_cubic_decay true a ha
  refine ⟨K0+K1+K2,by positivity,?_⟩
  intro j z v hv hav
  have hD:0≤v^3:=pow_nonneg hv.le 3
  fin_cases j
  · have hb:‖sourceCuspRemainder (cuspRepresentative 0) z v hv‖≤K0/v^3:=by
      simpa [cuspRepresentative,cuspParameter,lowerCuspMatrix_zero] using h0 z v hv hav
    exact hb.trans (div_le_div_of_nonneg_right (by linarith) hD)
  · have he:sourceCuspRemainder (cuspRepresentative 1) z v hv=
        ramifiedSourceFunction (ramifiedCuspRoot false:Eis) (upperPoint z v hv):=by
      rw [sourceCuspRemainder,sourceCuspLeadingCoefficient_ramified 1 (by decide),zero_mul,sub_zero]
      simp [cuspRepresentative,cuspParameter,ramifiedSourceFunction,ramifiedCuspRoot,ramifiedOmegaUnit_val]
    change ‖sourceCuspRemainder (cuspRepresentative 1) z v hv‖≤_
    rw [he]
    exact (h1 v hv z hav).trans (div_le_div_of_nonneg_right (by linarith) hD)
  · have he:sourceCuspRemainder (cuspRepresentative 2) z v hv=
        ramifiedSourceFunction (ramifiedCuspRoot true:Eis) (upperPoint z v hv):=by
      rw [sourceCuspRemainder,sourceCuspLeadingCoefficient_ramified 2 (by decide),zero_mul,sub_zero]
      simp [cuspRepresentative,cuspParameter,ramifiedSourceFunction,ramifiedCuspRoot,
        Units.val_pow_eq_pow_val,ramifiedOmegaUnit_val]
    change ‖sourceCuspRemainder (cuspRepresentative 2) z v hv‖≤_
    rw [he]
    exact (h2 v hv z hav).trans (div_le_div_of_nonneg_right (by linarith) hD)

theorem cubeSourceDifference_cubic_decay (p:Eis) (hp:Prime p) (hprimary:lambda^2∣p-1) :
    ∃C:ℝ,0≤C∧∀M:SL(2,Eis),∀z:ℂ,∀v:ℝ,∀hv:0<v,1≤v→
      ‖cubeSourceDifference p hp.ne_zero (integralComplexMatrix M • upperPoint z v hv)‖≤C/v^3 := by
  have hr:0<‖eisEmbedding p‖:=norm_pos_iff.mpr (eisEmbedding_ne_zero hp.ne_zero)
  obtain ⟨K,hK,hrep⟩:=sourceCuspRemainder_representatives_decay (‖eisEmbedding p‖^3)⁻¹ (by positivity)
  refine ⟨K*(‖eisEmbedding p‖^9+(Ideal.absNorm (Ideal.span {p}):ℝ)⁻¹),by positivity,?_⟩
  intro M z v hv hv1
  exact cubeSourceDifference_decay p hp hprimary K hK hrep M z v hv hv1

end

section
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CubicKubota EisensteinCuspModThree
local notation "Eis" => ActualEisensteinCubic.O

lemma cubeCuspTriangular_norm_sq_le {M:SL(2,Eis)} {p q:Eis}
    (d:CubeCuspData M p q) (hp:p≠0) :
    ‖cubeCuspTriangular d hp 1 1‖^2≤‖eisEmbedding p‖^3 := by
  rw [cubeCuspTriangular_norm_sq d hp,←Real.rpow_natCast ‖eisEmbedding p‖ 3]
  apply Real.rpow_le_rpow_of_exponent_le (cubePrime_norm_ge_one p hp)
  norm_num only [Nat.cast_ofNat]
  have hj:0≤(d.exponent.val:ℝ):=Nat.cast_nonneg _
  linarith

lemma cubeReducedRemainder_bound_from_height {M:SL(2,Eis)} {p q:Eis}
    (d:CubeCuspData M p q) (hp:p≠0) (a K:ℝ) (ha:0<a) (hK:0≤K)
    (hrep:∀j:Fin 3,∀z:ℂ,∀v:ℝ,∀hv:0<v,a/‖eisEmbedding p‖^3≤v→
      ‖sourceCuspRemainder (cuspRepresentative j) z v hv‖≤K/v^3)
    (z:ℂ) (v:ℝ) (hv:0<v) (hav:a≤v) :
    ‖cubeReducedRemainder d hp z v hv‖≤K*‖eisEmbedding p‖^9/v^3 := by
  let D:=‖cubeCuspTriangular d hp 1 1‖^2
  have hD:0<D:=cubeCuspTriangular_norm_sq_pos d hp
  have hr:0<‖eisEmbedding p‖:=norm_pos_iff.mpr (eisEmbedding_ne_zero hp)
  have hd:D≤‖eisEmbedding p‖^3:=cubeCuspTriangular_norm_sq_le d hp
  have hlow:a/‖eisEmbedding p‖^3≤v/D:=by
    apply (le_div_iff₀ hD).mpr
    calc
      _≤(a/‖eisEmbedding p‖^3)*‖eisEmbedding p‖^3:=
        mul_le_mul_of_nonneg_left hd (by positivity)
      _=a:=div_mul_cancel₀ a (pow_ne_zero 3 hr.ne')
      _≤v:=hav
  have hb:=sourceCuspRemainder_bound_all K (a/‖eisEmbedding p‖^3) hrep
    d.matrix ((cubeCuspTriangular d hp 0 0*z+cubeCuspTriangular d hp 0 1)/cubeCuspTriangular d hp 1 1)
    (v/D) (div_pos hv hD) hlow
  change ‖cubeReducedRemainder d hp z v hv‖≤K/(v/D)^3 at hb
  refine hb.trans ?_
  have hd3:D^3≤‖eisEmbedding p‖^9:=by
    calc
      _≤(‖eisEmbedding p‖^3)^3:=pow_le_pow_left₀ hD.le hd 3
      _=_:=by ring
  calc
    K/(v/D)^3=K*D^3/v^3:=by field_simp
    _≤K*‖eisEmbedding p‖^9/v^3:=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hd3 hK) (pow_nonneg hv.le 3)

theorem cubeSourceDifference_cubic_decay_from_height (p:Eis) (hp:Prime p)
    (hprimary:lambda^2∣p-1) (a:ℝ) (ha:0<a) :
    ∃C:ℝ,0≤C∧∀M:SL(2,Eis),∀z:ℂ,∀v:ℝ,∀hv:0<v,a≤v→
      ‖cubeSourceDifference p hp.ne_zero (integralComplexMatrix M • upperPoint z v hv)‖≤C/v^3 := by
  have hr:0<‖eisEmbedding p‖:=norm_pos_iff.mpr (eisEmbedding_ne_zero hp.ne_zero)
  have hr1:1≤‖eisEmbedding p‖:=cubePrime_norm_ge_one p hp.ne_zero
  obtain ⟨K,hK,hrep⟩:=sourceCuspRemainder_representatives_decay
    (a/‖eisEmbedding p‖^3) (by positivity)
  refine ⟨K*(‖eisEmbedding p‖^9+(Ideal.absNorm (Ideal.span {p}):ℝ)⁻¹),by positivity,?_⟩
  intro M z v hv hav
  have hlow:a/‖eisEmbedding p‖^3≤v:=by
    calc
      _≤a:=div_le_self ha.le (one_le_pow₀ hr1)
      _≤v:=hav
  have hbase:=sourceCuspRemainder_bound_all K _ hrep M z v hv hlow
  let d (r:Eis⧸Ideal.span {p^3}):=actualCubeCuspData M p
    (GaussianShiftedPartition.representative (p^3) r) hp hprimary
  have hsum:=cube_normalized_sum_bound p hp.ne_zero
    (fun r=>cubeReducedRemainder (d r) hp.ne_zero z v hv) (K*‖eisEmbedding p‖^9/v^3)
    (by positivity) (fun r=>cubeReducedRemainder_bound_from_height (d r) hp.ne_zero a K ha hK hrep z v hv hav)
  have hrest:‖(Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹*sourceCuspRemainder M z v hv‖≤
      (Ideal.absNorm (Ideal.span {p}):ℝ)⁻¹*(K/v^3):=by
    rw [norm_mul,norm_inv,Complex.norm_natCast]
    exact mul_le_mul_of_nonneg_left hbase (inv_nonneg.mpr (Nat.cast_nonneg _))
  unfold cubeSourceDifference
  rw [cubeSource_difference_eq_remainders M p hp hprimary z v hv]
  refine (norm_sub_le _ _).trans ?_
  calc
    _≤K*‖eisEmbedding p‖^9/v^3+(Ideal.absNorm (Ideal.span {p}):ℝ)⁻¹*(K/v^3):=
      add_le_add hsum hrest
    _=_:=by ring

end

section
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CubicKubota EisensteinCuspModThree
local notation "Eis" => ActualEisensteinCubic.O

def cubeInverseLeftMatrix (q:Eis) : SL(2,Eis) :=
  ⟨!![3*q,1;-1,0],by simp⟩

lemma cubeAverageMatrix_inverse_factor (p:Eis) (hp:p≠0) (q:Eis) :
    (cubeAverageMatrix p hp q)⁻¹=
      integralComplexMatrix (cubeInverseLeftMatrix q)*cubeAverageMatrix p hp 0*
        integralComplexMatrix (rationalEmbedding ModularGroup.S) := by
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_inv, Matrix.SpecialLinearGroup.coe_mul,
    cubeAverageMatrix_entries]
  apply Matrix.ext
  intro i j
  simp only [Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two,
    integralComplexMatrix_apply, rationalEmbedding, Matrix.SpecialLinearGroup.map_apply_coe]
  fin_cases i <;> fin_cases j <;>
    simp [cubeInverseLeftMatrix, ModularGroup.S, map_ofNat]
  ring

lemma cubeAverageMatrix_inverse_cusp_factor (M:SL(2,Eis)) (p q:Eis)
    (hp:Prime p) (hprimary:lambda^2∣p-1) :
    let d:=actualCubeCuspData (rationalEmbedding ModularGroup.S*M) p 0 hp hprimary
    (cubeAverageMatrix p hp.ne_zero q)⁻¹*integralComplexMatrix M=
      integralComplexMatrix (cubeInverseLeftMatrix q*d.matrix)*cubeCuspTriangular d hp.ne_zero := by
  dsimp only
  let d:=actualCubeCuspData (rationalEmbedding ModularGroup.S*M) p 0 hp hprimary
  calc
    _=integralComplexMatrix (cubeInverseLeftMatrix q)*
        (cubeAverageMatrix p hp.ne_zero 0*integralComplexMatrix (rationalEmbedding ModularGroup.S*M)):=by
      rw [cubeAverageMatrix_inverse_factor,map_mul]
      group
    _=integralComplexMatrix (cubeInverseLeftMatrix q)*
        (integralComplexMatrix d.matrix*cubeCuspTriangular d hp.ne_zero):=by
      rw [cubeCuspTriangular_factor d hp.ne_zero]
    _=integralComplexMatrix (cubeInverseLeftMatrix q*d.matrix)*cubeCuspTriangular d hp.ne_zero:=by
      rw [map_mul,mul_assoc]

end

open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CubicKubota EisensteinCuspModThree
local notation "Eis" => ActualEisensteinCubic.O

theorem cubeSourceDifference_inverse_cubic_decay (p:Eis) (hp:Prime p)
    (hprimary:lambda^2∣p-1) :
    ∃C:ℝ,0≤C∧∀q:Eis,∀M:SL(2,Eis),∀z:ℂ,∀v:ℝ,∀hv:0<v,1≤v→
      ‖cubeSourceDifference p hp.ne_zero ((cubeAverageMatrix p hp.ne_zero q)⁻¹ •
        (integralComplexMatrix M • upperPoint z v hv))‖≤C/v^3 := by
  have hr:0<‖eisEmbedding p‖:=norm_pos_iff.mpr (eisEmbedding_ne_zero hp.ne_zero)
  obtain ⟨K,hK,hdecay⟩:=cubeSourceDifference_cubic_decay_from_height p hp hprimary
    (‖eisEmbedding p‖^3)⁻¹ (by positivity)
  refine ⟨K*‖eisEmbedding p‖^9,by positivity,?_⟩
  intro q M z v hv hv1
  let d:=actualCubeCuspData (rationalEmbedding ModularGroup.S*M) p 0 hp hprimary
  let T:=cubeCuspTriangular d hp.ne_zero
  let D:=‖T 1 1‖^2
  have hT:T 1 0=0:=(cubeCuspTriangular_entries d hp.ne_zero).2.1
  have hD:0<D:=cubeCuspTriangular_norm_sq_pos d hp.ne_zero
  have hDle:D≤‖eisEmbedding p‖^3:=cubeCuspTriangular_norm_sq_le d hp.ne_zero
  have hlow:(‖eisEmbedding p‖^3)⁻¹≤v/D:=by
    apply (le_div_iff₀ hD).mpr
    calc
      _≤(‖eisEmbedding p‖^3)⁻¹*‖eisEmbedding p‖^3:=
        mul_le_mul_of_nonneg_left hDle (by positivity)
      _=1:=inv_mul_cancel₀ (pow_ne_zero 3 hr.ne')
      _≤v:=hv1
  have hfactor: (cubeAverageMatrix p hp.ne_zero q)⁻¹*integralComplexMatrix M=
      integralComplexMatrix (cubeInverseLeftMatrix q*d.matrix)*T :=
    cubeAverageMatrix_inverse_cusp_factor M p q hp hprimary
  have hact: (cubeAverageMatrix p hp.ne_zero q)⁻¹ •
      (integralComplexMatrix M • upperPoint z v hv)=
      integralComplexMatrix (cubeInverseLeftMatrix q*d.matrix) •
        upperPoint ((T 0 0*z+T 0 1)/T 1 1) (v/D) (div_pos hv hD) := by
    rw [←mul_smul,hfactor,mul_smul,complex_upper_triangular_action T hT z v hv]
  rw [hact]
  refine (hdecay (cubeInverseLeftMatrix q*d.matrix) _ _ _ hlow).trans ?_
  have hd3:D^3≤‖eisEmbedding p‖^9:=by
    calc
      _≤(‖eisEmbedding p‖^3)^3:=pow_le_pow_left₀ hD.le hDle 3
      _=_:=by ring
  calc
    K/(v/D)^3=K*D^3/v^3:=by field_simp
    _≤K*‖eisEmbedding p‖^9/v^3:=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hd3 hK) (pow_nonneg hv.le 3)

end CubicEisenstein

open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups InnerProductSpace
open Finset AddChar MulChar EisensteinEmbedding

namespace CubicEisenstein
local notation "O" => ActualEisensteinCubic.O

lemma kernelSourcePullback_pairing_inverse (M : CubicKubota.levelTwo) (F G : KernelQuotientL2) :
    inner ℂ F (kernelSourcePullback M G)=inner ℂ (kernelSourcePullback M⁻¹ F) G := by
  calc
    _ = inner ℂ (kernelSourcePullback M (kernelSourcePullback M⁻¹ F)) (kernelSourcePullback M G) := by
      rw [kernelSourcePullback_comp,inv_mul_cancel,kernelSourcePullback_one]
    _ = _ := LinearIsometry.inner_map_map _ _ _

lemma kernelSourcePullback_integral_cusp_decay (M : CubicKubota.levelTwo)
    (f : KernelQuotient→ℂ) (C : ℝ)
    (hdec : ∀N : SL(2,ActualEisensteinCubic.O),∀z : ℂ,∀v : ℝ,∀hv : 0<v,1<v→
      ‖f (integralOrbitProjection globalKubotaKernel
        (integralComplexMatrix N•upperPoint z v hv))‖≤C/v^3)
    (N : SL(2,ActualEisensteinCubic.O)) (z : ℂ) (v : ℝ) (hv : 0<v) (hlarge : 1<v) :
    ‖f (kernelSourceAction M (integralOrbitProjection globalKubotaKernel
      (integralComplexMatrix N•upperPoint z v hv)))‖≤C/v^3 := by
  rw [kernelSourceAction_mk]
  change ‖f (integralOrbitProjection globalKubotaKernel
    (integralComplexMatrix (M:SL(2,ActualEisensteinCubic.O))•(integralComplexMatrix N•upperPoint z v hv)))‖≤C/v^3
  have hh := hdec ((M:SL(2,ActualEisensteinCubic.O))*N) z v hv hlarge
  simpa only [map_mul,mul_smul] using hh

lemma cubicEisensteinResidue_source_translate_orthogonal
    (F : KernelQuotientL2) (hF : (F,(8/9:ℂ)•F)∈kernelEnergyLaplacian.graph)
    (f : KernelQuotient→ℂ) (hrep : F=ᵐ[integralQuotientVolume globalKubotaKernel]f)
    (C : ℝ) (hC : 0≤C)
    (hdec : ∀N : SL(2,ActualEisensteinCubic.O),∀z : ℂ,∀v : ℝ,∀hv : 0<v,1<v→
      ‖f (integralOrbitProjection globalKubotaKernel
        (integralComplexMatrix N•upperPoint z v hv))‖≤C/v^3)
    (M : CubicKubota.levelTwo) :
    inner ℂ F (kernelSourcePullback M cubicEisensteinResidue)=0 := by
  rw [kernelSourcePullback_pairing_inverse]
  have hrepM : kernelSourcePullback M⁻¹ F=ᵐ[integralQuotientVolume globalKubotaKernel]
      fun q=>f (kernelSourceAction M⁻¹ q) :=
    (kernelSourcePullback_ae_eq M⁻¹ F).trans
      ((kernelSourceAction_measurePreserving M⁻¹).quasiMeasurePreserving.ae_eq_comp hrep)
  apply cubicEisensteinResidue_orthogonal_of_cusp_chart_decay _
    (kernelSource_eigenvector M⁻¹ F (8/9:ℂ) hF) _ hrepM C hC
  intro N z v hv hlarge
  exact kernelSourcePullback_integral_cusp_decay M⁻¹ f C hdec (N:SL(2,ActualEisensteinCubic.O)) z v hv hlarge

theorem cubicSourceResidue_orthogonal_of_integral_cusp_decay
    (F : KernelQuotientL2) (hF : (F,(8/9:ℂ)•F)∈kernelEnergyLaplacian.graph)
    (f : KernelQuotient→ℂ) (hrep : F=ᵐ[integralQuotientVolume globalKubotaKernel]f)
    (C : ℝ) (hC : 0≤C)
    (hdec : ∀N : SL(2,ActualEisensteinCubic.O),∀z : ℂ,∀v : ℝ,∀hv : 0<v,1<v→
      ‖f (integralOrbitProjection globalKubotaKernel
        (integralComplexMatrix N•upperPoint z v hv))‖≤C/v^3) :
    inner ℂ F (kernelSourceProjection cubicEisensteinResidue)=0 := by
  rw [kernelSourceProjection_apply,inner_smul_right,inner_sum]
  simp only [cubicEisensteinResidue_source_translate_orthogonal F hF f hrep C hC hdec,
    Finset.sum_const_zero,mul_zero]

theorem commonCover_source_span_vanish {H : Subgroup (SL(2,ActualEisensteinCubic.O))} {ι : Type*} [Fintype ι]
    (leg : ι→KernelQuotientL2→L[ℂ]IntegralQuotientL2 H) (c : ι→ℂ)
    (D : IntegralQuotientL2 H)
    (hD : D=∑i,c i • leg i (kernelSourceProjection cubicEisensteinResidue))
    (hEig : ∀i,(ContinuousLinearMap.adjoint (leg i) D,
      (8/9:ℂ)•ContinuousLinearMap.adjoint (leg i) D)∈kernelEnergyLaplacian.graph)
    (f : ι→KernelQuotient→ℂ)
    (hrep : ∀i,ContinuousLinearMap.adjoint (leg i) D=ᵐ[integralQuotientVolume globalKubotaKernel]f i)
    (C : ι→ℝ) (hC : ∀i,0≤C i)
    (hdec : ∀i,∀N : SL(2,ActualEisensteinCubic.O),∀z : ℂ,∀v : ℝ,∀hv : 0<v,1<v→
      ‖f i (integralOrbitProjection globalKubotaKernel
        (integralComplexMatrix N•upperPoint z v hv))‖≤C i/v^3) : D=0 := by
  apply (inner_self_eq_zero (𝕜:=ℂ)).mp
  calc
    inner ℂ D D=inner ℂ D (∑i,c i • leg i (kernelSourceProjection cubicEisensteinResidue)) :=
      congrArg (inner ℂ D) hD
    _ = ∑i,c i * inner ℂ D (leg i (kernelSourceProjection cubicEisensteinResidue)) := by
      simp only [inner_sum,inner_smul_right]
    _ = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      rw [←ContinuousLinearMap.adjoint_inner_left]
      rw [cubicSourceResidue_orthogonal_of_integral_cusp_decay _ (hEig i) (f i) (hrep i) (C i) (hC i) (hdec i),mul_zero]

end CubicEisenstein

open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups InnerProductSpace
open Finset AddChar MulChar EisensteinEmbedding

namespace CubicEisenstein
local notation "O" => ActualEisensteinCubic.O

theorem kernelCoverLeg_adjoint_sum_eigenvector
    {H : Subgroup (SL(2,ActualEisensteinCubic.O))} {ι : Type*} [Fintype ι]
    (J : ι→Subgroup (SL(2,ActualEisensteinCubic.O)))
    (hHK : H≤globalKubotaKernel) (hJK : ∀i,J i≤globalKubotaKernel)
    [∀i,(J i).IsFiniteRelIndex globalKubotaKernel]
    (e : ∀i,H≃*J i) (g : ι→SL(2,ℂ)) (he : ∀i,IntegralCoverIntertwines (e i) (g i))
    (F : KernelQuotientL2) (eigenvalue : ℂ)
    (hF : (F,eigenvalue • F)∈kernelEnergyLaplacian.graph)
    (c : ι→ℂ) (j : ι) :
    let D := ∑i,c i • kernelCoverLeg hHK (hJK i) (e i) (g i) (he i) F
    (ContinuousLinearMap.adjoint (kernelCoverLeg hHK (hJK j) (e j) (g j) (he j)) D,
      eigenvalue • ContinuousLinearMap.adjoint (kernelCoverLeg hHK (hJK j) (e j) (g j) (he j)) D)
      ∈kernelEnergyLaplacian.graph := by
  let traced (i : ι) :=
    ContinuousLinearMap.adjoint (kernelCoverLeg hHK (hJK j) (e j) (g j) (he j))
      (kernelCoverLeg hHK (hJK i) (e i) (g i) (he i) F)
  have hi (i : ι) : (traced i,eigenvalue • traced i)∈kernelEnergyLaplacian.graph := by
    change (((ContinuousLinearMap.adjoint (kernelCoverLeg hHK (hJK j) (e j) (g j) (he j))).comp
      (kernelCoverLeg hHK (hJK i) (e i) (g i) (he i))) F,
      eigenvalue • ((ContinuousLinearMap.adjoint (kernelCoverLeg hHK (hJK j) (e j) (g j) (he j))).comp
      (kernelCoverLeg hHK (hJK i) (e i) (g i) (he i))) F)∈kernelEnergyLaplacian.graph
    rw [kernelCoverLeg_adjoint_comp]
    exact kernelCorrespondence_eigenvector _ _ _ _ _ F eigenvalue hF
  have hsum : (∑i,c i • (traced i,eigenvalue • traced i))∈kernelEnergyLaplacian.graph :=
    kernelEnergyLaplacian.graph.sum_mem (fun i _=>kernelEnergyLaplacian.graph.smul_mem (c i) (hi i))
  have hEq : (∑i,c i • (traced i,eigenvalue • traced i))=
      (∑i,c i • traced i,eigenvalue • ∑i,c i • traced i) := by
    apply Prod.ext <;> simp [Prod.fst_sum,Prod.snd_sum,Finset.smul_sum,smul_smul,mul_comm]
  rw [hEq] at hsum
  simpa only [map_sum,map_smul] using hsum

end CubicEisenstein

end

end OAI
