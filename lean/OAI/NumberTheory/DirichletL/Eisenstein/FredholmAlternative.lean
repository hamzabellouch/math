import OAI.NumberTheory.DirichletL.CubicSieve.ClosedRecursion

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
open Filter MeasureTheory
open scoped BigOperators Classical Topology InnerProductSpace

section

variable {E F G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
  [NormedAddCommGroup G] [NormedSpace ℂ G]

omit [CompleteSpace E] in
lemma ker_orthogonal_restriction_injective (T : E→L[ℂ]F) :
    Function.Injective (T.domRestrict T.kerᗮ) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro u hu
  apply Subtype.ext
  apply (inner_self_eq_zero (𝕜 := ℂ)).mp
  exact T.ker.inner_right_of_mem_orthogonal hu u.2

lemma ker_orthogonal_restriction_range (T : E→L[ℂ]F) :
    Set.range (T.domRestrict T.kerᗮ)=Set.range T := by
  let : CompleteSpace T.ker := T.isClosed_ker.completeSpace_coe
  apply Set.Subset.antisymm
  · rintro _ ⟨u,rfl⟩
    exact ⟨u.1,rfl⟩
  · rintro _ ⟨u,rfl⟩
    refine ⟨⟨u-T.ker.starProjection u,T.ker.sub_starProjection_mem_orthogonal u⟩,?_⟩
    change T (u-T.ker.starProjection u)=T u
    rw [map_sub]
    have hz : T (T.ker.starProjection u)=0 := T.ker.starProjection_apply_mem u
    rw [hz,sub_zero]

lemma ker_orthogonal_restriction_antilipschitz (T : E→L[ℂ]F) (K : E→L[ℂ]G)
    (hK : IsCompactOperator K) (A B : ℝ)
    (hest : ∀u,‖u‖^2≤A*‖T u‖^2+B*‖K u‖^2) :
    ∃D : NNReal,AntilipschitzWith D (T.domRestrict T.kerᗮ) := by
  let : CompleteSpace T.kerᗮ := T.ker.isClosed_orthogonal.completeSpace_coe
  apply antilipschitz_of_injective_compact_estimate (T.domRestrict T.kerᗮ)
    (K.domRestrict T.kerᗮ) (hK.comp_clm T.kerᗮ.subtypeL) A B
      (fun u => hest u) (ker_orthogonal_restriction_injective T)

lemma closed_range_of_compact_estimate (T : E→L[ℂ]F) (K : E→L[ℂ]G)
    (hK : IsCompactOperator K) (A B : ℝ)
    (hest : ∀u,‖u‖^2≤A*‖T u‖^2+B*‖K u‖^2) : IsClosed (Set.range T) := by
  let : CompleteSpace T.kerᗮ := T.ker.isClosed_orthogonal.completeSpace_coe
  obtain ⟨D,hD⟩ := ker_orthogonal_restriction_antilipschitz T K hK A B hest
  rw [←ker_orthogonal_restriction_range T]
  exact hD.isClosed_range (T.domRestrict T.kerᗮ).uniformContinuous

lemma selfAdjoint_range_eq_ker_orthogonal (T : E→L[ℂ]E) (hT : IsSelfAdjoint T)
    (hrange : IsClosed (Set.range T)) : T.range=T.kerᗮ := by
  have hh := T.orthogonal_ker
  rw [hT.adjoint_eq] at hh
  rw [hrange.submodule_topologicalClosure_eq] at hh
  exact hh.symm

end

section
variable {E G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup G] [NormedSpace ℂ G]

lemma selfAdjoint_fredholm_of_compact_estimate (T : E→L[ℂ]E) (hT : IsSelfAdjoint T)
    (K : E→L[ℂ]G) (hK : IsCompactOperator K) (A B : ℝ)
    (hest : ∀u,‖u‖^2≤A*‖T u‖^2+B*‖K u‖^2) : T.IsFredholm := by
  let : CompleteSpace T.ker := T.isClosed_ker.completeSpace_coe
  let : FiniteDimensional ℂ T.ker := finiteDimensional_ker_of_compact_estimate T K hK A B hest
  let : T.kerᗮ.CoFG :=
    (T.kerᗮ.quotientEquivOfIsCompl T.ker T.ker.isCompl_orthogonal.symm).symm.finiteDimensional
  have hrange := closed_range_of_compact_estimate T K hK A B hest
  have heq := selfAdjoint_range_eq_ker_orthogonal T hT hrange
  let : T.range.CoFG := heq.symm ▸ (inferInstance : T.kerᗮ.CoFG)
  obtain ⟨D,hD⟩ := ker_orthogonal_restriction_antilipschitz T K hK A B hest
  let : CompleteSpace T.kerᗮ := T.ker.isClosed_orthogonal.completeSpace_coe
  have hf : (T.domRestrict T.kerᗮ).IsFredholm := by
    apply (hD.isClosedEmbedding (T.domRestrict T.kerᗮ).uniformContinuous).isFredholm
    have he : (T.domRestrict T.kerᗮ).range=T.range := by
      apply SetLike.coe_injective
      exact ker_orthogonal_restriction_range T
    rw [he]
    infer_instance
  exact (ContinuousLinearMap.isFredholm_domRestrict_iff T.ker.isClosed_orthogonal).mp hf

end

def kernelSpectralFormOperator (z : ℂ) : KernelEnergyGraph→L[ℂ]KernelEnergyGraph :=
  ContinuousLinearMap.id ℂ KernelEnergyGraph-
    (z+1)•(kernelEnergyMass.adjoint.comp kernelEnergyMass)

lemma kernelSpectralFormOperator_inner (z : ℂ) (u : KernelEnergyGraph) :
    inner ℂ u (kernelSpectralFormOperator z u)=
      ((‖kernelEnergyGradient u‖^2:ℝ):ℂ)-z*((‖kernelEnergyMass u‖^2:ℝ):ℂ) := by
  change inner ℂ u (u-(z+1)•kernelEnergyMass.adjoint (kernelEnergyMass u))=_
  rw [inner_sub_right,inner_smul_right u (kernelEnergyMass.adjoint (kernelEnergyMass u)) (z + 1),kernelEnergyMass.adjoint_inner_right,
    inner_self_eq_norm_sq_to_K,inner_self_eq_norm_sq_to_K]
  simp only [RCLike.ofReal_eq_complex_ofReal,←Complex.ofReal_pow,kernelEnergyGraph_norm_sq,Complex.ofReal_add]
  ring

lemma kernelSpectralFormOperator_selfAdjoint (spectralParam : ℝ) :
    IsSelfAdjoint (kernelSpectralFormOperator (spectralParam:ℂ)) := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  apply (LinearMap.isSymmetric_iff_inner_map_self_real _).mpr
  intro u
  have hh := kernelSpectralFormOperator_inner (spectralParam:ℂ) u
  have hr : inner ℂ (kernelSpectralFormOperator (spectralParam:ℂ) u) u=
      (((‖kernelEnergyGradient u‖^2-spectralParam*‖kernelEnergyMass u‖^2):ℝ):ℂ) := by
    rw [←inner_conj_symm,kernelSpectralFormOperator_inner]
    simp only [map_sub,map_mul,Complex.conj_ofReal,Complex.ofReal_sub,Complex.ofReal_mul]
  change (starRingEnd ℂ) (inner ℂ (kernelSpectralFormOperator (spectralParam:ℂ) u) u)=
    inner ℂ (kernelSpectralFormOperator (spectralParam:ℂ) u) u
  rw [hr,Complex.conj_ofReal]

lemma scalar_compact_energy_estimate (m g n t k spectralParam C : ℝ)
    (_hn : 0≤n) (_ht : 0≤t) (hspectralParam : 0≤spectralParam) (hspectralParamone : spectralParam<1) (hC : 0≤C)
    (hspace : n^2=m^2+g^2) (hcore : m^2≤g^2+C*k^2)
    (hform : g^2-spectralParam*m^2≤n*t) :
    n^2≤(4/(1-spectralParam)^2)*t^2+(4*C/(1-spectralParam))*k^2 := by
  have hd : 0<1-spectralParam := sub_pos.mpr hspectralParamone
  have hlow : (1-spectralParam)/2*n^2≤n*t+C*k^2 := by
    nlinarith [mul_nonneg (show 0≤1+spectralParam by linarith) (sub_nonneg.mpr hcore),
      mul_nonneg hd.le (mul_nonneg hC (sq_nonneg k))]
  have hlow' := mul_le_mul_of_nonneg_left hlow (show 0≤4*(1-spectralParam) by positivity)
  have hsq : (1-spectralParam)^2*n^2≤4*t^2+4*(1-spectralParam)*C*k^2 := by
    nlinarith [sq_nonneg ((1-spectralParam)*n-2*t)]
  have he : (4/(1-spectralParam)^2)*t^2+(4*C/(1-spectralParam))*k^2=
      (4*t^2+4*(1-spectralParam)*C*k^2)/(1-spectralParam)^2 := by
    field_simp [hd.ne']
  rw [he]
  exact (le_div_iff₀ (sq_pos_of_pos hd)).mpr (by nlinarith [hsq])

lemma kernelSpectralFormOperator_compact_estimate
    (K : Set KernelQuotient) (hK : MeasurableSet K) (C : ℝ) (hC : 0≤C)
    (hcore : ∀u : KernelEnergyGraph,‖kernelEnergyMass u‖^2≤‖kernelEnergyGradient u‖^2+
      C*‖kernelEnergyMassRestriction K hK u‖^2)
    (spectralParam : ℝ) (hspectralParam : 0≤spectralParam) (hspectralParamone : spectralParam<1) (u : KernelEnergyGraph) :
    ‖u‖^2≤(4/(1-spectralParam)^2)*‖kernelSpectralFormOperator (spectralParam:ℂ) u‖^2+
      (4*C/(1-spectralParam))*‖kernelEnergyMassRestriction K hK u‖^2 := by
  apply scalar_compact_energy_estimate ‖kernelEnergyMass u‖ ‖kernelEnergyGradient u‖
    ‖u‖ ‖kernelSpectralFormOperator (spectralParam:ℂ) u‖ ‖kernelEnergyMassRestriction K hK u‖ spectralParam C
    (norm_nonneg _) (norm_nonneg _) hspectralParam hspectralParamone hC (kernelEnergyGraph_norm_sq u) (hcore u)
  have hh := re_inner_le_norm (𝕜 := ℂ) u (kernelSpectralFormOperator (spectralParam:ℂ) u)
  rw [kernelSpectralFormOperator_inner] at hh
  simpa only [RCLike.re_to_complex,Complex.sub_re,Complex.mul_re,Complex.ofReal_re,
    Complex.ofReal_im,mul_zero,sub_zero] using hh

lemma kernelSpectralFormOperator_solution_graph (z : ℂ) (F : KernelQuotientL2)
    (v : KernelEnergyGraph) (hv : kernelSpectralFormOperator z v=kernelVariationalSolution F) :
    (kernelEnergyMass v,F+z•kernelEnergyMass v)∈kernelEnergyLaplacian.graph := by
  rw [kernelEnergyLaplacian_graph,mem_kernelLaplacianGraph]
  have hh : v-(z+1)•kernelEnergyMass.adjoint (kernelEnergyMass v)=kernelEnergyMass.adjoint F := hv
  have hv' : kernelEnergyMass.adjoint (F+(z+1)•kernelEnergyMass v)=v := by
    rw [map_add,map_smul]
    exact (sub_eq_iff_eq_add.mp hh).symm
  have he : kernelEnergyMass v+(F+z•kernelEnergyMass v)=F+(z+1)•kernelEnergyMass v := by
    rw [add_smul,one_smul]
    abel
  rw [he]
  change kernelEnergyMass (kernelEnergyMass.adjoint (F+(z+1)•kernelEnergyMass v))=kernelEnergyMass v
  rw [hv']

lemma kernelSpectralFormOperator_of_domain (z : ℂ) (u : kernelEnergyLaplacian.domain) :
    kernelSpectralFormOperator z (kernelVariationalSolution (kernelEnergyLaplacian u+u))=
      kernelVariationalSolution (kernelEnergyLaplacian u-z•(u:KernelQuotientL2)) := by
  have hu : kernelEnergyMass (kernelVariationalSolution (kernelEnergyLaplacian u+u))=u :=
    kernelEnergyLaplacian_resolvent_relation u
  change kernelVariationalSolution (kernelEnergyLaplacian u+u)-
    (z+1)•kernelVariationalSolution (kernelEnergyMass (kernelVariationalSolution (kernelEnergyLaplacian u+u)))=_
  rw [hu,←map_smul,←map_sub]
  congr 1
  rw [add_smul,one_smul]
  abel

theorem kernelSpectralFormOperator_isFredholm (spectralParam : ℝ)
    (hzero : 0≤spectralParam) (hone : spectralParam<1) :
    (kernelSpectralFormOperator (spectralParam:ℂ)).IsFredholm := by
  obtain ⟨K,hK,C,hC,hcompact,hcoercive⟩ := kernel_global_exterior_coercivity
  exact selfAdjoint_fredholm_of_compact_estimate _
    (kernelSpectralFormOperator_selfAdjoint spectralParam)
    (kernelEnergyMassRestriction K hK.measurableSet) hcompact
    (4/(1-spectralParam)^2) (4*C/(1-spectralParam))
    (kernelSpectralFormOperator_compact_estimate K hK.measurableSet C hC hcoercive spectralParam hzero hone)

theorem kernel_theta_spectral_fredholm :
    (kernelSpectralFormOperator (8/9:ℂ)).IsFredholm := by
  convert kernelSpectralFormOperator_isFredholm (8/9) (by norm_num) (by norm_num) using 1
  norm_num

end CubicEisenstein

namespace CanonicalRowCompletion
open SecondPassArithmetic

theorem cubeLogRange_sq_small_power (b ε : ℝ) (_hb : 0≤b) (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀X Z : ℝ,0≤X → 1≤Z → X≤Z^3 →
      ((cubeLogRange b X).card:ℝ)^2≤C*Z^ε := by
  let B:=max 1 b
  let deltaLoss:=ε/2
  let C₀:=1+Real.log B+3/deltaLoss
  have hB : 1≤B:=le_max_left _ _
  have hB0 : 0<B:=zero_lt_one.trans_le hB
  have hδ : 0<deltaLoss:=by dsimp [deltaLoss];positivity
  have hlogB : 0≤Real.log B:=Real.log_nonneg hB
  have hC₀ : 0<C₀:=by dsimp [C₀];positivity
  refine ⟨C₀^2,by positivity,?_⟩
  intro X Z hX hZ hXZ
  have hZ0 : 0<Z:=zero_lt_one.trans_le hZ
  have hZ3 : 1≤Z^3:=one_le_pow₀ hZ
  have hY : 1≤B*Z^3:=one_le_mul_of_one_le_of_one_le hB hZ3
  have hxY : max 1 (b*X)≤B*Z^3 := by
    apply max_le hY
    calc
      b*X ≤ B*X:=mul_le_mul_of_nonneg_right (le_max_right _ _) hX
      _ ≤ B*Z^3:=mul_le_mul_of_nonneg_left hXZ hB0.le
  have hcard : ((cubeLogRange b X).card:ℝ)≤1+Real.log B+3*Real.log Z := by
    rw [cubeLogRange_card,Nat.cast_add,Nat.cast_one]
    have hlog:=normLogBin_le_log_upper (max 1 (b*X)) (B*Z^3)
      (zero_lt_one.trans_le (le_max_left _ _)) hxY hY
    rw [Real.log_mul hB0.ne' (pow_pos hZ0 3).ne',Real.log_pow] at hlog
    norm_num at hlog
    linarith
  have hr : 1≤Z^deltaLoss:=Real.one_le_rpow hZ hδ.le
  have hl : Real.log Z≤Z^deltaLoss/deltaLoss:=Real.log_le_rpow_div hZ0.le hδ
  have hc : 1+Real.log B+3*Real.log Z≤C₀*Z^deltaLoss := by
    calc
      _ ≤ (1+Real.log B)*Z^deltaLoss+3*(Z^deltaLoss/deltaLoss) := by
        gcongr
        exact le_mul_of_one_le_right (by linarith) hr
      _ = _:=by dsimp [C₀];ring
  calc
    _ ≤ (C₀*Z^deltaLoss)^2:=pow_le_pow_left₀ (Nat.cast_nonneg _) (hcard.trans hc) 2
    _ = C₀^2*Z^ε:=by
      rw [mul_pow,←Real.rpow_natCast (Z^deltaLoss) 2,←Real.rpow_mul hZ0.le]
      congr 1
      dsimp [deltaLoss]
      congr 1
      ring

end CanonicalRowCompletion

namespace SecondPassArithmetic
open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding)

theorem halfCanonicalPadding_budget (ε C : ℝ) (hε : 0<ε) (hC : 0≤C) :
    0<canonicalPadding ε C/2 ∧ canonicalPadding ε C/2≤(1:ℝ)/1000 ∧
    3000*(canonicalPadding ε C/2)≤(1:ℝ)/80 ∧
    3001*C*(canonicalPadding ε C/2)≤ε/2 := by
  have h:=canonicalPadding_budget ε C hε hC
  refine ⟨by linarith,by linarith,by linarith,?_⟩
  have hceta : 0≤3001*C*canonicalPadding ε C :=
    mul_nonneg (mul_nonneg (by norm_num) hC) h.1.le
  nlinarith [h.2.2.2.2.1]

theorem canonicalRankMargin_strict_reserve (η : ℝ) (hη : 0≤η)
    (hbudget : 3000*η≤(1:ℝ)/80) (r : ℕ) :
    (3:ℝ)/80≤canonicalRankMargin ((1:ℝ)/20) η r :=
  (by linarith : (3:ℝ)/80≤(1:ℝ)/20-3000*η).trans
    (canonicalRankMargin_lower _ η hη r)

theorem CanonicalStateCondition.fixed_factor_margin
    {base : ActualEisensteinCubic.O→*ℂ} {bad : Ideal ActualEisensteinCubic.O} {Z η : ℝ} {Ψ : ActualEisensteinCubic.O→*ℂ} {m : ActualEisensteinCubic.O}
    {labels : Finset (Ideal ActualEisensteinCubic.O)} {X F K : ℝ}
    (h : CanonicalStateCondition base bad Z η Ψ m labels X F K)
    (hZ : 1≤Z) (hη : 0≤η) (hbudget : 3000*η≤(1:ℝ)/80)
    (C : ℝ) (hC : 0≤C) (hCZ : C≤Z^((1:ℝ)/80)) :
    C*K*‖eisEmbedding m‖^2≤(X*F)*Z^(-((1:ℝ)/40)) := by
  have hZ0 : 0<Z:=zero_lt_one.trans_le hZ
  have hXF : 0≤X*F:=mul_nonneg h.column_pos.le (zero_le_one.trans h.label_ge_one)
  have hm := canonicalRankMargin_strict_reserve η hη hbudget (fixedDepthRank Z K)
  have hi : K*‖eisEmbedding m‖^2≤(X*F)*Z^(-((3:ℝ)/80)) := by
    apply h.invariant.trans
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hZ (neg_le_neg hm)) hXF
  calc
    C*K*‖eisEmbedding m‖^2 = C*(K*‖eisEmbedding m‖^2) := by ring
    _ ≤ C*((X*F)*Z^(-((3:ℝ)/80))) := mul_le_mul_of_nonneg_left hi hC
    _ ≤ Z^((1:ℝ)/80)*((X*F)*Z^(-((3:ℝ)/80))) :=
      mul_le_mul_of_nonneg_right hCZ (mul_nonneg hXF (Real.rpow_nonneg hZ0.le _))
    _ = (X*F)*(Z^((1:ℝ)/80)*Z^(-((3:ℝ)/80))) := by ring
    _ = _ := by rw [←Real.rpow_add hZ0];norm_num

end SecondPassArithmetic

namespace CanonicalRowCompletion

open MeasureTheory
open scoped BigOperators Classical SchwartzMap ContDiff
open ActualEisensteinCubic
open CompletedGauss hiding O
open ConcretePrimeRowBridge hiding O columnWeight
open CanonicalQuadraticSieve hiding O
open SecondPassArithmetic hiding O
open CanonicalCubeSeparation JointLogSeparation
open FirstPassCubeLabels (columnLog)

private theorem height_sum_bound (a b : ℝ) (J : ℕ) :
    (1+|a+b|)^(2*J)≤(1+|a|)^(2*J)*(1+|b|)^(2*J) := by
  have h : 1+|a+b|≤(1+|a|)*(1+|b|) := by
    have := abs_add_le a b
    nlinarith [abs_nonneg a,abs_nonneg b]
  simpa only [mul_pow] using pow_le_pow_left₀ (by positivity : 0≤1+|a+b|) h (2*J)

theorem progressingCanonicalBin_energy
    (S : Finset (Ideal ActualEisensteinCubic.O)) (D : ℕ) (hbad : fixedBadPrimes⊆S)
    (Q : Finset (primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)→₀ℕ))
    (labels : Finset (Ideal ActualEisensteinCubic.O)) (Ψ : ActualEisensteinCubic.O→*ℂ) (m : ActualEisensteinCubic.O) (W : ℝ→ℂ)
    (a b : ℝ) (ha : 0<a) (hs : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (V : 𝓢(ℝ,ℂ)) (hV : ∀u,|u|≤columnWindowRadius a b→V u=1)
    (B ell X H₀ K E oldHeight : ℝ) (J : ℕ)
    (hB : 0<B) (hell : 0<ell) (hX : X=B^3*ell) (hK : 0<K) (hE : 0≤E)
    (hn : ∀v∈Q,B≤(Ideal.absNorm (cubeIdeal (InitialMeanSquare.outsideSquarefreeIdeals S D) v):ℝ))
    (hn' : ∀v∈Q,(Ideal.absNorm (cubeIdeal (InitialMeanSquare.outsideSquarefreeIdeals S D) v):ℝ)≤Real.exp 1*B) :
    let F:=InitialMeanSquare.outsideSquarefreeIdeals S D
    let hF:=InitialMeanSquare.outsideSquarefree_admissible S D hbad
    letI : ∀i : primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
      fun i=>by rw [poolPrimary_span F hF i];infer_instance
    let Q':=progressingCubes S D H₀ Q
    let β:=fun I v=>reopenedCubeCoefficient H₀
      (rowTwist (normHeightTwist Ψ oldHeight) (m*excludedGenerator S) (idealGenerator I) 1) (cubeIdeal F v)
    let n:=fun v=>(Ideal.absNorm (cubeIdeal F v):ℝ)
    (∀ξ : ℝ,B*rowFamilyEnergy labels (fun I z=>
      reopenedCanonicalRow (poolPrimary F) (poolPrimary_ne_zero F hF) (poolPrimary_coprime F hF)
        (poolPrimary_good F hF) Finset.univ Q' (separatedCubeCoefficient (β I) n B ξ)
        Ψ m (idealGenerator I) (fun T=>frequencyTwist V (oldHeight+ξ) (columnLog (poolPrimary F) ell T)) z) K≤
      E*(1+|oldHeight+ξ|)^(2*J)) →
    X*rowFamilyEnergy labels (fun I z=>
      outsideCanonicalBin S D hbad Q (normHeightTwist Ψ oldHeight) m (idealGenerator I) z W X H₀) K≤
      E*(1+|oldHeight|)^(2*J)*
        (∫ξ : ℝ,‖reopeningCoefficient W a b ha hs hW ξ‖*(1+|ξ|)^J)^2 := by
  dsimp only
  let F:=InitialMeanSquare.outsideSquarefreeIdeals S D
  have hF:=InitialMeanSquare.outsideSquarefree_admissible S D hbad
  let : ∀i : primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
    fun i=>by rw [poolPrimary_span F hF i];infer_instance
  let Q':=progressingCubes S D H₀ Q
  let β:=fun I v=>reopenedCubeCoefficient H₀
    (rowTwist (normHeightTwist Ψ oldHeight) (m*excludedGenerator S) (idealGenerator I) 1) (cubeIdeal F v)
  let n:=fun v=>(Ideal.absNorm (cubeIdeal F v):ℝ)
  intro hsource
  have hX0 : 0<X := by rw [hX];positivity
  have hQsub : Q'⊆Q := Finset.filter_subset _ _
  have heq : (fun I z=>outsideCanonicalBin S D hbad Q (normHeightTwist Ψ oldHeight) m (idealGenerator I) z W X H₀)=
      (fun I z=>outsideCanonicalBin S D hbad Q' (normHeightTwist Ψ oldHeight) m (idealGenerator I) z W X H₀) := by
    funext I z
    exact outsideCanonicalBin_filter S D hbad Q _ m _ z W X H₀
  rw [heq]
  have he := outsideCanonicalBin_energy S D hbad Q' labels (normHeightTwist Ψ oldHeight) m W
    a b ha hs hW V hV B ell X H₀ K ((E/B)*(1+|oldHeight|)^(2*J)) J hB hell hX hK
    (by positivity) (fun v hv=>hn v (hQsub hv)) (fun v hv=>hn' v (hQsub hv))
  have hpnt : ∀ξ : ℝ,rowFamilyEnergy labels (fun I z=>
      reopenedCanonicalRow (poolPrimary F) (poolPrimary_ne_zero F hF) (poolPrimary_coprime F hF)
        (poolPrimary_good F hF) Finset.univ Q' (separatedCubeCoefficient (β I) n B ξ)
        (normHeightTwist Ψ oldHeight) m (idealGenerator I)
        (fun T=>frequencyTwist V ξ (columnLog (poolPrimary F) ell T)) z) K≤
      ((E/B)*(1+|oldHeight|)^(2*J))*(1+|ξ|)^(2*J) := by
    intro ξ
    change (∑I∈labels,nonzeroRowMajorantSum _ K).re≤_
    rw [reopenedCanonicalEnergy_two_heights (poolPrimary F) (poolPrimary_ne_zero F hF)
      (poolPrimary_coprime F hF) (poolPrimary_good F hF) Finset.univ Q' labels
      (fun I=>separatedCubeCoefficient (β I) n B ξ) Ψ m V ell K oldHeight ξ hell]
    change rowFamilyEnergy labels _ K≤_
    have ht := (le_div_iff₀ hB).mpr (by simpa only [mul_comm] using hsource ξ)
    calc
      _ ≤ E*(1+|oldHeight+ξ|)^(2*J)/B := by simpa only [Nat.mul_comm J 2] using ht
      _ ≤ E*((1+|oldHeight|)^(2*J)*(1+|ξ|)^(2*J))/B :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (height_sum_bound oldHeight ξ J) hE) hB.le
      _ = _ := by ring
  have hf:=he hpnt
  have hh:=mul_le_mul_of_nonneg_left hf hX0.le
  apply hh.trans_eq
  rw [hX]
  field_simp

end CanonicalRowCompletion

open scoped BigOperators Classical SchwartzMap ContDiff
namespace CompletedGauss
open ActualEisensteinCubic

theorem shortCompletedSum_nonpos (Ψ : ActualEisensteinCubic.O→*ℂ) (W : ℝ→ℂ) (X H₀ : ℝ) (hH : H₀≤0) :
    shortCompletedSum Ψ W X H₀=0 := by
  unfold shortCompletedSum
  calc
    _ = ∑'I : Ideal ActualEisensteinCubic.O,(0:ℂ) := tsum_congr (fun I=>ite_eq_right (not_lt_of_ge (hH.trans (Nat.cast_nonneg (Ideal.absNorm I)))))
    _ = 0 := tsum_zero

end CompletedGauss
namespace CanonicalRowCompletion
open ActualEisensteinCubic
open CompletedGauss hiding O
open ConcretePrimeRowBridge hiding O columnWeight
open CanonicalQuadraticSieve hiding O
open SecondPassArithmetic hiding O
open ConcreteTraceCRT (eisEmbedding)

theorem canonicalLabels_subset_idealRange
    (base : ActualEisensteinCubic.O→*ℂ) (bad : Ideal ActualEisensteinCubic.O) (Z η : ℝ) (Ψ : ActualEisensteinCubic.O→*ℂ) (m : ActualEisensteinCubic.O)
    (labels : Finset (Ideal ActualEisensteinCubic.O)) (X F K : ℝ)
    (hstate : CanonicalStateCondition base bad Z η Ψ m labels X F K)
    (hbad : ∀P∈fixedBadPrimes,P∣bad) : labels⊆idealRange F := by
  intro I hI
  have hb:=hstate.label_bounds I hI
  exact mem_idealRange.mpr ⟨admissible_of_squarefree_coprime_bad I bad hb.2.1 hb.2.2.1 hbad,hb.2.2.2⟩

theorem rowFamilyEnergy_le_rectangle (labels : Finset (Ideal ActualEisensteinCubic.O)) (F K : ℝ)
    (hK : 0<K) (hlabels : labels⊆idealRange F) (P : Ideal ActualEisensteinCubic.O→ActualEisensteinCubic.O→ℂ) :
    rowFamilyEnergy labels P K≤SchwartzMap.seminorm ℝ 0 0 rowMajorant*
      ∑f : idealRange F,∑z∈(firstFrequencyDisk (2*K)).erase 0,‖P f.val z‖^2 := by
  rw [rowFamilyEnergy_eq_sum labels P K hK]
  have hM : 0≤SchwartzMap.seminorm ℝ 0 0 rowMajorant:=apply_nonneg _ _
  calc
    _ ≤ ∑I∈labels,∑z∈(firstFrequencyDisk (2*K)).erase 0,
        SchwartzMap.seminorm ℝ 0 0 rowMajorant*‖P I z‖^2 := by
      apply Finset.sum_le_sum
      intro I hI
      apply Finset.sum_le_sum
      intro z hz
      exact mul_le_mul_of_nonneg_right
        ((Complex.re_le_norm _).trans (SchwartzMap.norm_le_seminorm ℝ rowMajorant _)) (sq_nonneg _)
    _ = SchwartzMap.seminorm ℝ 0 0 rowMajorant*
        ∑I∈labels,∑z∈(firstFrequencyDisk (2*K)).erase 0,‖P I z‖^2 := by
      simp only [Finset.mul_sum]
    _ ≤ SchwartzMap.seminorm ℝ 0 0 rowMajorant*
        ∑I∈idealRange F,∑z∈(firstFrequencyDisk (2*K)).erase 0,‖P I z‖^2 := by
      apply mul_le_mul_of_nonneg_left _ hM
      exact Finset.sum_le_sum_of_subset_of_nonneg hlabels (fun I _ _=>Finset.sum_nonneg (fun z hz=>sq_nonneg _))
    _ = _ := by
      congr 1
      exact (Finset.sum_coe_sort (s:=idealRange F)
        (f:=fun I=>∑z∈(firstFrequencyDisk (2*K)).erase 0,‖P I z‖^2)).symm

theorem canonicalShortEnergy_uniform_twist
    (a b : ℝ) (ha : 0<a) (ε ρ q levelBound : ℝ)
    (hε : 0<ε) (hρ : 0<ρ) (hq : 1<q) (hlevel : 1≤levelBound) :
    ∃d : ℕ,∀W : ℝ→ℂ,Function.support W⊆Set.Icc a b → ContDiff ℝ ∞ W →
    ∃C : ℝ,0≤C ∧ ∀(θ : ℝ) (rays : ℕ) (Z K X F : ℝ),1≤Z → 1≤K → 1≤F →
      F≤Z^((1:ℝ)/1000) → ∀G : Ideal ActualEisensteinCubic.O,G≠0 → (∀P∈fixedBadPrimes,P∣G) →
      (2*K)*(Ideal.absNorm G:ℝ)≤X*F*Z^(-((1:ℝ)/40)) →
    ∀(labels : Finset (Ideal ActualEisensteinCubic.O)),labels⊆idealRange F →
    ∀(Ψ : ActualEisensteinCubic.O→*ℂ),(∀x,‖Ψ x‖≤1) → ∀(mask : ActualEisensteinCubic.O) (lengthScale : ℂ),
      (∀u : ActualEisensteinCubic.Oˣ,∀f : idealRange F,∀H∈shortCubeRange (Z^((1:ℝ)/1000)),
        HasExactCompletedDyadicModels rays (((firstFrequencyDisk (2*K)).erase 0).image (fun z=>Ideal.span {z})) (2*K)
          (X/(Ideal.absNorm H:ℝ)^3) ρ q levelBound f.val (G*f.val)
          (CompletedHeight.normTwistedSource W θ) (CompletedUnitRows.unitRowFamily Ψ mask u f) lengthScale) →
      rowFamilyEnergy labels (fun I z=>shortCompletedSum (rowTwist (normHeightTwist Ψ θ)
        mask (idealGenerator I) z) W X (Z^((1:ℝ)/1000))) K≤
      (C*(1+‖θ‖)^d)*(rays:ℝ)^2*‖lengthScale‖^2*((2*K)*(Ideal.absNorm G:ℝ)*F)^ε*(K*F)*Z^ε := by
  obtain ⟨d,hbound⟩:=CompletedUnitRows.short_completed_elements_uniform_twist a b ha ε ρ q levelBound hε hρ hq hlevel
  refine ⟨d,?_⟩
  intro W hs hW
  obtain ⟨C,hC,h⟩:=hbound W hs hW
  refine ⟨2*SchwartzMap.seminorm ℝ 0 0 rowMajorant*C,by positivity,?_⟩
  intro θ rays Z K X F hZ hK hF hFZ G hG hbad hmargin labels hlabels Ψ hΨ mask lengthScale hmodels
  have hK0 : 0<K:=zero_lt_one.trans_le hK
  have hF0 : 0<F:=zero_lt_one.trans_le hF
  have hT : ∀z∈(firstFrequencyDisk (2*K)).erase 0,
      z≠0 ∧ (Ideal.absNorm (Ideal.span {z}):ℝ)≤2*K := by
    intro z hz
    refine ⟨(Finset.mem_erase.mp hz).1,?_⟩
    rw [←eisEmbedding_norm_sq_eq_absNorm_span]
    exact (mem_firstFrequencyDisk (2*K) z).mp (Finset.mem_erase.mp hz).2
  have hshort:=h θ rays Z (2*K) X F hZ (by linarith) hF hFZ G hG hbad hmargin
    ((firstFrequencyDisk (2*K)).erase 0) hT Ψ hΨ mask lengthScale hmodels
  have hsum := (div_le_iff₀ hF0).mp hshort
  have hrect:=rowFamilyEnergy_le_rectangle labels F K hK0 hlabels
    (fun I z=>shortCompletedSum (rowTwist (normHeightTwist Ψ θ) mask (idealGenerator I) z) W X (Z^((1:ℝ)/1000)))
  exact hrect.trans ((mul_le_mul_of_nonneg_left hsum (apply_nonneg _ _)).trans_eq (by ring))

end CanonicalRowCompletion

open MeasureTheory
open scoped BigOperators Classical SchwartzMap ContDiff
namespace CanonicalRowCompletion
open ActualEisensteinCubic
open CompletedGauss hiding O
open ConcretePrimeRowBridge hiding O columnWeight
open CanonicalQuadraticSieve hiding O
open SecondPassArithmetic hiding O
open CanonicalCubeSeparation JointLogSeparation
open FirstPassCubeLabels (columnLog)

theorem progressingCanonicalFamily_energy
    (S : Finset (Ideal ActualEisensteinCubic.O)) (D : ℕ) (hbad : fixedBadPrimes⊆S) (hSp : ∀P∈S,Prime P)
    (labels : Finset (Ideal ActualEisensteinCubic.O)) (Ψ : ActualEisensteinCubic.O→*ℂ) (m : ActualEisensteinCubic.O) (W : ℝ→ℂ)
    (a b : ℝ) (ha : 0<a) (hb : 0≤b)
    (hs : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W) (hWc : HasCompactSupport W)
    (V : 𝓢(ℝ,ℂ)) (hV : ∀u,|u|≤columnWindowRadius a b→V u=1)
    (X H₀ K E oldHeight : ℝ) (J : ℕ)
    (hX : 0<X) (hK : 0<K) (hE : 0≤E) (hD : b*X≤D) :
    let F:=InitialMeanSquare.outsideSquarefreeIdeals S D
    let hF:=InitialMeanSquare.outsideSquarefree_admissible S D hbad
    letI : ∀i : primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
      fun i=>by rw [poolPrimary_span F hF i];infer_instance
    let β:=fun I v=>reopenedCubeCoefficient H₀
      (rowTwist (normHeightTwist Ψ oldHeight) (m*excludedGenerator S) (idealGenerator I) 1) (cubeIdeal F v)
    let n:=fun v=>(Ideal.absNorm (cubeIdeal F v):ℝ)
    (∀j∈cubeLogRange b X,
      let B:=normLogScale j
      let Q':=progressingCubes S D H₀ (activeCubeLogBin S D b X j)
      Q'.Nonempty → ∀ξ : ℝ,B*rowFamilyEnergy labels (fun I z=>
        reopenedCanonicalRow (poolPrimary F) (poolPrimary_ne_zero F hF) (poolPrimary_coprime F hF)
          (poolPrimary_good F hF) Finset.univ Q' (separatedCubeCoefficient (β I) n B ξ)
          Ψ m (idealGenerator I)
          (fun T=>frequencyTwist V (oldHeight+ξ) (columnLog (poolPrimary F) (X/B^3) T)) z) K≤
        E*(1+|oldHeight+ξ|)^(2*J)) →
    rowFamilyEnergy labels (fun I z=>outsideCanonicalRow S D hbad (normHeightTwist Ψ oldHeight)
      m (idealGenerator I) z W X) K≤
    2*X*rowFamilyEnergy labels (fun I z=>
      shortCompletedSum (rowTwist (normHeightTwist Ψ oldHeight) (m*excludedGenerator S) (idealGenerator I) z) W X H₀) K+
    2*((cubeLogRange b X).card:ℝ)^2*E*(1+|oldHeight|)^(2*J)*
      (∫ξ : ℝ,‖reopeningCoefficient W a b ha hs hW ξ‖*(1+|ξ|)^J)^2 := by
  dsimp only
  let F:=InitialMeanSquare.outsideSquarefreeIdeals S D
  have hF:=InitialMeanSquare.outsideSquarefree_admissible S D hbad
  let : ∀i : primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
    fun i=>by rw [poolPrimary_span F hF i];infer_instance
  intro hsource
  let T:=E*(1+|oldHeight|)^(2*J)*(∫ξ : ℝ,‖reopeningCoefficient W a b ha hs hW ξ‖*(1+|ξ|)^J)^2
  have hT : 0≤T := by dsimp only [T];positivity
  let binEnergy:=fun j=>rowFamilyEnergy labels (fun I z=>
    outsideCanonicalBin S D hbad (activeCubeLogBin S D b X j) (normHeightTwist Ψ oldHeight)
      m (idealGenerator I) z W X H₀) K
  have hbin (j : ℕ) (hj : j∈cubeLogRange b X) : X*binEnergy j≤T := by
    by_cases hnon : (progressingCubes S D H₀ (activeCubeLogBin S D b X j)).Nonempty
    · apply progressingCanonicalBin_energy S D hbad (activeCubeLogBin S D b X j) labels Ψ m W
        a b ha hs hW V hV (normLogScale j) (X/(normLogScale j)^3) X H₀ K E oldHeight J
        (normLogScale_pos j) (div_pos hX (pow_pos (normLogScale_pos j) _))
        (by field_simp [(normLogScale_pos j).ne']) hK hE
        (fun v hv=>(activeCubeLogBin_norms S D b X j v hv).1)
        (fun v hv=>(activeCubeLogBin_norms S D b X j v hv).2)
      exact hsource j hj hnon
    · have hempty:=Finset.not_nonempty_iff_eq_empty.mp hnon
      have heq : (fun I z=>outsideCanonicalBin S D hbad (activeCubeLogBin S D b X j)
          (normHeightTwist Ψ oldHeight) m (idealGenerator I) z W X H₀)=(fun _ _=>0) := by
        funext I z
        exact outsideCanonicalBin_zero_of_empty_filter S D hbad _ _ m _ z W X H₀ hempty
      dsimp only [binEnergy]
      rw [heq]
      simpa only [rowFamilyEnergy,nonzeroRowMajorantSum,norm_zero,zero_pow (by decide : (2:ℕ)≠0),
        Complex.ofReal_zero,mul_zero,ite_self,tsum_zero,Finset.sum_const_zero,Complex.zero_re] using hT
  have hsum : X*∑j∈cubeLogRange b X,binEnergy j≤((cubeLogRange b X).card:ℝ)*T := by
    simpa only [Finset.mul_sum,Finset.sum_const,nsmul_eq_mul] using Finset.sum_le_sum hbin
  have hwhole:=outsideCanonicalRow_family_binned_energy S D hbad hSp (normHeightTwist Ψ oldHeight)
    m labels W hWc b X H₀ K hb hX hK (fun x hx=>(hs hx).2) hD
  calc
    _ ≤ 2*X*(rowFamilyEnergy labels (fun I z=>
        shortCompletedSum (rowTwist (normHeightTwist Ψ oldHeight) (m*excludedGenerator S) (idealGenerator I) z) W X H₀) K+
        (cubeLogRange b X).card*∑j∈cubeLogRange b X,binEnergy j) := hwhole
    _ = 2*X*rowFamilyEnergy labels (fun I z=>
        shortCompletedSum (rowTwist (normHeightTwist Ψ oldHeight) (m*excludedGenerator S) (idealGenerator I) z) W X H₀) K+
        (2*((cubeLogRange b X).card:ℝ))*(X*∑j∈cubeLogRange b X,binEnergy j) := by ring
    _ ≤ 2*X*rowFamilyEnergy labels (fun I z=>
        shortCompletedSum (rowTwist (normHeightTwist Ψ oldHeight) (m*excludedGenerator S) (idealGenerator I) z) W X H₀) K+
        (2*((cubeLogRange b X).card:ℝ))*(((cubeLogRange b X).card:ℝ)*T) := by gcongr
    _ = _ := by dsimp only [T];ring

end CanonicalRowCompletion

end

end OAI
