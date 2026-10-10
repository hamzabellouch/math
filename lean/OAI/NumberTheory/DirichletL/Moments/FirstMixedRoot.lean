import OAI.NumberTheory.DirichletL.Moments.FirstMixedAllowance
import OAI.NumberTheory.DirichletL.Moments.FirstExceptionalPrefactorActual
import OAI.NumberTheory.DirichletL.Moments.FirstPhysicalSourceFixedFamily

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentFirstMixedRoot
open CanonicalQuadraticSieve CenteredMomentFirstMixedAllowance
open CenteredMomentFirstCanonicalAllowance CenteredMomentFirstNonexceptionalPrefactor
open CenteredMomentCanonicalFirst CenteredMomentRankinRadical CenteredMomentCompleteCommon
open CenteredMomentFirstPhysicalSource CenteredMomentFirstCanonicalFamily
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge HeckeFamily
open CenteredMomentFirstScale CenteredMomentSupportedCorrelation
local notation "O"=>HeckeFamily.O

lemma active_span_swap (C D:Ideal O):
    Ideal.span {activeConductor D C}=Ideal.span {activeConductor C D}:=by
  rw [activeConductor_span_filter,activeConductor_span_filter,
    CenteredMomentCompleteCommon.commonSupport_comm D C]
  congr 1
  apply Finset.filter_congr
  intro P hP
  simp only [CenteredMomentActive.netExponent]
  omega

lemma allowance_pair (C D:Ideal O)(hC:Supported C)(hD:Supported D)
    (hCD:CompletedGauss.primeSupport C=CompletedGauss.primeSupport D)(Z:ℝ)(hZ:1<Z):
    allowance C D Z+allowance D C Z≤
      Real.logb Z (C.absNorm:ℝ)+Real.logb Z (D.absNorm:ℝ)-
        2*Real.logb Z ((commonRadical C D).absNorm:ℝ)-
        Real.logb Z ((Ideal.span {activeConductor C D}).absNorm:ℝ):=by
  have hh:=actual_allowance_sum C D hC hD hCD Z hZ
  simpa only [allowance,active_span_swap C D] using hh

lemma allowance_root (Z C D P R b:ℝ)(hZ:1<Z)(hC:0<C)(hD:0<D)(hP:0<P)(hR:0<R)
    (hb:b≤Real.logb Z C+Real.logb Z D-2*Real.logb Z P-Real.logb Z R):
    Real.sqrt R/Real.sqrt (C*D)*Z^(b/2)≤1/P:=by
  have hz:0<Z:=zero_lt_one.trans hZ
  have hlz:0<Real.log Z:=Real.log_pos hZ
  have hb':b≤(Real.log C+Real.log D-2*Real.log P-Real.log R)/Real.log Z:=by
    convert hb using 1 ; simp only [Real.logb] ; ring
  have hh: b*Real.log Z≤Real.log C+Real.log D-2*Real.log P-Real.log R:=
    (le_div_iff₀ hlz).mp hb'
  apply (Real.log_le_log_iff (by positivity) (by positivity)).mp
  simp (disch := positivity) only [Real.log_mul,Real.log_div,Real.log_sqrt,
    Real.log_rpow,Real.log_one]
  nlinarith

lemma paired_reference_root (qL qR V C D Z bL bR EL ER:ℝ)
    (hqL:0<qL)(hqR:0<qR)(hV:0<V)(hC:0<C)(hD:0<D)(hZ:0<Z)
    (_hEL:0≤EL)(_hER:0≤ER):
    Real.sqrt ((qL*(V/C)^2*Z^bL*EL)*(qR*(V/D)^2*Z^bR*ER))=
      V^2/(C*D)*Real.sqrt (qL*qR)*Z^((bL+bR)/2)*Real.sqrt (EL*ER):=by
  have hbase:Real.sqrt ((qL*(V/C)^2*Z^bL)*(qR*(V/D)^2*Z^bR))=
      V^2/(C*D)*Real.sqrt (qL*qR)*Z^((bL+bR)/2):=by
    apply Real.log_injOn_pos
    · simp only [Set.mem_Ioi];positivity
    · simp only [Set.mem_Ioi];positivity
    · simp (disch := positivity) only [Real.log_sqrt,Real.log_mul,Real.log_div,
        Real.log_pow,Real.log_rpow]
      ring
  rw [show (qL*(V/C)^2*Z^bL*EL)*(qR*(V/D)^2*Z^bR*ER)=
    ((qL*(V/C)^2*Z^bL)*(qR*(V/D)^2*Z^bR))*(EL*ER) by ring,
    Real.sqrt_mul (by positivity),hbase]

theorem actual_fixed_reference_pair (C D:Ideal O)(hC:Supported C)(hD:Supported D)
    (hCD:CompletedGauss.primeSupport C=CompletedGauss.primeSupport D)
    (E:Finset (CommonIndex C D))(η:Character)(ξ₁ ξ₂:RayFourExpansion.RayCharacter)
    (F:FixedPair η C D hC E ξ₁ ξ₂)
    (K A₀ B₀ a T M Z EL ER:ℝ)(hK:0<K)(hA:0<A₀)(hB:0<B₀)
    (ha:0<a)(hT:0<T)(hZ:1<Z)(hEL:0≤EL)(hER:0≤ER)
    (hl:a*T≤(C.absNorm:ℝ)*Real.exp M*A₀)
    (hr:a*T≤(D.absNorm:ℝ)*Real.exp M*B₀):
    ‖scalar C D hC E K A₀ B₀‖/T*
      Real.sqrt (((F.left.modulus.absNorm:ℝ)*(T/(C.absNorm:ℝ))^2*Z^(allowance C D Z)*EL)*
        ((F.right.modulus.absNorm:ℝ)*(T/(D.absNorm:ℝ))^2*Z^(allowance D C Z)*ER))≤
      ‖inactiveWeight C D E‖*(Real.exp M/a)*fixedPresentationCost*K*(η.modulus.absNorm:ℝ)/
        (commonRadical C D).absNorm*Real.sqrt (EL*ER):=by
  have hF:0<fixedPresentationCost:=fixedPresentationCost_pos
  have hNC:0<(C.absNorm:ℝ):=norm_pos C hC.1
  have hND:0<(D.absNorm:ℝ):=norm_pos D hD.1
  have hNR:0<((Ideal.span {activeConductor C D}).absNorm:ℝ):=active_norm_pos C D
  have hP:0<((commonRadical C D).absNorm:ℝ):=norm_pos _ (commonRadical_ne_zero C D)
  have hqL:0<(F.left.modulus.absNorm:ℝ):=norm_pos _ F.left.modulus_ne_bot
  have hqR:0<(F.right.modulus.absNorm:ℝ):=norm_pos _ F.right.modulus_ne_bot
  have he:0<‖eisEmbedding (primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E)‖:=
    norm_pos_iff.mpr (eisEmbedding_ne_zero (supported_element_ne_zero _ (subsetGenerator_supported C D hC E)))
  have hrpos:0<‖eisEmbedding (activeConductor C D)‖:=
    norm_pos_iff.mpr (eisEmbedding_ne_zero (supported_element_ne_zero _ (activeConductor_supported C D hC)))
  have hs:=scalar_conductor_algebra _ _ K T _ _ _ (Real.exp M/a) fixedPresentationCost
    (η.modulus.absNorm:ℝ) (F.left.modulus.absNorm:ℝ) (F.right.modulus.absNorm:ℝ)
    (norm_nonneg _) (norm_nonneg _) hK.le hT (mul_pos hNC hND)
    (sq_pos_of_pos he) hrpos (by positivity) fixedPresentationCost_pos.le (Nat.cast_nonneg _)
    hqL.le hqR.le (weighted_scalar_volume C D hC E K A₀ B₀ a T M hK hA hB ha hT hl hr)
    F.conductor_caps.1 F.conductor_caps.2
  have haR:=allowance_root Z (C.absNorm:ℝ) (D.absNorm:ℝ)
    ((commonRadical C D).absNorm:ℝ) ((Ideal.span {activeConductor C D}).absNorm:ℝ)
    (allowance C D Z+allowance D C Z) hZ hNC hND hP hNR
    (allowance_pair C D hC hD hCD Z hZ)
  rw [←eisEmbedding_norm_sq_eq_absNorm_span,Real.sqrt_sq (norm_nonneg _)] at haR
  rw [paired_reference_root _ _ T _ _ Z _ _ EL ER hqL hqR hT hNC hND
    (zero_lt_one.trans hZ) hEL hER]
  calc
    _=(‖scalar C D hC E K A₀ B₀‖*T/((C.absNorm:ℝ)*D.absNorm)*
        Real.sqrt ((F.left.modulus.absNorm:ℝ)*F.right.modulus.absNorm))*
        (Z^((allowance C D Z+allowance D C Z)/2)*Real.sqrt (EL*ER)):=by
      field_simp
    _≤(‖inactiveWeight C D E‖*(Real.exp M/a)*fixedPresentationCost*K*(η.modulus.absNorm:ℝ)*
        (‖eisEmbedding (activeConductor C D)‖/Real.sqrt ((C.absNorm:ℝ)*D.absNorm)))*
        (Z^((allowance C D Z+allowance D C Z)/2)*Real.sqrt (EL*ER)):=
      mul_le_mul_of_nonneg_right hs (by positivity)
    _=(‖inactiveWeight C D E‖*(Real.exp M/a)*fixedPresentationCost*K*(η.modulus.absNorm:ℝ))*
        ((‖eisEmbedding (activeConductor C D)‖/Real.sqrt ((C.absNorm:ℝ)*D.absNorm))*
          Z^((allowance C D Z+allowance D C Z)/2))*Real.sqrt (EL*ER):=by ring
    _≤(‖inactiveWeight C D E‖*(Real.exp M/a)*fixedPresentationCost*K*(η.modulus.absNorm:ℝ))*
        (1/(commonRadical C D).absNorm)*Real.sqrt (EL*ER):=by
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left haR (by positivity))
        (Real.sqrt_nonneg _)
    _=_:=by ring

open CenteredMomentFirstPhysicalSourceSupport CenteredMomentCommonRadialData
open CenteredMomentOriginalCommonHarmonic CenteredMomentExceptionalAmplitudePair
open HeckeFamily CenteredMomentSupportedCorrelation

theorem original_fixed_reference_pair {ι:Type*}[Fintype ι][DecidableEq ι]
    (s:Input ι)(R seed:Ideal O)(a₁ a₂:ℝ)(ha₁:0<a₁)(ha₂:0<a₂)
    (hs₁:∀x,s.W₁ x≠0→a₁≤x)(hs₂:∀x,s.W₂ x≠0→a₂≤x)
    (m A:O)(t:ℝ)(S:Finset (Ideal O))(C D:Ideal O)(hC:Supported C)(hD:Supported D)
    (hCD:CompletedGauss.primeSupport C=CompletedGauss.primeSupport D)
    (E:Finset (CommonIndex C D))(ξ₁ ξ₂:RayFourExpansion.RayCharacter)
    (F:FixedPair s.η C D hC E ξ₁ ξ₂)
    (rows:Finset O)(W:𝓢(ℝ,ℂ))(U:Fin 4→ℝ→ℂ)
    (K K₀ H₀ A₀ B₀ M Z EL ER:ℝ)(hK:0<K)(hA:0<A₀)(hB:0<B₀)(hZ:1<Z)
    (hEL:0≤EL)(hER:0≤ER)(hwin:∀i y,U i y≠0→|y|≤M)
    (hn:block s.η m A t S (CenteredMomentOriginalCommonHarmonic.coefficient s R seed)
      C D hC hD E rows W U K K₀ H₀ A₀ B₀≠0):
    let V:=volume s.toData;
    ‖scalar C D hC E K A₀ B₀‖/V*
      Real.sqrt (((F.left.modulus.absNorm:ℝ)*(V/(C.absNorm:ℝ))^2*Z^(allowance C D Z)*EL)*
        ((F.right.modulus.absNorm:ℝ)*(V/(D.absNorm:ℝ))^2*Z^(allowance D C Z)*ER))≤
      ‖inactiveWeight C D E‖*(Real.exp M/((∏i,s.lo i)*a₁*a₂))*fixedPresentationCost*K*
        (s.η.modulus.absNorm:ℝ)/(commonRadical C D).absNorm*Real.sqrt (EL*ER):=by
  have ha:0<(∏i,s.lo i)*a₁*a₂:=
    mul_pos (mul_pos (Finset.prod_pos (fun i _=>s.lo_pos i)) ha₁) ha₂
  obtain ⟨hl,hr⟩:=block_reference_lower s.η m A t S
    (CenteredMomentOriginalCommonHarmonic.coefficient s R seed) C D hC hD E rows W U
    K K₀ H₀ A₀ B₀ ((∏i,s.lo i)*a₁*a₂) (volume s.toData) M hA hB
    (fun I hi=>original_column_lower s R seed I a₁ a₂ ha₁.le ha₂.le hs₁ hs₂ hi) hwin hn
  exact actual_fixed_reference_pair C D hC hD hCD E s.η ξ₁ ξ₂ F
    K A₀ B₀ _ _ M Z EL ER hK hA hB ha (volume_pos s.toData) hZ hEL hER hl hr

end SevenEighths.CenteredMomentFirstMixedRoot

end

end OAI
