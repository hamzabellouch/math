import OAI.NumberTheory.DirichletL.Moments.FirstPhysicalSourceSupport
import OAI.NumberTheory.DirichletL.Moments.FirstActiveRadicalBudget

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentFirstNonexceptionalPrefactor
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge HeckeFamily CanonicalQuadraticSieve
open CenteredMomentCanonicalFirst CenteredMomentFirstCanonicalFamily
open CenteredMomentFirstPhysicalSource CenteredMomentFirstPhysicalSourceSupport
open CenteredMomentCommonRadialData CenteredMomentOriginalCommonHarmonic
open CenteredMomentFirstActiveRadicalBudget CenteredMomentRankinRadical
open CenteredMomentExceptionalAmplitudePair
open CenteredMomentSupportedCorrelation
local notation "O"=>ActualEisensteinCubic.O

lemma pair_conductor_root (q₁ q₂ B:ℝ)(_h₁:0≤q₁)(h₂:0≤q₂)
    (hB:0≤B)(hb₁:q₁≤B)(hb₂:q₂≤B):Real.sqrt (q₁*q₂)≤B := by
  have hh:=mul_le_mul hb₁ hb₂ h₂ hB
  have hs:=Real.sqrt_le_sqrt hh
  simpa only [←pow_two,Real.sqrt_sq hB] using hs

lemma scalar_conductor_algebra (s μ K T N E r C F q q₁ q₂:ℝ)
    (_hs:0≤s)(hμ:0≤μ)(hK:0≤K)(_hT:0<T)(hN:0<N)(hE:0<E)(hr:0<r)
    (hC:0≤C)(hF:0≤F)(hq:0≤q)(h₁:0≤q₁)(h₂:0≤q₂)
    (hscalar:s*T≤μ*C*K*Real.sqrt N/(E*r))
    (hc₁:q₁≤F*q*E*r^2)(hc₂:q₂≤F*q*E*r^2):
    s*T/N*Real.sqrt (q₁*q₂)≤μ*C*F*K*q*(r/Real.sqrt N) := by
  have hroot:=pair_conductor_root q₁ q₂ (F*q*E*r^2) h₁ h₂ (by positivity) hc₁ hc₂
  calc
    _≤(μ*C*K*Real.sqrt N/(E*r))/N*(F*q*E*r^2):=
      mul_le_mul (div_le_div_of_nonneg_right hscalar hN.le) hroot
        (Real.sqrt_nonneg _) (by positivity)
    _=μ*C*F*K*q*(r/Real.sqrt N):=by
      have hn:Real.sqrt N≠0:=ne_of_gt (Real.sqrt_pos.mpr hN)
      have hn2:=Real.sq_sqrt hN.le
      field_simp
      linear_combination μ*C*K*F*q*hn2

theorem weighted_scalar_volume (C D:Ideal O)(hC:Supported C)(E:Finset (CommonIndex C D))
    (K A₀ B₀ a T M:ℝ)(hK:0<K)(hA:0<A₀)(hB:0<B₀)(ha:0<a)(hT:0<T)
    (hl:a*T≤(C.absNorm:ℝ)*Real.exp M*A₀)
    (hr:a*T≤(D.absNorm:ℝ)*Real.exp M*B₀):
    ‖scalar C D hC E K A₀ B₀‖*T≤
      ‖inactiveWeight C D E‖*(Real.exp M/a)*K*Real.sqrt ((C.absNorm:ℝ)*D.absNorm)/
        (‖eisEmbedding (primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E)‖^2*
          ‖eisEmbedding (activeConductor C D)‖) := by
  have hs:=reference_sqrt_lower (C.absNorm:ℝ) (D.absNorm:ℝ) A₀ B₀ a T M
    (Nat.cast_nonneg _) (Nat.cast_nonneg _) hA.le hB.le ha.le hT.le hl hr
  have hden:0<Real.sqrt A₀*Real.sqrt B₀:=mul_pos (Real.sqrt_pos.2 hA) (Real.sqrt_pos.2 hB)
  have hratio:T/(Real.sqrt A₀*Real.sqrt B₀)≤Real.exp M*Real.sqrt ((C.absNorm:ℝ)*D.absNorm)/a:=by
    apply (div_le_div_iff₀ hden ha).mpr
    nlinarith [hs]
  rw [scalar_norm C D hC E K A₀ B₀ hK hA hB]
  calc
    _=(‖inactiveWeight C D E‖*K/
        (‖eisEmbedding (primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E)‖^2*
          ‖eisEmbedding (activeConductor C D)‖))*(T/(Real.sqrt A₀*Real.sqrt B₀)):=by ring
    _≤(‖inactiveWeight C D E‖*K/
        (‖eisEmbedding (primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E)‖^2*
          ‖eisEmbedding (activeConductor C D)‖))*(Real.exp M*Real.sqrt ((C.absNorm:ℝ)*D.absNorm)/a):=
      mul_le_mul_of_nonneg_left hratio (by positivity)
    _=_:=by ring

theorem actual_scalar_conductors (C D:Ideal O)(hC:Supported C)(hD:Supported D)
    (E:Finset (CommonIndex C D))(η τ₁ τ₂:Character)
    (K A₀ B₀ a T M F:ℝ)(hK:0<K)(hA:0<A₀)(hB:0<B₀)(ha:0<a)(hT:0<T)(hF:0≤F)
    (hl:a*T≤(C.absNorm:ℝ)*Real.exp M*A₀)
    (hr:a*T≤(D.absNorm:ℝ)*Real.exp M*B₀)
    (hc₁:(τ₁.modulus.absNorm:ℝ)≤F*(η.modulus.absNorm:ℝ)*
      ‖eisEmbedding (primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E)‖^2*
      ‖eisEmbedding (activeConductor C D)‖^2)
    (hc₂:(τ₂.modulus.absNorm:ℝ)≤F*(η.modulus.absNorm:ℝ)*
      ‖eisEmbedding (primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E)‖^2*
      ‖eisEmbedding (activeConductor C D)‖^2):
    ‖scalar C D hC E K A₀ B₀‖*T/((C.absNorm:ℝ)*D.absNorm)*
      Real.sqrt ((τ₁.modulus.absNorm:ℝ)*τ₂.modulus.absNorm)≤
      ‖inactiveWeight C D E‖*(Real.exp M/a)*F*K*(η.modulus.absNorm:ℝ)/
        (commonRadical C D).absNorm := by
  have hN:0<(C.absNorm:ℝ)*D.absNorm:=mul_pos
    (by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hC.1))
    (by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hD.1))
  have he:0<‖eisEmbedding (primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E)‖:=
    norm_pos_iff.mpr (eisEmbedding_ne_zero (supported_element_ne_zero _ (subsetGenerator_supported C D hC E)))
  have hrpos:0<‖eisEmbedding (activeConductor C D)‖:=
    norm_pos_iff.mpr (eisEmbedding_ne_zero (supported_element_ne_zero _ (activeConductor_supported C D hC)))
  have hh:=scalar_conductor_algebra _ _ K T _ _ _ (Real.exp M/a) F (η.modulus.absNorm:ℝ)
    (τ₁.modulus.absNorm:ℝ) (τ₂.modulus.absNorm:ℝ) (norm_nonneg _) (norm_nonneg _)
    hK.le hT hN (sq_pos_of_pos he) hrpos (by positivity) hF (Nat.cast_nonneg _)
    (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    (weighted_scalar_volume C D hC E K A₀ B₀ a T M hK hA hB ha hT hl hr) hc₁ hc₂
  have hroot:=active_root_le_radical C D hC.1 hD.1
  rw [←eisEmbedding_norm_sq_eq_absNorm_span,Real.sqrt_sq (norm_nonneg _)] at hroot
  exact hh.trans ((mul_le_mul_of_nonneg_left hroot (by positivity)).trans_eq (by ring))

theorem original_scalar_conductors {ι:Type*}[Fintype ι][DecidableEq ι]
    (s:Input ι)(R seed:Ideal O)(a₁ a₂:ℝ)(ha₁:0<a₁)(ha₂:0<a₂)
    (hs₁:∀x,s.W₁ x≠0→a₁≤x)(hs₂:∀x,s.W₂ x≠0→a₂≤x)
    (m A:O)(t:ℝ)(S:Finset (Ideal O))(C D:Ideal O)(hC:Supported C)(hD:Supported D)
    (E:Finset (CommonIndex C D))(rows:Finset O)(W:𝓢(ℝ,ℂ))(V:Fin 4→ℝ→ℂ)
    (K K₀ H₀ A₀ B₀ M F:ℝ)(τ₁ τ₂:Character)
    (hK:0<K)(hA:0<A₀)(hB:0<B₀)(hF:0≤F)(hwin:∀i y,V i y≠0→|y|≤M)
    (hn:block s.η m A t S (CenteredMomentOriginalCommonHarmonic.coefficient s R seed)
      C D hC hD E rows W V K K₀ H₀ A₀ B₀≠0)
    (hc₁:(τ₁.modulus.absNorm:ℝ)≤F*(s.η.modulus.absNorm:ℝ)*
      ‖eisEmbedding (primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E)‖^2*
      ‖eisEmbedding (activeConductor C D)‖^2)
    (hc₂:(τ₂.modulus.absNorm:ℝ)≤F*(s.η.modulus.absNorm:ℝ)*
      ‖eisEmbedding (primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E)‖^2*
      ‖eisEmbedding (activeConductor C D)‖^2):
    ‖scalar C D hC E K A₀ B₀‖*volume s.toData/((C.absNorm:ℝ)*D.absNorm)*
      Real.sqrt ((τ₁.modulus.absNorm:ℝ)*τ₂.modulus.absNorm)≤
      ‖inactiveWeight C D E‖*(Real.exp M/((∏i,s.lo i)*a₁*a₂))*F*K*(s.η.modulus.absNorm:ℝ)/
        (commonRadical C D).absNorm := by
  have ha:0<(∏i,s.lo i)*a₁*a₂:=
    mul_pos (mul_pos (Finset.prod_pos (fun i _=>s.lo_pos i)) ha₁) ha₂
  obtain ⟨hl,hr⟩:=block_reference_lower s.η m A t S
    (CenteredMomentOriginalCommonHarmonic.coefficient s R seed) C D hC hD E rows W V
    K K₀ H₀ A₀ B₀ ((∏i,s.lo i)*a₁*a₂) (volume s.toData) M hA hB
    (fun I hi=>original_column_lower s R seed I a₁ a₂ ha₁.le ha₂.le hs₁ hs₂ hi) hwin hn
  exact actual_scalar_conductors C D hC hD E s.η τ₁ τ₂ K A₀ B₀ _ _ M F hK hA hB
    ha (volume_pos s.toData) hF hl hr hc₁ hc₂

end SevenEighths.CenteredMomentFirstNonexceptionalPrefactor

end

end OAI
