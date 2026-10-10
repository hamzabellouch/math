import OAI.NumberTheory.DirichletL.Moments.FirstExceptionalPrefactor
import OAI.NumberTheory.DirichletL.Moments.FirstNonexceptionalPrefactor

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentFirstExceptionalPrefactor
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge CanonicalQuadraticSieve
open CenteredMomentCanonicalFirst CenteredMomentCompleteCommon CenteredMomentRankinRadical
open CenteredMomentFirstCanonicalFamily CenteredMomentFirstPhysicalSource
open CenteredMomentFirstNonexceptionalPrefactor CenteredMomentFirstScale IdealMobiusDivisorSum
local notation "O"=>ActualEisensteinCubic.O

lemma commonPart_of_equal_support (C D:Ideal O)(hC:C≠0)
    (hCD:primeSupport C=primeSupport D):commonPart C D=C := by
  have he:commonPart C D=commonPart C C:=by
    simp only [commonPart,commonSupport,←hCD]
  exact he.trans (commonPart_self C hC)

lemma nominal_equal_support (C D E:Ideal O)(hC:C≠0)(hD:D≠0)
    (hCD:primeSupport C=primeSupport D)(K V:ℝ):
    firstNominalScale C D E K V=
      (E.absNorm:ℝ)*(Ideal.span {activeConductor C D}).absNorm*V^2/
        (K*(C.absNorm:ℝ)*D.absNorm) := by
  rw [firstNominalScale,commonPart_of_equal_support C D hC hCD,
    commonPart_of_equal_support D C hD hCD.symm]

theorem actual_scalar_exceptional (C D:Ideal O)(hC:Supported C)(hD:Supported D)
    (hCD:primeSupport C=primeSupport D)(E:Finset (CommonIndex C D))
    (K A₀ B₀ a V M Z j g:ℝ)(hK:0<K)(hA:0<A₀)(hB:0<B₀)
    (ha:0<a)(hV:0<V)(hZ:1<Z)
    (hl:a*V≤(C.absNorm:ℝ)*Real.exp M*A₀)
    (hr:a*V≤(D.absNorm:ℝ)*Real.exp M*B₀):
    let e:=primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E;
    let NE:ℝ:=(Ideal.span {e}).absNorm;
    let NR:ℝ:=(Ideal.span {activeConductor C D}).absNorm;
    ‖scalar C D hC E K A₀ B₀‖/V*
      (V/(C.absNorm:ℝ))^((2:ℝ)/3)*(V/(D.absNorm:ℝ))^((2:ℝ)/3)*
        (Z^(j+g))^((5:ℝ)/6) ≤
    ‖inactiveWeight C D E‖*(Real.exp M/a)*
      (V*K^((1:ℝ)/6)*NR^((1:ℝ)/3)/(NE^((1:ℝ)/6)*(C.absNorm:ℝ)*D.absNorm)*
        Z^(5*(j-Real.logb Z (firstNominalScale C D (Ideal.span {e}) K V)+g)/6)) := by
  dsimp only
  have hNE:=norm_pos _ (subsetGenerator_supported C D hC E).1
  have hNR:=active_norm_pos C D
  have hNC:=norm_pos C hC.1
  have hND:=norm_pos D hD.1
  have hroot:Real.sqrt ((Ideal.span {activeConductor C D}).absNorm:ℝ)=
      ‖eisEmbedding (activeConductor C D)‖:=by
    rw [←eisEmbedding_norm_sq_eq_absNorm_span,Real.sqrt_sq (norm_nonneg _)]
  have hs:=weighted_scalar_volume C D hC E K A₀ B₀ a V M hK hA hB ha hV hl hr
  rw [eisEmbedding_norm_sq_eq_absNorm_span,←hroot] at hs
  have hh:=scalar_exceptional_bound _ _ (Real.exp M/a) K V _ _ _ _ Z j g
    hK hV hNE hNR hNC hND hZ hs
  rw [nominal_equal_support C D _ hC.1 hD.1 hCD K V]
  exact hh

open CenteredMomentFirstPhysicalSourceSupport CenteredMomentCommonRadialData
open CenteredMomentOriginalCommonHarmonic CenteredMomentExceptionalAmplitudePair
open HeckeFamily CenteredMomentSupportedCorrelation

theorem original_scalar_exceptional {ι:Type*}[Fintype ι][DecidableEq ι]
    (s:Input ι)(R seed:Ideal O)(a₁ a₂:ℝ)(ha₁:0<a₁)(ha₂:0<a₂)
    (hs₁:∀x,s.W₁ x≠0→a₁≤x)(hs₂:∀x,s.W₂ x≠0→a₂≤x)
    (m A:O)(t:ℝ)(S:Finset (Ideal O))(C D:Ideal O)(hC:Supported C)(hD:Supported D)
    (hCD:primeSupport C=primeSupport D)(E:Finset (CommonIndex C D))
    (rows:Finset O)(W:𝓢(ℝ,ℂ))(U:Fin 4→ℝ→ℂ)
    (K K₀ H₀ A₀ B₀ M Z j g:ℝ)(hK:0<K)(hA:0<A₀)(hB:0<B₀)(hZ:1<Z)
    (hwin:∀i y,U i y≠0→|y|≤M)
    (hn:block s.η m A t S (CenteredMomentOriginalCommonHarmonic.coefficient s R seed)
      C D hC hD E rows W U K K₀ H₀ A₀ B₀≠0):
    let V:=volume s.toData;
    let e:=primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E;
    let NE:ℝ:=(Ideal.span {e}).absNorm;
    let NR:ℝ:=(Ideal.span {activeConductor C D}).absNorm;
    ‖scalar C D hC E K A₀ B₀‖/V*
      (V/(C.absNorm:ℝ))^((2:ℝ)/3)*(V/(D.absNorm:ℝ))^((2:ℝ)/3)*
        (Z^(j+g))^((5:ℝ)/6) ≤
    ‖inactiveWeight C D E‖*(Real.exp M/((∏i,s.lo i)*a₁*a₂))*
      (V*K^((1:ℝ)/6)*NR^((1:ℝ)/3)/(NE^((1:ℝ)/6)*(C.absNorm:ℝ)*D.absNorm)*
        Z^(5*(j-Real.logb Z (firstNominalScale C D (Ideal.span {e}) K V)+g)/6)) := by
  have ha:0<(∏i,s.lo i)*a₁*a₂:=
    mul_pos (mul_pos (Finset.prod_pos (fun i _=>s.lo_pos i)) ha₁) ha₂
  obtain ⟨hl,hr⟩:=block_reference_lower s.η m A t S
    (CenteredMomentOriginalCommonHarmonic.coefficient s R seed) C D hC hD E rows W U
    K K₀ H₀ A₀ B₀ ((∏i,s.lo i)*a₁*a₂) (volume s.toData) M hA hB
    (fun I hi=>original_column_lower s R seed I a₁ a₂ ha₁.le ha₂.le hs₁ hs₂ hi) hwin hn
  exact actual_scalar_exceptional C D hC hD hCD E K A₀ B₀ _ _ M Z j g
    hK hA hB ha (volume_pos s.toData) hZ hl hr

end SevenEighths.CenteredMomentFirstExceptionalPrefactor

end

end OAI
