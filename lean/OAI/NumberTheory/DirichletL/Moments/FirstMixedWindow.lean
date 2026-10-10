import OAI.NumberTheory.DirichletL.Moments.FirstMixedRoot
import OAI.NumberTheory.DirichletL.Moments.FirstWindowBudgets

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentFirstMixedWindow
open CenteredMomentFirstMixedRoot CenteredMomentFirstMixedAllowance CenteredMomentSecondWindowBudget
open CenteredMomentFirstPhysicalSource CenteredMomentFirstCanonicalFamily
open CenteredMomentFirstPhysicalSourceSupport CenteredMomentCommonRadialData
open CenteredMomentOriginalCommonHarmonic CenteredMomentExceptionalAmplitudePair
open CenteredMomentCanonicalFirst CenteredMomentRankinRadical CenteredMomentCompleteCommon
open HeckeFamily CanonicalQuadraticSieve CenteredMomentSupportedCorrelation
open CenteredMomentFirstScale CenteredMomentFirstNonexceptionalPrefactor
local notation "O"=>HeckeFamily.O

theorem original_four_budget_reference {ι:Type*}[Fintype ι][DecidableEq ι]
    (s:Input ι)(R seed:Ideal O)(a₁ a₂:ℝ)(ha₁:0<a₁)(ha₂:0<a₂)
    (hs₁:∀x,s.W₁ x≠0→a₁≤x)(hs₂:∀x,s.W₂ x≠0→a₂≤x)
    (m A:O)(t:ℝ)(S:Finset (Ideal O))(C D:Ideal O)(hC:Supported C)(hD:Supported D)
    (hCD:CompletedGauss.primeSupport C=CompletedGauss.primeSupport D)
    (E:Finset (CommonIndex C D))(ξ₁ ξ₂:RayFourExpansion.RayCharacter)
    (F:FixedPair s.η C D hC E ξ₁ ξ₂)
    (rows:Finset O)(W:𝓢(ℝ,ℂ))(U:Fin 4→ℝ→ℂ)
    (K K₀ H₀ A₀ B₀ M Z:ℝ)(EL ER:Fin 4→ℝ)(JL JR:ℕ)(height:ℝ)(hK:0<K)(hA:0<A₀)(hB:0<B₀)(hZ:1<Z)
    (hEL:∀i,0≤EL i)(hER:∀i,0≤ER i)(hwin:∀i y,U i y≠0→|y|≤M)
    (hn:block s.η m A t S (CenteredMomentOriginalCommonHarmonic.coefficient s R seed)
      C D hC hD E rows W U K K₀ H₀ A₀ B₀≠0):
    let V:=volume s.toData;
    ‖scalar C D hC E K A₀ B₀‖/V*
      (∑i:Fin 4,∑j:Fin 4,
        windowBudget JL height ((F.left.modulus.absNorm:ℝ)*(V/(C.absNorm:ℝ))^2*Z^(allowance C D Z)*EL i)*
        windowBudget JR height ((F.right.modulus.absNorm:ℝ)*(V/(D.absNorm:ℝ))^2*Z^(allowance D C Z)*ER j))≤
      (‖inactiveWeight C D E‖*(Real.exp M/((∏i,s.lo i)*a₁*a₂))*fixedPresentationCost*K*
        (s.η.modulus.absNorm:ℝ)/(commonRadical C D).absNorm)*
        (∑i:Fin 4,∑j:Fin 4,windowBudget JL height (EL i)*windowBudget JR height (ER j)) :=by
  dsimp only
  rw [Finset.mul_sum,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  rw [Finset.mul_sum,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j hj
  have hh:=original_fixed_reference_pair s R seed a₁ a₂ ha₁ ha₂ hs₁ hs₂
    m A t S C D hC hD hCD E ξ₁ ξ₂ F rows W U K K₀ H₀ A₀ B₀ M Z
    (EL i) (ER j) hK hA hB hZ (hEL i) (hER j) hwin hn
  have hqL:0<(F.left.modulus.absNorm:ℝ):=norm_pos _ F.left.modulus_ne_bot
  have hqR:0<(F.right.modulus.absNorm:ℝ):=norm_pos _ F.right.modulus_ne_bot
  have hCpos:=norm_pos C hC.1
  have hDpos:=norm_pos D hD.1
  have hV:=volume_pos s.toData
  have hz:0<Z:=zero_lt_one.trans hZ
  have hei:=hEL i
  have herj:=hER j
  have hh':=mul_le_mul_of_nonneg_right hh
    (mul_nonneg (mul_nonneg (pow_nonneg (heightEnvelope_pos height).le JL)
      (profileMoment_nonneg JL)) (mul_nonneg (pow_nonneg (heightEnvelope_pos height).le JR)
      (profileMoment_nonneg JR)))
  simp only [Real.sqrt_mul (by positivity : 0≤
    (F.left.modulus.absNorm:ℝ)*(volume s.toData/(C.absNorm:ℝ))^2*Z^(allowance C D Z)*EL i),
    Real.sqrt_mul (hEL i)] at hh'
  unfold windowBudget
  nlinarith only [hh']

end SevenEighths.CenteredMomentFirstMixedWindow

end

end OAI
