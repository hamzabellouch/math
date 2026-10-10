import OAI.NumberTheory.DirichletL.Moments.FirstSecondCapacityDefect
import OAI.NumberTheory.DirichletL.Moments.FirstPhysicalLedger
import OAI.NumberTheory.DirichletL.Moments.SecondCanonical
import OAI.NumberTheory.DirichletL.Moments.FinalStageLedger

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentFirstSecondPaidLedger
open CenteredMomentFirstSecondCapacityLedger CenteredMomentFirstAmplificationChoice
open CenteredMomentFirstPhysicalLedger CenteredMomentFirstScale
open CenteredMomentSectorLocalization CenteredMomentDescentLedger
open CenteredMomentSecondCanonical CenteredMomentSecondLedger CenteredMomentCanonicalFirst
open CenteredMomentCompleteCommon CenteredMomentSupportedCorrelation
open CenteredMomentSupport CenteredMomentRankinRadical
open CenteredMomentFinalStageLedger CanonicalQuadraticSieve
local notation "O"=>ActualEisensteinCubic.O

theorem repaired_error_capacity_shift (A m q c d R E j σ δ Z g₂ t₂ c₂ V:ℝ)
    (p:O)(k:ℕ)(hc:0≤c)(hσ:0≤σ)(hδ:0≤δ)
    (hD: -δ≤d+(2*A-c-d+R+E-m)-j)(hcommon:g₂-t₂≤c₂)
    (hk:k=1 ∨ k=6 ∨ k=7)(hl:σ/6≤Real.logb Z (CenteredMomentSectorLocalization.normValue p)):
    let D₀:=d+(2*A-c-d+R+E-m)-j;
    let w:=errorRemoval p Z k;
    let wo:=errorMoving p Z k;
    let g:=errorGain D₀ c σ Z p k;
    let m':=2*(A-c-w)-j-g-g₂-V;
    let q':=q+R+E+wo+t₂+V;
    (A-c-w-c₂)-(m'+q')≤A-(m+q)+6*w+δ := by
  have hi:=nominal_capacity_shift_identity A m q c d R E j
    (errorGain (d+(2*A-c-d+R+E-m)-j) c σ Z p k)
    (errorRemoval p Z k) (errorMoving p Z k) g₂ t₂ c₂ V
  have hg:=error_capacity_gain _ c σ δ Z p k hc hσ hδ hD hk hl
  dsimp only at hi ⊢
  linarith

lemma paired_first_saving (c D₀ q B wL wR woL woR gL gR ellL ellR:ℝ):
    (firstSaving c D₀ wL q woL B gL ellL+
      firstSaving c D₀ wR q woR B gR ellR)/2=
      firstSaving c D₀ ((wL+wR)/2) q ((woL+woR)/2) B
        ((gL+gR)/2) ((ellL+ellR)/2) := by
  unfold firstSaving
  ring

theorem actual_stage_saving
    (I J E:Ideal O)(hI:Supported I)(hJ:Supported J)(hE:E≠0)
    (C D:Ideal O)(hC:Supported C)(hD:Supported D)
    (hCD:CompletedGauss.primeSupport C=CompletedGauss.primeSupport D)
    (u:O)(hne:idealCorrelation C D hC hD (commonFrequencyGenerator C D*u)≠0)
    (A M Z H X Tsec Csec ξ q w wo ell σ branch:ℝ)
    (hZ:1<Z)(hH:0<H)(hX:0<X)(hCsec:1≤Csec)(hξ:0≤ξ)
    (hsec:Tsec≤Csec*firstNominalScale I J E H X)
    (n:ℤ)(hn:Retained (frequencyRadius Tsec Z ξ) n)
    (hq:0≤q)(hw:0≤w)(hwo:0≤wo)(hell:0≤ell)(hσ:0≤σ)
    (hbranch:branch≤2)(hwσ:w≤7*σ/3):
    let c:=Real.logb Z ((commonPart I J).absNorm:ℝ);
    let d:=Real.logb Z ((commonPart J I).absNorm:ℝ);
    let p:=Real.logb Z ((commonRadical I J).absNorm:ℝ);
    let R:=Real.logb Z ((Ideal.span {activeConductor I J}).absNorm:ℝ);
    let e:=Real.logb Z (E.absNorm:ℝ);
    let D₀:=d+Real.logb Z (firstNominalScale I J E H X)-Real.logb Z (dyadicScale n);
    let F₁:=firstSaving c D₀ w (q+R+e) wo (c+d-2*p-R)
      (max (D₀-c-2*w+wo) 0+branch*σ) ell;
    let F₂:=secondSaving (commonPrime C D) (leftExponent C D) (rightExponent C D) u Z;
    let v:=c+w+min (Real.logb Z (C.absNorm:ℝ)) (Real.logb Z (D.absNorm:ℝ));
    A-5*M/6-F₁-F₂-max (M/4-v) 0≤
      max (A-M) 0+3*σ+5*frequencyLoss Z Csec ξ/6 := by
  have hfirst:=actual_first_saving I J E hI hJ hE Z H X Tsec Csec ξ q w wo ell σ branch
    hZ hH hX hCsec hξ hsec n hn hq hw hwo hell hσ hbranch hwσ
  have hsecond:=actual_ideal_secondSaving_lower C D hC hD hCD u Z hZ hne
  have hm₁:=min_le_left (Real.logb Z (C.absNorm:ℝ)) (Real.logb Z (D.absNorm:ℝ))
  have hm₂:=min_le_right (Real.logb Z (C.absNorm:ℝ)) (Real.logb Z (D.absNorm:ℝ))
  have hf:=final_exponent A M
    (Real.logb Z ((commonPart I J).absNorm:ℝ)+w+
      min (Real.logb Z (C.absNorm:ℝ)) (Real.logb Z (D.absNorm:ℝ)))
    (3*σ+5*frequencyLoss Z Csec ξ/6) 0
  dsimp only at hfirst ⊢
  linarith

end SevenEighths.CenteredMomentFirstSecondPaidLedger

end

end OAI
