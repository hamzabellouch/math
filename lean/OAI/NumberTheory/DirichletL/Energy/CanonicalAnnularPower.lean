import OAI.NumberTheory.DirichletL.Energy.CanonicalAmplifiedUniform
import OAI.NumberTheory.DirichletL.Energy.AmplifierFamilyAdmission
import OAI.NumberTheory.DirichletL.Energy.FirstLiveAdmission
import OAI.NumberTheory.DirichletL.Energy.FirstAnnularAdmission
import OAI.NumberTheory.DirichletL.Energy.FirstRawScaleAdmission
import OAI.NumberTheory.DirichletL.Moments.FirstAmplifiedPowerBudget
import OAI.NumberTheory.DirichletL.Energy.CanonicalMainSubsets
import OAI.NumberTheory.DirichletL.Energy.CanonicalErrorSubsets
import OAI.NumberTheory.DirichletL.Energy.CanonicalMainHomogeneous
import OAI.NumberTheory.DirichletL.Energy.CanonicalMainSeparatedPower
import OAI.NumberTheory.DirichletL.Energy.FirstGaussianProfileWeights
import OAI.NumberTheory.DirichletL.Energy.CanonicalMainSeparated
import OAI.NumberTheory.DirichletL.Energy.FirstGaussianCoefficients
import OAI.NumberTheory.DirichletL.Energy.OriginalProfileControl
import OAI.NumberTheory.DirichletL.Energy.AmplifiedChildWidth
import OAI.NumberTheory.DirichletL.Energy.CanonicalMainUniform
import OAI.NumberTheory.DirichletL.Moments.FirstSeededGaussianPower
import OAI.NumberTheory.DirichletL.Moments.FirstSecondInputGates
import OAI.NumberTheory.DirichletL.Moments.SecondInputCapacitySource
import OAI.NumberTheory.DirichletL.Energy.CanonicalMainPaid
import OAI.NumberTheory.DirichletL.Energy.ChildEnvelopeFitting
import OAI.NumberTheory.DirichletL.Moments.FirstAmplifiedPaidReserve
import OAI.NumberTheory.DirichletL.Energy.CanonicalUniformReference
import OAI.NumberTheory.DirichletL.Moments.FirstAmplifiedPaidAdmission
import OAI.NumberTheory.DirichletL.Energy.AmplifiedRayDictionary

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentEnergyCanonicalAnnularPower
open HeckeFamily ConcreteTraceCRT
open CenteredMomentEnergyAllocatedChildren CenteredMomentAllocatedNaturalSource
open CenteredMomentAllocatedNaturalRadial CenteredMomentOriginalRadialComparison
open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw CenteredMomentRetainedProfile
open CenteredMomentRadialEligibleEnergy
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
local instance {ι:Type*} : DecidableEq (ι⊕Fin 2) := Classical.decEq _

open CenteredMomentEnergyCanonicalLiveBound CenteredMomentEnergyCanonicalLiveCapacity
open CenteredMomentEnergyCanonicalPaidSource CenteredMomentEnergyCanonicalCommonPaid
open CenteredMomentEnergyCanonicalReferencePaid CenteredMomentEnergyBandSubtypeTransport
open CenteredMomentFirstAmplifiedCapacityCommon (ratioPenalty)
open CenteredMomentEnergyAllocatedClipped CenteredMomentEnergyAllocatedHomogeneous
open CenteredMomentEnergyChildState CenteredMomentSecondNonexceptionalChosenBlock
open HeckeFamily CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentEnergyAllocatedPaid CenteredMomentEnergyAllocatedProfiles
open CenteredMomentEnergyAllocatedChildren CenteredMomentEnergyAllocatedZero
open CenteredMomentInductionEnergy CenteredMomentFiniteProfileExceptional
open CenteredMomentNaturalFixedRaySource CenteredMomentCommonRadialData
open CenteredMomentCommonHeightEnvelope CenteredMomentCommonAllocationSum
open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentAllocatedNaturalSource CenteredMomentRetainedProfile
open CenteredMomentAllocatedRayDictionary QuadraticInitialBound

open CenteredMomentEnergyCanonicalChildBound CenteredMomentSectorLocalization
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

open CenteredMomentEnergyCanonicalUniformReference CenteredMomentEnergyAmplifiedRayDictionary
open CenteredMomentFirstAmplifiedPaidAdmission CenteredMomentFirstAmplifiedCapacityCommon
open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps
open CenteredMomentCanonicalFirst CenteredMomentSecondExceptionalFamily CenteredMomentSourceLiveColumn
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonical CanonicalQuadraticSieve CompletedGauss
open CanonicalRowCompletion ConcretePrimeRowBridge ActualEisensteinCubic
open CenteredMomentSecondHeightFamily
open CenteredMomentFirstCanonicalFamily CenteredMomentFirstScale CenteredMomentAmplifiedRetainedRadius

open RayFourExpansion CenteredMomentSourceMass CenteredMomentSecondRetainedAggregate
open CenteredMomentSecondEnergySplit CenteredMomentGaussNormalization
open Filter CenteredMomentOriginalCommonHarmonic CenteredMomentActiveSource
open CenteredMomentSecondLiveBlock CenteredMomentSecondBlockAggregate CenteredMomentSecondWindowSource
open CenteredMomentFirstChildProfileControl CenteredMomentSecondChildPowerBudget
open CenteredMomentSecondSourceSeededPowerDescent CenteredMomentSecondReferenceNormalization
open CenteredMomentFirstSeededGaussianPower CenteredMomentFirstSecondInputGates

open CenteredMomentEnergyFirstGaussianCoefficients CenteredMomentFirstAmplifiedFourCoefficients

open CenteredMomentFirstSecondActiveErrorGates CenteredMomentFirstAnnularInput
open CenteredMomentFirstAmplificationChoice (errorMoving errorRemoval)

open CenteredMomentEnergyAmplifiedChildWidth
open CenteredMomentEnergyCanonicalAmplifiedUniform CenteredMomentEnergyAmplifierFamilyAdmission
open CenteredMomentEnergyFirstLiveAdmission CenteredMomentEnergyFirstAnnularAdmission
open CenteredMomentEnergyFirstRawScaleAdmission CenteredMomentEnergyInputParentCapacity
open CenteredMomentFirstReferenceSource CenteredMomentFirstNonexceptionalWeightSum
open CenteredMomentPrimePool CenteredMomentPrimeElements CenteredMomentAmplificationRadicalFamily
open CenteredMomentAmplificationActiveFactor CenteredMomentAmplificationEligibility
open CenteredMomentFirstPhysicalSource CenteredMomentFirstPhysicalDyadicRows
open CenteredMomentFirstAmplifiedPowerBudget CenteredMomentFirstAmplificationChoice
open CenteredMomentSecondRetainedRows CenteredMomentLogDyadic

theorem actual_original_subsets_annular_power
    (Wslot:ℝ→ℂ)(aslot bslot Mcap Lslot εremove lo hi κ:ℝ)
    (a b Mslot εmask:ℝ)(hMslot:0≤Mslot)(hεmask:0<εmask)(haPlain:0<a)(hbPlain:0≤b)
    (L:ℝ)(hL:0≤L)(degree:ℕ)(S:Finset (ℕ×ℕ))
    (ha:0<aslot)(hWs:Function.support Wslot⊆Set.Icc aslot bslot)
    (hW:ContDiff ℝ ∞ Wslot)(hMcap:0≤Mcap)(hLs:0≤Lslot)(hε:0<εremove)
    (hκsmall:(1/6:ℝ)≤κ)(hbeta:(51/100:ℝ)≤HeckeZeroSupremum.beta)
    (hκ:2*HeckeZeroSupremum.beta-1≤κ)
    (N:ℕ)(lower upper a0 θsource:ℝ)(hlower:0<lower)(hupper:1≤upper)
    (ha0:0<a0)(hθsource:0<θsource)
    (lows highs:α→ℝ)(hhighs:∀i,0≤highs i)
    (εsrc δsrc θsrc Bseed ξ saving:ℝ)
    (hεsrc:0<εsrc)(hδsrc:0<δsrc)(hθsrc:0<θsrc)(hξ:0<ξ)
    (sigma:ℝ)(hsigma:0<sigma)(hξsmall:ξ≤sigma/4)(A Pcap eta primeLoss reserve:ℝ)
    (hA:0≤A)(hPcap:0≤Pcap)(heta:eta<sigma/6)(hPrimeLoss:0<primeLoss)
    (hsigma1:sigma≤1)(_hξ1:ξ≤1)(hreserve:0<reserve):
    ∃Uprofile:Finset (ℕ×ℕ),∃Jheight:ℕ,
    ∀η₀:Character,∀Q:Ideal O,Q≤M →
      internalQ Q η₀≠0 → internalQ Q η₀≠⊤ → internalQ Q η₀≤Ideal.span {(72:O)} →
    ∃Cbound:ℝ,0<Cbound ∧ ∃Z₀:ℝ,1<Z₀ ∧ ∀Z:ℝ,Z₀≤Z →
    let P:=primePool M H fixedBadPrimes (1/2) 1 (Z^(sigma/3));
    P.Nonempty ∧ Z^(sigma/3-primeLoss)≤(P.card:ℝ) ∧
    ∀τ:Character,∃υ:(Aorig:Finset α)→(Ac:Finset Aorig)→elementPool P→Fin 3→RayCharacter→Character,
    (∀Aorig Ac prime i χ,(υ Aorig Ac prime i χ).modulus.absNorm≤
      radicalBound (CenteredMomentChildRows.childCharacter τ χ) fixedBadMask prime.val
        (errorMovingExponent (errorIndex i))) ∧
    ∀Aorig:Finset α,∀θ:Aorig→RayQuotient.Characters M H,
    ∀εchild:ℝ,∀C₀ C₁:ℝ,0≤C₀ → 0≤C₁ →
    ZeroAt (internalQ Q η₀) (a/max 1 b) b 2 0 L Mcap εchild Z degree S C₀ →
    PositiveAt (α:=α) M H hH Wslot bslot (a/max 1 b) b 2 0 L Lslot lo hi
      Mcap εchild κ Z η₀ Q degree S C₁ →
    ∀(w σ freq:Aorig→ℝ)(height mesh:ℝ),0≤mesh → (∀i,0≤w i) → (∀i,w i≤mesh) → (∀i,w i≤eta) →
    (∀i,w i≤Lslot) → (∀i,lo≤σ i) → (∀i,σ i≤hi) → 0≤height → (∀i,|freq i|≤height) →
    ∀src:Input Aorig,Matches M H hH src η₀ θ w σ freq Wslot bslot Z →
    (∀i,src.hi i≤bslot) → (∀i,src.M i≤Mslot) →
    (∀i,src.lo i=lows i.val) → (∀i,src.hi i=highs i.val) →
    Fintype.card Aorig≤N → lower≤src.lower → src.upper≤upper →
    0≤src.b₁ → 0≤src.b₂ → src.b₁≤max 1 b → src.b₂≤max 1 b →
    ∀(C D R0:Ideal O),∀_hC:Supported C,∀_hD:Supported D,primeSupport C=primeSupport D →
    R0≠0 → (R0.absNorm:ℝ)≤Z^Pcap → (C.absNorm:ℝ)≤Z^(A+1) →
    ∀E:Finset (CommonIndex C D),
    τ.modulus=src.η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E*activeConductor C D} →
    ∀K H0:ℝ,0<K → 0<H0 →
    H0≤4*frequencyRadius
      (firstNominalScale C D (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K (volume src)) Z ξ →
    8*H0≤Z^(amplifierCap A 0 ξ) →
    ∀(B:actualAllocations src.pools C)(t:ℝ),
    frozenCoefficient B.val C R0 src.ν src.W src.P≠0 →
    ∀seed:Ideal O,Squarefree seed → seed≠0 → (seed.absNorm:ℝ)≤Z^Bseed →
    ∀p:Profiles a b,p.profile 0=src.W₁ → p.profile 1=src.W₂ →
    src.X₁≤Z^L → src.X₂≤Z^L → src.Y₁≤Z^L → src.Y₂≤Z^L →
    ∀Mdecl Mwidth θclip:ℝ,0≤θclip →
    length Z src.X₁+length Z src.X₂+6*κ*(∑i,w i)≤Mdecl →
    Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ)≤Mdecl →
    Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ)≤Mwidth →
    Mwidth-sigma/2≤Mcap →
    Real.logb Z (max 1 b*max 1 b)≤2*θclip →
    a0≤CenteredMomentSecondInputCapacitySource.lowerFactor N lower a →
    Ready (child src C R0 B τ t) (R0*C)
      (mainRadius C D E K (volume src) Z sigma (frequencyLoss Z 32 ξ) reserve) Z ξ (readyBudget A Pcap) →
    (∀prime:elementPool P,∀i:Fin 3,∀χ:RayCharacter,
      ∀Bp:actualAllocations (activeInput (child src C R0 B τ t)).pools ((Ideal.span {prime.val})^(errorIndex i+1)),
      let d:=errorInput src C R0 B τ t (Ideal.span {prime.val}) (errorIndex i+1) Bp
        (υ Aorig (CenteredMomentCommonProfile.liveIndices B.val) prime i χ) t;
      (∀I:Ideal O,coefficient d ((R0*C)*(Ideal.span {prime.val})^(errorIndex i+1)) seed I=0) ∨
      Ready d ((R0*C)*(Ideal.span {prime.val})^(errorIndex i+1))
        (errorRadius C D E K (volume src) Z sigma (frequencyLoss Z 32 ξ) reserve prime (errorIndex i+1))
        Z ξ (readyBudget A Pcap)) →
    let input:=child src C R0 B τ t;
    let delta:=frequencyLoss Z 32 ξ;
    let Bcap:=readyBudget A Pcap;
    let paid:=(Bcap+Bcap)*εmask+εchild+εremove+(delta+reserve+θsource)/6+θclip/3+κ*mesh;
    let deficit:=Mdecl-(Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ));
    let rmain:=parentLower src Z-Real.logb Z (C.absNorm:ℝ);
    let Kmain:=mainRadius C D E K (volume src) Z sigma delta reserve;
    let Hcoef:=fun j=>Cbound*(C₀+C₁+1)*(p.control Uprofile)^2*(1+|t|+height)^Jheight*
      Z^(CenteredMomentEnergyFirstGaussianProfileWeights.losses εsrc δsrc θsrc Bcap j)/(seed.absNorm:ℝ);
    let amain:=fun j=>Hcoef j*mainPowers (τ.modulus.absNorm:ℝ) Z Kmain (sigma/3) deficit paid saving rmain j;
    let aerror:=fun (prime:elementPool P)(i:Fin 3)(_χ:RayCharacter)(j:Fin 4)=>
      Hcoef j*errorPowers prime (errorIndex i+1) (τ.modulus.absNorm:ℝ) Z
        (errorRadius C D E K (volume src) Z sigma delta reserve prime (errorIndex i+1))
        deficit paid saving (rmain-errorRemoval prime Z (errorIndex i+1)) j;
    childNormalizedGaussSource src C R0 seed B τ t CenteredMomentFirstAnnularMajorant.profile
      H0≤
      (∑j,sourceCoefficients P ((amplifierCap A 0 ξ+2*sigma)/(sigma/6)) amain aerror (powers εsrc) j*
        (volume input)^(powers εsrc j))*mass input^2 :=by
  let Bcap:=readyBudget A Pcap
  have hBcap:0≤Bcap:=readyBudget_nonneg A Pcap hA hPcap
  have hAmp:0≤amplifierCap A 0 ξ:=by unfold amplifierCap;positivity
  obtain ⟨U,J,huniform⟩:=actual_original_subsets_amplified_power (α:=α) M H hH
    Wslot aslot bslot Mcap Lslot εremove lo hi κ a b Mslot εmask hMslot hεmask haPlain hbPlain
    L hL degree S ha hWs hW hMcap hLs hε hκsmall hbeta hκ N lower upper a0 θsource
    hlower hupper ha0 hθsource lows highs hhighs εsrc δsrc θsrc Bcap Bseed ξ saving
    hεsrc hδsrc hθsrc hBcap hξ sigma referenceCost hsigma hξsmall referenceCost_ge_one
  refine ⟨U,J,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨Cbound,hCbound,Zbase,hZbase,hm,he⟩:=huniform η₀ Q hQM hQ0 hQt hQ72
  have hall:=Filter.eventually_all.mpr (fun Aorig:Finset α=>
    eventually_original_subsets_power_amplification (Ω:=Aorig) M H hH fixedBadPrimes (Finset.Subset.refl _)
      sigma primeLoss (Pcap+A+1) Bseed (amplifierCap A 0 ξ) (max 1 bslot) eta 1 ξ reserve
      hsigma hPrimeLoss hAmp (by positivity) heta (by norm_num) hξ.le hreserve)
  have hsepEvent:=CenteredMomentFirstAmplificationChoice.eventually_dyadic_amplification.{0}
    M H hH fixedBadPrimes (Finset.Subset.refl _) sigma primeLoss (Pcap+A+1) Bseed
      (amplifierCap A 0 ξ) (max 1 bslot) eta hsigma hPrimeLoss hAmp heta
  obtain ⟨Z₀,hZ₀⟩:=Filter.eventually_atTop.mp
    (hall.and (hsepEvent.and (eventually_ge_atTop Zbase)))
  refine ⟨Cbound,hCbound,max Z₀ Zbase,lt_of_lt_of_le hZbase (le_max_right _ _),?_⟩
  intro Z hZthreshold
  obtain ⟨hamp,hsepdata,hZZbase⟩:=
    hZ₀ Z ((le_max_left _ _).trans hZthreshold)
  have hZ:1<Z:=hZbase.trans_le hZZbase
  dsimp only
  have hbase:=hamp (∅:Finset α)
  refine ⟨hbase.2.1,hbase.2.2.1,?_⟩
  intro τ
  have hf (Aorig:Finset α):=(hamp Aorig).2.2.2 τ
  choose υ hυN henergy using hf
  refine ⟨υ,hυN,?_⟩
  intro Aorig θ εchild C₀ C₁ hC₀ hC₁ hzero hpos w σ freq height mesh hmesh hw hwm hweta hwL
    hσlo hσhi hheight hfreq src hmatch hhi hMs hloSrc hhiSrc hcard hlowerSrc hupperSrc
    hb1 hb2 hb1max hb2max C D R0 hC hD hCD hR0 hRcap hNC
    E hmod K H0 hK hH0 houter hHcap B t hB seed hseed hseedne hseedcap
    p hp₁ hp₂ hX₁ hX₂ hY₁ hY₂ Mdecl Mwidth θclip hθclip hcap hMdecl hMwidth
    hdrop hclip hsourceLower hreadym herrorPacket
  let input:=child src C R0 B τ t
  let delta:=frequencyLoss Z 32 ξ
  have hdelta:0≤delta:=frequencyLoss_nonneg Z 32 ξ hZ (by norm_num) hξ.le
  have hRC:(R0*C).absNorm=R0.absNorm*C.absNorm:=map_mul _ _ _
  have hRcommon:( (R0*C).absNorm:ℝ)≤Z^(Pcap+A+1):=by
    rw [hRC,Nat.cast_mul]
    calc
      _≤Z^Pcap*Z^(A+1):=mul_le_mul hRcap hNC (Nat.cast_nonneg _) (Real.rpow_nonneg (by linarith) _)
      _=Z^(Pcap+A+1):=by rw [←Real.rpow_add (by linarith:0<Z)];congr 1;ring
  have hmainlower:=main_minimum_lower src C R0 hC.1 B τ t Z hZ
  have hmain:=hm Aorig θ Z hZZbase εchild C₀ C₁ hC₀ hC₁ hzero hpos
    w σ freq height mesh hmesh hw hwm hwL hσlo hσhi hheight hfreq src hmatch hhi hMs
    hloSrc hhiSrc hcard hlowerSrc hupperSrc hb1 hb2 hb1max hb2max C D R0 hC hD hCD E B τ t hB hmod
    K delta reserve a0 hK ha0 hdelta hreserve.le le_rfl
    hreadym seed hseed hseedne hseedcap p hp₁ hp₂ hX₁ hX₂ hY₁ hY₂ Mdecl Mwidth θclip hθclip
    hcap hMdecl hMwidth hdrop hclip hsourceLower _
    hmainlower.1 hmainlower.2.1 hmainlower.2.2.1 hmainlower.2.2.2
  let paid:=(Bcap+Bcap)*εmask+εchild+εremove+(delta+reserve+θsource)/6+θclip/3+κ*mesh
  let deficit:=Mdecl-(Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ))
  let rmain:=parentLower src Z-Real.logb Z (C.absNorm:ℝ)
  let Kmain:=mainRadius C D E K (volume src) Z sigma delta reserve
  let Hcoef:=fun j=>Cbound*(C₀+C₁+1)*(p.control U)^2*(1+|t|+height)^J*
    Z^(CenteredMomentEnergyFirstGaussianProfileWeights.losses εsrc δsrc θsrc Bcap j)/(seed.absNorm:ℝ)
  let amain:=fun j=>Hcoef j*mainPowers (τ.modulus.absNorm:ℝ) Z Kmain (sigma/3) deficit paid saving rmain j
  let aerror:=fun (prime:elementPool (primePool M H fixedBadPrimes (1/2) 1 (Z^(sigma/3))))
    (i:Fin 3)(χ:RayCharacter)(j:Fin 4)=>Hcoef j*
      errorPowers prime (errorIndex i+1) (τ.modulus.absNorm:ℝ) Z
      (errorRadius C D E K (volume src) Z sigma delta reserve prime (errorIndex i+1))
      deficit paid saving (rmain-errorRemoval prime Z (errorIndex i+1)) j
  have hHcoef:∀j,0≤Hcoef j:=by intro j;dsimp [Hcoef];positivity
  have haerror:∀prime i χ j,0≤aerror prime i χ j:=by
    intro prime i χ j
    apply mul_nonneg (hHcoef j)
    fin_cases j <;> simp only [errorPowers,Matrix.cons_val,Fin.reduceFinMk]
    all_goals try unfold errorRadius errorCommonRadius
    all_goals positivity
  have hsupp:∀i,Function.support (input.W i)⊆Set.Iic (max 1 bslot):=by
    intro i x hx
    exact ((src.support i.val hx).2.trans (hhi i.val)).trans (le_max_right _ _)
  let z:CenteredMomentCommonProfile.liveIndices B.val→ℝ:=fun i=>w i.val
  have hz:∀i,z i≤eta:=fun i=>hweta i.val
  have hlen:∀i,input.P i=Z^(z i):=fun i=>hmatch.scale i.val
  obtain ⟨_,_,_,hsep,hdata,_⟩:=hsepdata
  have herror:∀prime:elementPool (primePool M H fixedBadPrimes (1/2) 1 (Z^(sigma/3))),
      ∀i:Fin 3,∀χ:RayCharacter,
      ∀Bp:actualAllocations (activeInput input).pools ((Ideal.span {prime.val})^(errorIndex i+1)),
      childNormalizedGaussSource (activeInput input) ((Ideal.span {prime.val})^(errorIndex i+1))
        (R0*C) seed Bp (υ Aorig (CenteredMomentCommonProfile.liveIndices B.val) prime i χ) input.t
        CenteredMomentFirstAmplificationChoice.ballProfile
        (errorRadius C D E K (volume src) Z sigma delta reserve prime (errorIndex i+1))≤
      (∑j,aerror prime i χ j*(volume (child (activeInput input)
        ((Ideal.span {prime.val})^(errorIndex i+1)) (R0*C) Bp
        (υ Aorig (CenteredMomentCommonProfile.liveIndices B.val) prime i χ) input.t))^(powers εsrc j))*
        mass (child (activeInput input) ((Ideal.span {prime.val})^(errorIndex i+1)) (R0*C) Bp
        (υ Aorig (CenteredMomentCommonProfile.liveIndices B.val) prime i χ) input.t)^2:=by
    intro prime i χ Bp
    have hd:=elementPool_data _ (fun Q hQ=>(hdata Q hQ).1)
      (fun Q hQ=>(hdata Q hQ).2.1) prime.val prime.property
    have hprime:prime.val≠0:=hd.1.ne_zero
    have hcop:∀j,∀I∈(activeInput input).slots j,IsCoprime (Ideal.span {prime.val}) I:=by
      exact CenteredMomentFirstAmplificationChoice.original_slot_coprime (original input (R0*C) seed).active
        Z sigma (max 1 bslot) eta hZ.le (by positivity) hsep z hz hlen hsupp
        (original input (R0*C) seed).active_slot
        (fun j Q hQ=>input.prime j Q ((original input (R0*C) seed).active_subset _ hQ))
        _ (hdata _ hd.2.1).1 (hdata _ hd.2.1).2.2.1
    have hk:=CenteredMomentFirstAmplificationChoice.errorIndex_cases i
    have hk':errorIndex i+1=1∨errorIndex i+1=6∨errorIndex i+1=7:=by omega
    have hN:=hυN Aorig (CenteredMomentCommonProfile.liveIndices B.val) prime i χ
    have hvcap:=actual_error_reference_cap τ _ χ prime.val hprime (errorIndex i) hk Z hZ hN
    have hre:=herrorPacket prime i χ Bp
    rcases hre with hdead|hlive
    · change normalizedGaussSource _ _ _ _ _≤_
      apply (CenteredMomentFirstSecondInputGates.normalized_zero _ _ _ hdead _ _).le.trans
      exact mul_nonneg (Finset.sum_nonneg (fun j _=>mul_nonneg (haerror prime i χ j)
        (Real.rpow_nonneg (volume_pos _).le _))) (sq_nonneg _)
    · have hlower:=error_minimum_lower src C R0 hC.1 B τ t prime.val hprime
        (errorIndex i+1) Bp (υ Aorig (CenteredMomentCommonProfile.liveIndices B.val) prime i χ) t Z hZ
      have hprimeScale: sigma/6≤Real.logb Z (normValue prime.val):=by
        have hh:=Real.logb_le_logb_of_le hZ
          (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) (sigma/6)) (hdata _ hd.2.1).2.2.1
        simpa only [normValue,Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne'] using hh
      have hh:=he Aorig θ Z hZZbase εchild C₀ C₁ hC₀ hC₁ hzero hpos
        w σ freq height mesh hmesh hw hwm hwL hσlo hσhi hheight hfreq src hmatch hhi hMs
        hloSrc hhiSrc hcard hlowerSrc hupperSrc hb1 hb2 hb1max hb2max C D R0 hC hD hCD E B τ t hB hmod
        K delta reserve a0 hK ha0 hdelta hreserve.le le_rfl
        prime.val hprime (errorIndex i) hk hprimeScale hcop Bp _ χ hN hvcap _ rfl
        hlive seed hseed hseedne hseedcap p hp₁ hp₂ hX₁ hX₂ hY₁ hY₂ Mdecl Mwidth θclip hθclip
        hcap hMdecl hMwidth hdrop hclip hsourceLower _
        hlower.1 hlower.2.1 hlower.2.2.1 hlower.2.2.2
      exact hh
  have hE:Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}≠0:=
    Ideal.span_singleton_eq_bot.not.mpr (primeSubsetGenerator_ne_zero _ _)
  have hann:=henergy Aorig (CenteredMomentCommonProfile.liveIndices B.val) input rfl hsupp z hz hlen
    (R0*C) seed (mul_ne_zero hR0 hC.1) hseedne hRcommon hseedcap
    (Real.logb Z (D.absNorm:ℝ)) (Real.logb Z (C.absNorm:ℝ)) C D
    (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) hE K (volume src) _
    hK (volume_pos src) (by simp only [one_mul];exact le_rfl) H0 hH0 houter hHcap
    amain aerror (powers εsrc) haerror (by simpa only [mul_one,nominalLog,input,amain,Hcoef,Kmain,mainRadius,paid,deficit,rmain,delta] using hmain)
    (by simpa only [mul_one,nominalLog,errorRadius,delta] using herror)
  apply hann.trans_eq
  rw [source_coefficients_identity _ _ _ (volume_pos input).le]
  dsimp only [normValue]
  ring

end SevenEighths.CenteredMomentEnergyCanonicalAnnularPower

end

end OAI
