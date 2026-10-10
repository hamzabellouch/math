import OAI.NumberTheory.DirichletL.Energy.CanonicalAnnularPower
import OAI.NumberTheory.DirichletL.Energy.CanonicalAmplifiedColumn
import OAI.NumberTheory.DirichletL.Energy.FirstLowHomogeneousPowers
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

namespace SevenEighths.CenteredMomentEnergyCanonicalLowColumn
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

open CenteredMomentEnergyCanonicalAnnularPower CenteredMomentEnergyCanonicalAmplifiedColumn
open CenteredMomentFirstCommonReferencePower CenteredMomentEnergyFirstLowHomogeneousPowers

lemma source_mass_cap {ι:Type*}[Fintype ι](s:Input ι)(N:ℕ)(Mslot:ℝ)
    (hc:Fintype.card ι≤N)(hM:∀i,s.M i≤Mslot):mass s≤(max 1 Mslot)^N:=by
  calc
    _≤∏i:ι,max 1 Mslot:=by
      apply Finset.prod_le_prod₀
      · intro i _;exact zero_le_one.trans (s.M_ge_one i)
      · intro i _;exact (hM i).trans (le_max_right _ _)
    _=(max 1 Mslot)^Fintype.card ι:=by simp
    _≤_:=pow_le_pow_right₀ (le_max_left _ _) hc

lemma inherited_height_split (t height:ℝ)(J:ℕ)(hh:0≤height):
    (1+|t|+height)^J≤(1+height)^J*(1+|t|)^(2*J):=by
  have hbase:1+|t|+height≤(1+height)*(1+|t|):=by
    nlinarith [abs_nonneg t,mul_nonneg hh (abs_nonneg t)]
  calc
    _≤((1+height)*(1+|t|))^J:=pow_le_pow_left₀ (by positivity) hbase J
    _=(1+height)^J*(1+|t|)^J:=mul_pow _ _ _
    _≤_:=mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ (by linarith [abs_nonneg t]) (by omega:J≤2*J)) (by positivity)

theorem actual_admitted_subsets_low_column
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
    (hsigma1:sigma≤1)(hξ1:ξ≤1)(hreserve:0<reserve)(heps1:εsrc≤1):
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
    ∀(C D R0:Ideal O),∀hC:Supported C,∀_hD:Supported D,primeSupport C=primeSupport D →
    R0≠0 → (R0.absNorm:ℝ)≤Z^Pcap → (C.absNorm:ℝ)≤Z^(A+1) →
    ∀E:Finset (CommonIndex C D),
    τ.modulus=src.η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E*activeConductor C D} →
    ∀K H0:ℝ,0<K → 0<H0 →
    H0≤4*frequencyRadius
      (firstNominalScale C D (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K (volume src)) Z ξ →
    8*H0≤Z^(amplifierCap A 0 ξ) →
    ∀(t:ℝ)(seed0:Ideal O),seed0∣C →
    ∀seed:Ideal O,Squarefree seed → seed≠0 → (seed.absNorm:ℝ)≤Z^Bseed →
    ∀p:Profiles a b,p.profile 0=src.W₁ → p.profile 1=src.W₂ →
    src.X₁≤Z^L → src.X₂≤Z^L → src.Y₁≤Z^L → src.Y₂≤Z^L →
    ∀Mdecl Mwidth θclip:ℝ,0≤θclip → 0≤Mdecl → Mdecl≤A →
    Real.logb Z (volume src)≤5*Mdecl/6 →
    length Z src.X₁+length Z src.X₂+6*κ*(∑i,w i)≤Mdecl →
    Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ)≤Mdecl →
    Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ)≤Mwidth →
    Mwidth-sigma/2≤Mcap →
    Real.logb Z (max 1 b*max 1 b)≤2*θclip →
    a0≤CenteredMomentSecondInputCapacitySource.lowerFactor N lower a →
    (∀B:actualAllocations src.pools C,
      frozenCoefficient B.val C R0 src.ν src.W src.P≠0 →
      Ready (child src C R0 B τ t) (R0*C)
      (mainRadius C D E K (volume src) Z sigma (frequencyLoss Z 32 ξ) reserve) Z ξ (readyBudget A Pcap) ∧
    (∀prime:elementPool P,∀i:Fin 3,∀χ:RayCharacter,
      ∀Bp:actualAllocations (activeInput (child src C R0 B τ t)).pools ((Ideal.span {prime.val})^(errorIndex i+1)),
      let d:=errorInput src C R0 B τ t (Ideal.span {prime.val}) (errorIndex i+1) Bp
        (υ Aorig (CenteredMomentCommonProfile.liveIndices B.val) prime i χ) t;
      (∀I:Ideal O,coefficient d ((R0*C)*(Ideal.span {prime.val})^(errorIndex i+1)) seed I=0) ∨
      Ready d ((R0*C)*(Ideal.span {prime.val})^(errorIndex i+1))
        (errorRadius C D E K (volume src) Z sigma (frequencyLoss Z 32 ξ) reserve prime (errorIndex i+1))
        Z ξ (readyBudget A Pcap))) →
    let delta:=frequencyLoss Z 32 ξ;
    let Bcap:=readyBudget A Pcap;
    let paid:=(Bcap+Bcap)*εmask+εchild+εremove+(delta+reserve+θsource)/6+θclip/3+κ*mesh;
    let deficit:=Mdecl-(Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ));
    let ref:=(τ.modulus.absNorm:ℝ)*(volume src/(C.absNorm:ℝ))^2*Z^(CenteredMomentFirstMixedAllowance.allowance C D Z);
    (commonEnergy (original src R0 seed0) C hC τ t seed
      CenteredMomentFirstAnnularMajorant.profile H0).re≤
      (ref/(seed.absNorm:ℝ))*(Cbound*(C₀+C₁+1)*(p.control Uprofile)^2*(1+height)^Jheight*
        Z^(deficit+εsrc*(A+1)+primeLoss)*
        ∑j:Fin 4,Z^(CenteredMomentEnergyFirstGaussianProfileWeights.losses εsrc δsrc θsrc Bcap j+
          lossVector sigma delta reserve paid εsrc A saving j))*(1+|t|)^(2*Jheight) :=by
  obtain ⟨U,J,hann⟩:=actual_original_subsets_annular_power (α:=α) M H hH
    Wslot aslot bslot Mcap Lslot εremove lo hi κ a b Mslot εmask hMslot hεmask haPlain hbPlain
    L hL degree S ha hWs hW hMcap hLs hε hκsmall hbeta hκ N lower upper a0 θsource
    hlower hupper ha0 hθsource lows highs hhighs εsrc δsrc θsrc Bseed ξ saving
    hεsrc hδsrc hθsrc hξ sigma hsigma hξsmall A Pcap eta primeLoss reserve
    hA hPcap heta hPrimeLoss hsigma1 hξ1 hreserve
  obtain ⟨Cb,hCb,hcommon⟩:=common_energy_reference_powers N lower upper εsrc hlower hupper hεsrc
  let Mamp:=amplifierCap A 0 ξ
  let avg:=56*((Mamp+2*sigma)/(sigma/6)+1872*(Fintype.card RayCharacter:ℝ))
  have hMamp:0≤Mamp:=by dsimp [Mamp,amplifierCap];positivity
  have havg:0<avg:=by dsimp [avg];positivity
  have hmcap:0<(max 1 Mslot)^(2*N):=pow_pos (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) _
  refine ⟨U,J,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨Ca,hCa,Z₀,hZ₀,hannZ⟩:=hann η₀ Q hQM hQ0 hQt hQ72
  let Ccolumn:=Cb*upper^N*avg*Ca*(max 1 Mslot)^(2*N)
  have hCcolumn:0<Ccolumn:=by dsimp [Ccolumn];positivity
  refine ⟨Ccolumn,hCcolumn,Z₀,hZ₀,?_⟩
  intro Z hZZ
  have hZ:1<Z:=hZ₀.trans_le hZZ
  have hZpos:0<Z:=zero_lt_one.trans hZ
  obtain ⟨hPne,hPcard,hfamily⟩:=hannZ Z hZZ
  dsimp only at hPne hPcard hfamily ⊢
  refine ⟨hPne,hPcard,?_⟩
  intro τ
  obtain ⟨υ,hυ,henergy⟩:=hfamily τ
  refine ⟨υ,hυ,?_⟩
  intro Aorig θ εchild C₀ C₁ hC₀ hC₁ hzero hpos w σ freq height mesh hmesh hw hwm hweta hwL
    hσlo hσhi hheight hfreq src hmatch hhi hMs hloSrc hhiSrc hcard hlowerSrc hupperSrc
    hb1 hb2 hb1max hb2max C D R0 hC hD hCD hR0 hRcap hNC E hmod
    K H0 hK hH0 houter hHcap t seed0 hseed0 seed hseed hseedne hseedcap
    p hp₁ hp₂ hX₁ hX₂ hY₁ hY₂ Mdecl Mwidth θclip hθclip hMdecl0 hMA hlow
    hcap hMdecl hMwidth hdrop hclip hsourceLower hpackets
  let P:=primePool M H fixedBadPrimes (1/2) 1 (Z^(sigma/3))
  let delta:=frequencyLoss Z 32 ξ
  let Bcap:=readyBudget A Pcap
  let paid:=(Bcap+Bcap)*εmask+εchild+εremove+(delta+reserve+θsource)/6+θclip/3+κ*mesh
  let deficit:=Mdecl-(Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ))
  let rmain:=parentLower src Z-Real.logb Z (C.absNorm:ℝ)
  let Kmain:=mainRadius C D E K (volume src) Z sigma delta reserve
  let Kerror:=fun (prime:elementPool P)(i:Fin 3)(_:RayCharacter)=>
    errorRadius C D E K (volume src) Z sigma delta reserve prime (errorIndex i+1)
  let rerror:=fun (prime:elementPool P)(i:Fin 3)(_:RayCharacter)=>
    rmain-errorRemoval prime Z (errorIndex i+1)
  let front:=Ca*(C₀+C₁+1)*(p.control U)^2*(1+|t|+height)^J
  let Hcoef:=fun j:Fin 4=>front*
    Z^(CenteredMomentEnergyFirstGaussianProfileWeights.losses εsrc δsrc θsrc Bcap j)/(seed.absNorm:ℝ)
  let amain:=fun j=>Hcoef j*mainPowers (τ.modulus.absNorm:ℝ) Z Kmain (sigma/3) deficit paid saving rmain j
  let aerror:=fun (prime:elementPool P)(i:Fin 3)(χ:RayCharacter)(j:Fin 4)=>
    Hcoef j*errorPowers prime (errorIndex i+1) (τ.modulus.absNorm:ℝ) Z
      (Kerror prime i χ) deficit paid saving (rerror prime i χ) j
  let coeff:=sourceCoefficients P ((Mamp+2*sigma)/(sigma/6)) amain aerror (powers εsrc)
  have hNseed:0<(seed.absNorm:ℝ):=CenteredMomentFirstScale.norm_pos _ hseedne
  have hq:0<(τ.modulus.absNorm:ℝ):=CenteredMomentFirstScale.norm_pos _ τ.modulus_ne_bot
  have hfront:0≤front:=by dsimp [front];positivity
  have hHcoef:∀j,0≤Hcoef j:=by intro j;dsimp [Hcoef];positivity
  have hKmain:0≤Kmain:=by unfold Kmain mainRadius mainCommonRadius;positivity
  have hKerror:∀prime i χ,0≤Kerror prime i χ:=by
    intro prime i χ;unfold Kerror errorRadius errorCommonRadius;positivity
  have hcoeff:∀j,0≤coeff j:=source_coefficients_nonneg P _ (by positivity)
    amain aerror (powers εsrc)
    (fun j=>mul_nonneg (hHcoef j) (main_coefficients_nonneg _ _ _ _ _ _ _ _ hq.le hZpos.le hKmain j))
    (fun prime i χ j=>mul_nonneg (hHcoef j)
      (error_coefficients_nonneg _ _ _ _ _ _ _ _ _ hq.le hZpos.le (hKerror prime i χ) j))
  have hchildren (B:actualAllocations src.pools C)
      (hB:frozenCoefficient B.val C R0 src.ν src.W src.P≠0):
      childNormalizedGaussSource src C R0 seed B τ t CenteredMomentFirstAnnularMajorant.profile H0≤
        (∑j,coeff j*(volume (child src C R0 B τ t))^(powers εsrc j))*mass (child src C R0 B τ t)^2:=by
    exact henergy Aorig θ εchild C₀ C₁ hC₀ hC₁ hzero hpos w σ freq height mesh
      hmesh hw hwm hweta hwL hσlo hσhi hheight hfreq src hmatch hhi hMs hloSrc hhiSrc
      hcard hlowerSrc hupperSrc hb1 hb2 hb1max hb2max C D R0 hC hD hCD hR0 hRcap hNC E hmod
      K H0 hK hH0 houter hHcap B t hB seed hseed hseedne hseedcap p hp₁ hp₂ hX₁ hX₂ hY₁ hY₂
      Mdecl Mwidth θclip hθclip hcap hMdecl hMwidth hdrop hclip hsourceLower
      (hpackets B hB).1 (hpackets B hB).2
  have hcommonBound:=hcommon src hcard hlowerSrc hupperSrc C R0 seed0 hC hseed0 τ t seed
    CenteredMomentFirstAnnularMajorant.profile H0 Z (CenteredMomentFirstMixedAllowance.allowance C D Z)
    hH0 hZpos (fun z=>CenteredMomentFirstAnnularMajorant.profile_nonneg _) 4 coeff (powers εsrc)
    hcoeff (powers_nonneg εsrc hεsrc.le) hchildren
  have hscalar:=actual_low_homogeneous_four_powers M H fixedBadPrimes (Finset.Subset.refl _)
    src.η τ C D hC hD hCD E K (volume src) Z sigma delta reserve paid εsrc saving Mdecl A Mamp primeLoss
    hK (volume_pos src) hZ hsigma hεsrc.le hMdecl0 hMA hMdecl hlow hPrimeLoss.le hMamp hPcard hmod
    upper N hupper Hcoef hHcoef front (seed.absNorm:ℝ) (A+1)
    (CenteredMomentEnergyFirstGaussianProfileWeights.losses εsrc δsrc θsrc Bcap)
    hfront hNseed heps1 hNC (fun j=>le_rfl) rmain rerror
  dsimp only at hscalar
  have hmass:=source_mass_cap src N Mslot hcard hMs
  have hmass2:mass src^2≤(max 1 Mslot)^(2*N):=by
    calc
      _≤((max 1 Mslot)^N)^2:=pow_le_pow_left₀ (mass_nonneg src) hmass 2
      _=_:=by rw [←pow_mul];congr 1;omega
  have hheightSplit:=inherited_height_split t height J hheight
  let ref:=(τ.modulus.absNorm:ℝ)*(volume src/(C.absNorm:ℝ))^2*
    Z^(CenteredMomentFirstMixedAllowance.allowance C D Z)
  have href:0≤ref:=by dsimp [ref];positivity
  have hsum:0≤∑j:Fin 4,Z^(CenteredMomentEnergyFirstGaussianProfileWeights.losses εsrc δsrc θsrc Bcap j+
      lossVector sigma delta reserve paid εsrc A saving j):=Finset.sum_nonneg (fun _ _=>Real.rpow_nonneg hZpos.le _)
  calc
    _≤ref*(Cb*mass src^2*∑j,normalizedPower upper (volume src) (C.absNorm:ℝ)
        (τ.modulus.absNorm:ℝ) Z (CenteredMomentFirstMixedAllowance.allowance C D Z)
        εsrc (coeff j) N (powers εsrc j)):=hcommonBound
    _≤ref*(Cb*mass src^2*((upper^N*avg*front/(seed.absNorm:ℝ))*
        Z^(deficit+εsrc*(A+1)+primeLoss)*
        ∑j:Fin 4,Z^(CenteredMomentEnergyFirstGaussianProfileWeights.losses εsrc δsrc θsrc Bcap j+
          lossVector sigma delta reserve paid εsrc A saving j))):=by
      apply mul_le_mul_of_nonneg_left _ href
      apply mul_le_mul_of_nonneg_left hscalar
      exact mul_nonneg hCb.le (sq_nonneg _)
    _≤ref*(Cb*(max 1 Mslot)^(2*N)*((upper^N*avg*
        (Ca*(C₀+C₁+1)*(p.control U)^2*((1+height)^J*(1+|t|)^(2*J)))/(seed.absNorm:ℝ))*
        Z^(deficit+εsrc*(A+1)+primeLoss)*
        ∑j:Fin 4,Z^(CenteredMomentEnergyFirstGaussianProfileWeights.losses εsrc δsrc θsrc Bcap j+
          lossVector sigma delta reserve paid εsrc A saving j))):=by
      have hfrontBound:front≤Ca*(C₀+C₁+1)*(p.control U)^2*
          ((1+height)^J*(1+|t|)^(2*J)):=
        mul_le_mul_of_nonneg_left hheightSplit
          (mul_nonneg (mul_nonneg hCa.le
            (add_nonneg (add_nonneg hC₀ hC₁) zero_le_one)) (sq_nonneg _))
      apply mul_le_mul_of_nonneg_left _ href
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left hmass2 hCb.le
      · apply mul_le_mul_of_nonneg_right _ hsum
        apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hZpos.le _)
        apply div_le_div_of_nonneg_right _ hNseed.le
        exact mul_le_mul_of_nonneg_left hfrontBound
          (mul_nonneg (pow_nonneg (zero_le_one.trans hupper) _) havg.le)
      · exact mul_nonneg (mul_nonneg
          (div_nonneg (mul_nonneg
            (mul_nonneg (pow_nonneg (zero_le_one.trans hupper) _) havg.le) hfront) hNseed.le)
          (Real.rpow_nonneg hZpos.le _)) hsum
      · exact mul_nonneg hCb.le hmcap.le
    _=_:=by dsimp only [Ccolumn,ref,deficit,paid,Bcap,delta];ring

end SevenEighths.CenteredMomentEnergyCanonicalLowColumn

end

end OAI
