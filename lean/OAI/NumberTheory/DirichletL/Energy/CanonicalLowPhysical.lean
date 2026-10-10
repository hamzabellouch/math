import OAI.NumberTheory.DirichletL.Energy.CanonicalLowSource
import OAI.NumberTheory.DirichletL.Energy.CanonicalRightSourceColumn
import OAI.NumberTheory.DirichletL.Energy.FirstColumnPairing
import OAI.NumberTheory.DirichletL.Energy.FirstPhysicalNormalization
import OAI.NumberTheory.DirichletL.Energy.FirstTwoSeedAdmission
import OAI.NumberTheory.DirichletL.Energy.CanonicalLowColumn
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

namespace SevenEighths.CenteredMomentEnergyCanonicalLowPhysical
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
open CenteredMomentEnergyCanonicalLowColumn CenteredMomentFirstNonexceptionalLocalWeightSum

theorem actual_low_physical
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
    (hsigma1:sigma≤1)(hξ1:ξ≤1)(hreserve:0<reserve)
    (heps1:εsrc≤1)(hBseed:A+1≤Bseed)
    (Ψ:(T:Finset α)→𝓢(ℝ,ℂ))(εphysical lowerProduct:ℝ)
    (hεphysical:0<εphysical)(hlowerProduct:0<lowerProduct):
    ∃Uprofile:Finset (ℕ×ℕ),∃Jheight:ℕ,
    ∀η₀:Character,∀Q:Ideal O,Q≤M →
      internalQ Q η₀≠0 → internalQ Q η₀≠⊤ → internalQ Q η₀≤Ideal.span {(72:O)} →
    ∃Cphysical:ℝ,0<Cphysical ∧ ∃Z₀:ℝ,1<Z₀ ∧
    ∀Aorig:Finset α,∀θ:Aorig→RayQuotient.Characters M H,∀Z:ℝ,Z₀≤Z →
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
    lowerProduct≤(∏i,src.lo i)*a*a →
    ∀(R0 seed0:Ideal O),R0≠0 → (R0.absNorm:ℝ)≤Z^Pcap → Squarefree seed0 → seed0≠0 →
    ∀K:ℝ,1≤K →
    ∀p:Profiles a b,p.profile 0=src.W₁ → p.profile 1=src.W₂ →
    src.X₁≤Z^L → src.X₂≤Z^L → src.Y₁≤Z^L → src.Y₂≤Z^L →
    ∀Mdecl Mwidth θclip ell:ℝ,0≤θclip → Mdecl≤A →
    length Z src.X₁+length Z src.X₂+6*κ*(∑i,w i)≤Mdecl →
    Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ)≤Mdecl →
    Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ)≤Mwidth →
    Mwidth-sigma/2≤Mcap →
    Real.logb Z (max 1 b*max 1 b)≤2*θclip →
    a0≤CenteredMomentSecondInputCapacitySource.lowerFactor N lower a →
    Real.logb Z (volume src)≤5*Mdecl/6 →
    (∀j:Fin 4,
      CenteredMomentEnergyFirstGaussianProfileWeights.losses εsrc δsrc θsrc (readyBudget A Pcap) j+
      lossVector sigma (frequencyLoss Z 32 ξ) reserve
        ((readyBudget A Pcap+readyBudget A Pcap)*εmask+εchild+εremove+
          (frequencyLoss Z 32 ξ+reserve+θsource)/6+θclip/3+κ*mesh)
        εsrc A saving j + εsrc*(A+1)+primeLoss ≤ ell) →
    CenteredMomentFirstSourceReduction.physicalMass src R0 seed0 fixedBadMask 1 (Ψ Aorig) K Z ξ /
      volume src ≤ Cphysical*(C₀+C₁+1)*(p.control Uprofile)^2*
        (1+|src.t|+height)^Jheight*Z^(Mdecl+ell+εphysical)/(seed0.absNorm:ℝ) := by
  obtain ⟨UL,JL,hleft⟩:=CenteredMomentEnergyCanonicalLowSource.actual_original_left_low_column
    (α:=α) M H hH Wslot aslot bslot Mcap Lslot εremove lo hi κ a b Mslot εmask
    hMslot hεmask haPlain hbPlain L hL degree S ha hWs hW hMcap hLs hε hκsmall hbeta hκ
    N lower upper a0 θsource hlower hupper ha0 hθsource lows highs hhighs
    εsrc δsrc θsrc Bseed ξ saving hεsrc hδsrc hθsrc hξ sigma hsigma hξsmall
    A Pcap eta primeLoss reserve hA hPcap heta hPrimeLoss hsigma1 hξ1 hreserve heps1 hBseed
  obtain ⟨UR,JR,hright⟩:=CenteredMomentEnergyCanonicalRightSourceColumn.actual_original_right_low_column
    (α:=α) M H hH Wslot aslot bslot Mcap Lslot εremove lo hi κ a b Mslot εmask
    hMslot hεmask haPlain hbPlain L hL degree S ha hWs hW hMcap hLs hε hκsmall hbeta hκ
    N lower upper a0 θsource hlower hupper ha0 hθsource lows highs hhighs
    εsrc δsrc θsrc Bseed ξ saving hεsrc hδsrc hθsrc hξ sigma hsigma hξsmall
    A Pcap eta primeLoss reserve hA hPcap heta hPrimeLoss hsigma1 hξ1 hreserve heps1 hBseed
  have hphysical (T:Finset α):=CenteredMomentEnergyFirstPhysicalNormalization.actual_physical_mass_of_columnBounds
    (ι:=T) (Ψ T) JL JR (fun i=>|highs i.val|) (max 1 b) (max 1 b) A ξ εphysical
    lowerProduct hA hξ.le hεphysical hlowerProduct
  choose Cp hCp hp using hphysical
  let Cmass:ℝ:=1+∑T:Finset α,Cp T
  have hCmass:0<Cmass:=by
    have hh:=Finset.sum_nonneg (fun T (_:T∈(Finset.univ:Finset (Finset α)))=>(hCp T).le)
    dsimp [Cmass];linarith
  have hCpCap (T:Finset α):Cp T≤Cmass:=by
    have hh:=Finset.single_le_sum (fun T (_:T∈(Finset.univ:Finset (Finset α)))=>(hCp T).le)
      (Finset.mem_univ T)
    dsimp [Cmass];linarith
  refine ⟨UL∪UR,2*(JL+JR),?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨CL,hCL,ZL,hZL,hleft⟩:=hleft η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨CR,hCR,ZR,hZR,hright⟩:=hright η₀ Q hQM hQ0 hQt hQ72
  have hmL:=CenteredMomentSecondWindowBudget.profileMoment_nonneg JL
  have hmR:=CenteredMomentSecondWindowBudget.profileMoment_nonneg JR
  let Cm:ℝ:=Cmass*(CL+CR)*(1+CenteredMomentSecondWindowBudget.profileMoment JL)*
    (1+CenteredMomentSecondWindowBudget.profileMoment JR)
  have hCm:0<Cm:=by dsimp [Cm];positivity
  have hall:∀ᶠZ:ℝ in atTop,∀T:Finset α,_:=Filter.eventually_all.mpr hp
  obtain ⟨Zp,hZp⟩:=Filter.eventually_atTop.mp hall
  refine ⟨Cm,hCm,max Zp (max ZL ZR),lt_of_lt_of_le hZL
    ((le_max_left _ _).trans (le_max_right _ _)),?_⟩
  intro T θ Z hZZ εchild C₀ C₁ hC₀ hC₁ hzero hpos w σ freq height mesh hmesh hw hwm hweta hwL
    hσlo hσhi hheight hfreq src hmatch hhi hMs hloSrc hhiSrc hcard hlowerSrc hupperSrc
    hb1 hb2 hb1max hb2max hprod R0 seed0 hR0 hRcap hseed0 hseed00 K hK1 p hp₁ hp₂
    hX₁ hX₂ hY₁ hY₂ Mdecl Mwidth θclip ell hθclip hMA hcap hMdecl hMwidth hdrop
    hclip hsourceLower hlow hfit
  have hZL':ZL≤Z:=(le_max_left _ _).trans ((le_max_right _ _).trans hZZ)
  have hZR':ZR≤Z:=(le_max_right _ _).trans ((le_max_right _ _).trans hZZ)
  have hZ:1<Z:=hZL.trans_le hZL'
  have hz:0<Z:=zero_lt_one.trans hZ
  have hK:0<K:=zero_lt_one.trans_le hK1
  have hPs:∀i,1≤src.P i:=by
    intro i;rw [hmatch.scale];exact Real.one_le_rpow hZ.le (hw i)
  have hV:volume src≤Z^A:=original_volume_cap src Z κ A hZ hκsmall hPs (by
    have hh:=hcap.trans hMA
    simpa only [hmatch.scale,Real.logb_rpow hz hZ.ne'] using hh)
  have hKi:K⁻¹≤Z^A:=(inv_le_one_of_one_le₀ hK1).trans (Real.one_le_rpow hZ.le hA)
  have hs₁:∀x,src.W₁ x≠0→a≤x:=by
    intro x hx;rw [←hp₁] at hx;exact (p.support 0 hx).1
  have hs₂:∀x,src.W₂ x≠0→a≤x:=by
    intro x hx;rw [←hp₂] at hx;exact (p.support 1 hx).1
  let delta:=frequencyLoss Z 32 ξ
  let paid:=(readyBudget A Pcap+readyBudget A Pcap)*εmask+εchild+εremove+
    (delta+reserve+θsource)/6+θclip/3+κ*mesh
  let powers:Fin 4→ℝ:=fun j=>
    CenteredMomentEnergyFirstGaussianProfileWeights.losses εsrc δsrc θsrc (readyBudget A Pcap) j+
      lossVector sigma delta reserve paid εsrc A saving j
  let deficit:=Mdecl-(Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ))
  let base:=εsrc*(A+1)+primeLoss
  let FL:=CL*(C₀+C₁+1)*(p.control UL)^2*(1+height)^JL
  let FR:=CR*(C₀+C₁+1)*(p.control UR)^2*(1+height)^JR
  let Fcap:ℝ:=(CL+CR)*(C₀+C₁+1)*(p.control (UL∪UR))^2*(1+height)^(JL+JR)
  let frontL:=FL*Z^(deficit+base)
  let frontR:=FR*Z^(deficit+base)
  have hfrontL:0≤frontL:=by dsimp [frontL,FL];positivity
  have hfrontR:0≤frontR:=by dsimp [frontR,FR];positivity
  have hFcap:0≤Fcap:=by dsimp [Fcap];positivity
  have hcontrol (S₁:Finset (ℕ×ℕ))(hs:S₁⊆UL∪UR):p.control S₁≤p.control (UL∪UR):=by
    unfold Profiles.control
    exact mul_le_mul
      (Seminorm.le_def.mp (Finset.sup_mono hs) (p.profile 0))
      (Seminorm.le_def.mp (Finset.sup_mono hs) (p.profile 1))
      (sourceControl_nonneg _ _) (sourceControl_nonneg _ _)
  have hFL:FL≤Fcap:=by
    dsimp [FL,Fcap]
    gcongr
    · linarith
    · exact p.control_nonneg UL
    · exact hcontrol UL Finset.subset_union_left
    · linarith
    · omega
  have hFR:FR≤Fcap:=by
    dsimp [FR,Fcap]
    gcongr
    · linarith
    · exact p.control_nonneg UR
    · exact hcontrol UR Finset.subset_union_right
    · linarith
    · omega
  have hcoeff (F:ℝ)(hF:F≤Fcap)(j:Fin 4):
      (F*Z^(deficit+base))*Z^(powers j)≤Fcap*Z^(deficit+ell):=by
    rw [mul_assoc,←Real.rpow_add hz]
    apply mul_le_mul hF (Real.rpow_le_rpow_of_exponent_le hZ.le ?_) (Real.rpow_nonneg hz.le _) hFcap
    have hh:powers j+base≤ell:=by
      dsimp [powers,base,paid,delta]
      linarith [hfit j]
    linarith
  have hcols (lab:CenteredMomentFirstNonexceptionalWeightSum.Labels src R0 seed0)
      (E:Finset (CommonIndex lab.val.1 lab.val.2))
      (n:CenteredMomentFirstReferenceSource.SourceBlocks src R0 seed0 K Z ξ lab E)
      (hne:originalBlock src R0 seed0 (Ψ T) K Z ξ lab E n≠0):
      CenteredMomentFirstReferenceEnergy.ColumnBounds src R0 seed0 Z JL JR
        (fun j=>frontL*Z^(powers j)) (fun j=>frontR*Z^(powers j)) lab E (fun i=>(n i).val):=by
    apply CenteredMomentEnergyFirstColumnPairing.column_bounds_of_reference_sums
    · intro innerL hLcap hLsq χ v
      let hs:=CenteredMomentFirstReferenceEnergy.supported src R0 seed0 lab
      let family:=fixedPair src.η lab.val.1 lab.val.2 hs.1 E χ χ
      have hh:=hleft T θ Z hZL' εchild C₀ C₁ hC₀ hC₁ hzero hpos w σ freq height mesh
        hmesh hw hwm hweta hwL hσlo hσhi hheight hfreq src hmatch hhi hMs hloSrc hhiSrc
        hcard hlowerSrc hupperSrc hb1 hb2 hb1max hb2max R0 seed0 hR0 hRcap hseed0
        lab.val.1 lab.val.2 hs.1 hs.2 lab.property E χ χ family family.left (Or.inl rfl)
        K hK1 (Ψ T) n hne innerL hLsq hLcap p hp₁ hp₂ hX₁ hX₂ hY₁ hY₂
        Mdecl Mwidth θclip hθclip hMA hcap hMdecl hMwidth hdrop hclip hsourceLower hlow v
      simpa only [frontL,FL,powers,delta,paid,deficit,base,add_assoc,family,hs,
        CenteredMomentAmplificationChildInput.volume,CenteredMomentExceptionalAmplitudePair.volume] using hh
    · intro innerL hLcap hLsq χ v
      let hs:=CenteredMomentFirstReferenceEnergy.supported src R0 seed0 lab
      let family:=fixedPair src.η lab.val.1 lab.val.2 hs.1 E χ χ
      have hh:=hright T θ Z hZR' εchild C₀ C₁ hC₀ hC₁ hzero hpos w σ freq height mesh
        hmesh hw hwm hweta hwL hσlo hσhi hheight hfreq src hmatch hhi hMs hloSrc hhiSrc
        hcard hlowerSrc hupperSrc hb1 hb2 hb1max hb2max R0 seed0 hR0 hRcap hseed0
        lab.val.1 lab.val.2 hs.1 hs.2 lab.property E χ χ family family.right rfl
        K hK1 (Ψ T) n hne innerL hLsq hLcap p hp₁ hp₂ hX₁ hX₂ hY₁ hY₂
        Mdecl Mwidth θclip hθclip hMA hcap hMdecl hMwidth hdrop hclip hsourceLower hlow v
      simpa only [frontR,FR,powers,delta,paid,deficit,base,add_assoc,family,hs,
        CenteredMomentAmplificationChildInput.volume,CenteredMomentExceptionalAmplitudePair.volume] using hh
  have hmass:=(hZp Z ((le_max_left _ _).trans hZZ) T) src R0 seed0 hseed0 hseed00
    (fun i=>by rw [hhiSrc]) (by rwa [abs_of_nonneg hb1]) (by rwa [abs_of_nonneg hb2])
    a a K haPlain haPlain hK hprod hs₁ hs₂ hV hKi Fcap Mdecl ell (fun _=>ell) (fun _=>ell)
    (fun j=>frontL*Z^(powers j)) (fun j=>frontR*Z^(powers j)) hFcap
    (fun j=>mul_nonneg hfrontL (Real.rpow_nonneg hz.le _))
    (fun j=>mul_nonneg hfrontR (Real.rpow_nonneg hz.le _))
    (hcoeff FL hFL) (hcoeff FR hFR) (fun _=>le_rfl)
    (fun _=>le_rfl) (fun lab E _ n hne=>hcols lab E n hne)
  have hconst:Cp T*(CL+CR)*CenteredMomentSecondWindowBudget.profileMoment JL*
      CenteredMomentSecondWindowBudget.profileMoment JR≤Cm:=by
    dsimp [Cm]
    gcongr
    · exact hCpCap T
    · linarith
    · linarith
  have hheightProduct:(1+height)^(JL+JR)*(1+|src.t|)^(JL+JR)≤
      (1+|src.t|+height)^(2*(JL+JR)):=by
    have heq:(1+|src.t|+height)^(2*(JL+JR))=
        (1+|src.t|+height)^(JL+JR)*(1+|src.t|+height)^(JL+JR):=by
      rw [show 2*(JL+JR)=(JL+JR)+(JL+JR) by omega]
      exact pow_add _ _ _
    rw [heq]
    apply mul_le_mul
      (pow_le_pow_left₀ (by linarith) (by linarith [abs_nonneg src.t]) _)
      (pow_le_pow_left₀ (by positivity) (by linarith) _)
      (by positivity) (by positivity)
  calc
    _ ≤ (Cp T*(CL+CR)*CenteredMomentSecondWindowBudget.profileMoment JL*
          CenteredMomentSecondWindowBudget.profileMoment JR)*(C₀+C₁+1)*
          (p.control (UL∪UR))^2*((1+height)^(JL+JR)*(1+|src.t|)^(JL+JR))*
          Z^(Mdecl+ell+εphysical)/(seed0.absNorm:ℝ) := by
      apply hmass.trans_eq
      dsimp [Fcap]
      ring
    _ ≤ _ := by gcongr

end SevenEighths.CenteredMomentEnergyCanonicalLowPhysical

end

end OAI
