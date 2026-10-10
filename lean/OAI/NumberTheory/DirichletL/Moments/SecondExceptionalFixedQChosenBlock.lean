import OAI.NumberTheory.DirichletL.Moments.SecondExceptionalSourceFamily
import OAI.NumberTheory.DirichletL.Moments.FiniteProfileExceptionalFixedQUniform
import OAI.NumberTheory.DirichletL.Moments.SecondExceptionalFamily
import OAI.NumberTheory.DirichletL.Moments.OriginalCommonHarmonic
import OAI.NumberTheory.DirichletL.Moments.SourceLowerSupport
import OAI.NumberTheory.DirichletL.Moments.FiniteProfileExceptionalPhysicalSaved
import OAI.NumberTheory.DirichletL.Moments.FiniteProfileExceptionalPhysicalBudget
import OAI.NumberTheory.DirichletL.Moments.SecondExceptionalCommonSaving
import OAI.NumberTheory.DirichletL.Moments.SecondExceptionalPhysicalSaving
import OAI.NumberTheory.DirichletL.Moments.SecondDyadicRowSupport
import OAI.NumberTheory.DirichletL.Moments.SecondPhysicalBlock
import OAI.NumberTheory.DirichletL.Moments.SecondExceptionalKernel
import OAI.NumberTheory.DirichletL.Moments.SecondDivisorSupport

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter MeasureTheory

namespace SevenEighths.CenteredMomentSecondExceptionalFixedQChosenBlock
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss UniqueFactorizationMonoid
open CenteredMomentCommonRadialData CenteredMomentCommonWindowColumn CenteredMomentReflectedSource
open CenteredMomentCommonSectorWindow CenteredMomentSecondSectorColumns
open CenteredMomentSecondScaled CenteredMomentChildAssembly CenteredMomentRowNorm
open CenteredMomentHeckeColumnWindow CenteredMomentFirstSectors CenteredMomentSourceRow
open CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentExceptionalAmplitudePair
open CenteredMomentLogDyadic RayFourExpansion CenteredMomentSmooth
open CenteredMomentCommonHeightEnvelope CenteredMomentCommonExceptionalCost
open CenteredMomentExceptionalSourceShell CenteredMomentExceptionalHeight CenteredMomentSecondHeightFamily
open CenteredMomentSecondExceptionalPairBound
open CenteredMomentFiniteProfileExceptional CenteredMomentFiniteProfileExceptionalCommon
open CenteredMomentSecondExceptionalKernel CenteredMomentSecondCanonical
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonicalFrequency
open CenteredMomentSecondCanonicalNonunit CenteredMomentForcing CenteredMomentChildRows
open CenteredMomentSecondPhysicalBlock
open CenteredMomentSecondWholeKernel CenteredMomentSectorLocalization
open CenteredMomentSecondDyadicRowSupport

open CenteredMomentSecondExceptionalPhysicalSaving CenteredMomentRankinRadical
open CenteredMomentSecondExceptionalCommonSaving
open ConcretePrimeRowBridge CenteredMomentMobiusRegroup CenteredMomentSupportedCorrelation
open CenteredMomentSupport CenteredMomentSecondCanonicalScalar CenteredMomentSecondDivisorSupport
local notation "O" => HeckeFamily.O
local instance {ι:Type*}:DecidableEq (ι⊕Fin 2):=Classical.decEq _
universe u
variable {ι:Type u}[Fintype ι][DecidableEq ι]

open CenteredMomentSecondExceptionalFamily CenteredMomentSecondExceptionalSourceFamily
open CenteredMomentSecondEnergySplit CenteredMomentSecondLiveBlock
open CenteredMomentOriginalCommonHarmonic CenteredMomentSourceLowerSupport
open CenteredMomentFiniteProfileExceptionalPhysical

theorem chosen_exceptional_block (wlo whi:ℝ)(hwlo:0<wlo)(hwhi:0≤whi)(lo hi:ι→ℝ)(W:𝓢(ℝ,ℂ))
    (ε δ θ B Lbound:ℝ)(hε:0<ε)(hδ:0<δ)(hθ:0<θ)(hB:0≤B)(hL:0≤Lbound):
    ∃J:ℕ,∃Sprofile:Finset (ℕ×ℕ),(0,0)∈Sprofile ∧ ∃Ck:ℝ,0≤Ck ∧
      ∀Q:Ideal O,Q≠0 → Q≠⊤ → Q≤Ideal.span {(72:O)} →
      ∃K:ℝ,0<K ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
      ∀(s:Input ι)(p:Profiles wlo whi),(∀i,s.lo i=lo i) → (∀i,s.hi i=hi i) →
      (∀i,1≤s.P i) → s.W₁=p.profile 0 → s.W₂=p.profile 1 →
      ∀(C D:Ideal O)(hC:Supported C)(hD:Supported D)(R0 seed:Ideal O),
      R0≠0 → seed∣C → seed∣D → (C.absNorm:ℝ)≤Z^B → (D.absNorm:ℝ)≤Z^B →
      primeSupport C=primeSupport D → ∀U:Finset (CommonIndex C D),
      ∀r:ℝ,Z^r≤s.X₁ → Z^r≤s.X₂ → Z^r≤s.Y₁ → Z^r≤s.Y₂ →
      ∀χ₀:RayCharacter,idealCoeff s.η C≠0 →
      ∀m:O,m≠0 → goodLambda∣m → (2:O)∣m →
      sourceRadius s≤Z^Lbound → ∀(R Kphys:ℝ),0<Kphys →
      (expandedFactor s.η:ℝ)*R0.absNorm*C.absNorm*D.absNorm*(4*R)≤Z^B →
      ∀n:Fin 4→ℤ,
      ‖physicalBlock s.η s.t (finiteColumns (Fintype.piFinset s.pools))
        (coefficient s R0 seed) C D hC hD U R
        (partRows true s.η χ₀ Q m C D U R) W Kphys n‖/volume s.toData≤
        Ck*(profileFactor Sprofile s p J Q K*
          Z^(2*ε+δ+2*B*θ-2*max r 0/3)*
          (volume s.toData)^(1/3:ℝ)*Kphys^(5/6:ℝ)*((∏i,s.lo i)*wlo*wlo)^(-2/3:ℝ)/
          (Ideal.absNorm (commonRadical C D):ℝ)):=by
  obtain ⟨J,Sprofile,hSp,Ck,hCk,hbound⟩:=
    CenteredMomentFiniteProfileExceptionalFixedQ.actual_uniform_exceptional_block
      wlo whi hwlo hwhi lo hi W ε δ θ B Lbound hε hδ hθ hB hL
  refine ⟨J,Sprofile,hSp,Ck,hCk,?_⟩
  intro Q hQ hQt hQ72
  obtain ⟨K,hK,hbound⟩:=hbound Q hQ hQt hQ72
  refine ⟨K,hK,?_⟩
  filter_upwards [hbound] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro s p hlo hhi hP hW1 hW2 C D hC hD R0 seed hR0 hsC hsD hNC hND hCD U
    r hX1 hX2 hY1 hY2 χ₀ hη m hm hml hm2 hsource R Kphys hKphys hcond n
  let S:=finiteColumns (Fintype.piFinset s.pools)
  let β:=coefficient s R0 seed
  let rows:=partRows true s.η χ₀ Q m C D U R
  have hn:∀z∈rows,z≠0:=exceptional_part_nonzero s.η χ₀ Q m C D U R
  have hex:=exceptional_part_inducing s.η χ₀ Q m C D U R
  have hprofile0 (i:Fin 2):p.profile i 0=0:=by
    by_contra hh
    have hp:=(p.support i hh).1
    linarith
  have hz1:s.W₁ 0=0:=by rw [hW1];exact hprofile0 0
  have hz2:s.W₂ 0=0:=by rw [hW2];exact hprofile0 1
  have hβ:∀I:Ideal O,β I≠0→(I.absNorm:ℝ)≤sourceRadius s:=
    fun I hI=>(original_column_norm s R0 seed I hz1 hz2 hI).2
  have hD1:1≤(D.absNorm:ℝ):=by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hD.1)
  have hHD:sourceRadius s/(D.absNorm:ℝ)≤Z^Lbound:=by
    by_cases hh:0≤sourceRadius s
    · exact (div_le_self hh hD1).trans hsource
    · exact (div_nonpos_of_nonpos_of_nonneg (le_of_not_ge hh) (Nat.cast_nonneg _)).trans
        (Real.rpow_nonneg (zero_lt_one.trans hZ.1).le _)
  have ha:0<(∏i,s.lo i)*wlo*wlo:=
    mul_pos (mul_pos (Finset.prod_pos (fun i _=>s.lo_pos i)) hwlo) hwlo
  have hlower (I:Ideal O)(hI:β I≠0):
      ((∏i,s.lo i)*wlo*wlo)*volume s.toData≤(I.absNorm:ℝ):=by
    have hh:=profile_column_lower R0 s.ν s.W s.P s.lo s.W₁ s.W₂ wlo wlo
      s.X₁ s.X₂ s.Y₁ s.Y₂ (s.X₁*s.X₂) 1 1 seed s.P_pos (fun i=>(s.lo_pos i).le)
      hwlo.le hwlo.le s.X₁_pos s.X₂_pos s.Y₁_pos s.Y₂_pos one_ne_zero one_ne_zero rfl s.same_product
      (fun i x hx=>(s.support i hx).1)
      (fun x hx=>(p.support 0 (by rwa [hW1] at hx)).1)
      (fun x hx=>(p.support 1 (by rwa [hW2] at hx)).1)
      (Fintype.piFinset s.pools) I hI
    simpa only [CenteredMomentExceptionalAmplitudePair.volume,map_one,Nat.cast_one,mul_one,div_one,mul_assoc] using hh
  by_cases hzero:physicalBlock s.η s.t S β C D hC hD U R rows W Kphys n=0
  · rw [hzero,norm_zero,zero_div]
    have hp:=profileFactor_nonneg Sprofile s p J Q K hK.le
    have hv:=volume_pos s.toData
    have hZpos:0<Z:=zero_lt_one.trans hZ.1
    exact mul_nonneg hCk (div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg
      (mul_nonneg hp (Real.rpow_nonneg hZpos.le _)) (Real.rpow_nonneg hv.le _))
      (Real.rpow_nonneg hKphys.le _)) (Real.rpow_nonneg ha.le _)) (Nat.cast_nonneg _))
  obtain ⟨τ,hτ⟩:=exists_exceptional_family s.η C D hC hD hCD U
  have he:=actual_family_both_rows s.η χ₀ Q hQ72 m hm hml hm2 C D hC hD U τ hτ R
  have hc (χ ξ:RayCharacter)(z:O)(hz:z∈rows):
      (expandedConductor (τ χ) R0 C z:ℝ)≤Z^B ∧
      (expandedConductor (reflected (τ ξ)) R0 D z:ℝ)≤Z^B:=by
    have hg:=expanded_conductor_bounds hτ hCD s.t S β R rows W Kphys hKphys n hzero χ ξ R0 z
    have hzlive:z∈liveRows C D U R rows:=by
      rw [show liveRows C D U R rows=rows from exceptional_part_live s.η χ₀ Q m C D U R]
      exact hz
    have hzN:=live_norm_le_four_radius C D U R rows z hzlive
    have hb:(expandedFactor s.η:ℝ)*R0.absNorm*C.absNorm*D.absNorm*(Ideal.span {z}).absNorm≤Z^B:=by
      apply le_trans _ hcond
      exact mul_le_mul_of_nonneg_left hzN (by positivity)
    constructor
    · exact (show (expandedConductor (τ χ) R0 C z:ℝ)≤
        (expandedFactor s.η:ℝ)*R0.absNorm*C.absNorm*D.absNorm*(Ideal.span {z}).absNorm by
        exact_mod_cast hg.1).trans hb
    · exact (show (expandedConductor (reflected (τ ξ)) R0 D z:ℝ)≤
        (expandedFactor s.η:ℝ)*R0.absNorm*C.absNorm*D.absNorm*(Ideal.span {z}).absNorm by
        exact_mod_cast hg.2).trans hb
  exact hZ.2 s p hlo hhi hP hW1 hW2 C D hC hD R0 seed hR0 hsC hsD hNC hND hCD U
    r hX1 hX2 hY1 hY2 τ hτ.height_eq rows hn he.1 he.2
    (fun χ z hz=>by simpa only [expandedConductor,Nat.cast_mul] using (hc χ χ z hz).1)
    (fun χ z hz=>by simpa only [expandedConductor,Nat.cast_mul] using (hc χ χ z hz).2)
    χ₀ hη m hm hml hm2 hex (sourceRadius s) hβ hHD
    ((∏i,s.lo i)*wlo*wlo) ha hlower R Kphys hKphys n

end SevenEighths.CenteredMomentSecondExceptionalFixedQChosenBlock

end

end OAI
