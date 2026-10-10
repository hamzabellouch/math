import OAI.NumberTheory.DirichletL.Moments.SecondExceptionalUniformSource
import OAI.NumberTheory.DirichletL.Moments.SecondSourceDiagonal
import OAI.NumberTheory.DirichletL.Moments.SourceInputTailUniform
import OAI.NumberTheory.DirichletL.Moments.SecondLocalization
import OAI.NumberTheory.DirichletL.Moments.SecondExceptionalFixedQSource
import OAI.NumberTheory.DirichletL.Moments.SecondExceptionalSourceCaps
import OAI.NumberTheory.DirichletL.Moments.SecondExceptionalFixedQChosenBlock
import OAI.NumberTheory.DirichletL.Moments.SecondExceptionalAggregate
import OAI.NumberTheory.DirichletL.Moments.SecondExceptionalSourceFamily
import OAI.NumberTheory.DirichletL.Moments.FiniteProfileExceptionalPhysicalUniform
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

namespace SevenEighths.CenteredMomentSecondSourceRemainder
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

open CenteredMomentSecondExceptionalFixedQChosenBlock CenteredMomentSecondExceptionalAggregate
open CenteredMomentSecondBlockRadicalHarmonicMass CenteredMomentSecondActivePhysicalDictionary
open CenteredMomentSecondRetainedAggregate
open CenteredMomentActiveSource

open CenteredMomentOriginalChildEnergy CenteredMomentSecondLocalization
open CenteredMomentSourceSecondZeroEnergy CenteredMomentSourceInputTailUniform
open CenteredMomentSupportedTailAggregate EisensteinSchwartzPoisson

theorem original_source_remainder (wlo whi:ℝ)(hwlo:0<wlo)(hwhi:0≤whi)
    (lo hi:ι→ℝ)(hhi:∀i,0≤hi i)(W:𝓢(ℝ,ℂ))
    (ε δ θ B ξ saving:ℝ)(hε:0<ε)(hδ:0<δ)(hθ:0<θ)(hB:0≤B)(hξ:0<ξ):
    ∃J:ℕ,∃Sprofile SΦ:Finset (ℕ×ℕ),(0,0)∈Sprofile ∧
      ∃Cexc Cdiag Ctail:ℝ,0≤Cexc ∧ 0<Cdiag ∧ 0<Ctail ∧
      ∀Q:Ideal O,Q≠0 → Q≠⊤ → Q≤Ideal.span {(72:O)} →
      ∃Kc:ℝ,0<Kc ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
      ∀(s:Input ι)(p:Profiles wlo whi),(∀i,s.lo i=lo i) → (∀i,s.hi i=hi i) →
      (∀i,1≤s.P i) → s.W₁=p.profile 0 → s.W₂=p.profile 1 →
      ∀(R0 seed:Ideal O),R0≠0 → Squarefree seed → seed≠0 →
      0≤sourceRadius s → sourceRadius s≤Z^B →
      (s.η.modulus.absNorm:ℝ)≤Z^B → (R0.absNorm:ℝ)≤Z^B →
      let S:=finiteColumns (Fintype.piFinset s.pools)
      let β:=coefficient s R0 seed
      ∀χ₀:RayCharacter,∀m:O,m≠0 → goodLambda∣m → (2:O)∣m →
      ∀(Tsec Kphys:ℝ),0<Kphys → volume s.toData≤Z^B → Tsec≤Z^B →
      (volume s.toData)^2/Kphys≤Tsec →
      let R:=frequencyRadius Tsec Z ξ
      0<R → R≤Z^B →
      ∀r:ℝ,Z^r≤s.X₁ → Z^r≤s.X₂ → Z^r≤s.Y₁ → Z^r≤s.Y₂ →
      ‖sourceGaussEnergy S β (heightCoeff s.η s.t) W Kphys-
        partEnergy false s.η χ₀ Q m s.t S β W Kphys Tsec Z ξ (sourceRadius s)‖/volume s.toData≤
      Cdiag*Kphys*‖paperRadialFourier W 0‖*
        (2*SchwartzMap.seminorm ℝ 0 0 (p.profile 0)*SchwartzMap.seminorm ℝ 0 0 (p.profile 1)*(∏i,s.M i))^2*
        (1+(∏i,hi i)*whi*whi)^(1+ε)*(volume s.toData)^ε/(seed.absNorm:ℝ)+
      Cexc*profileFactor Sprofile s p J Q Kc*
        Z^(2*ε+2*δ+2*(5*B+1)*θ-2*max r 0/3)*
        (volume s.toData)^(1/3:ℝ)*Kphys^(5/6:ℝ)*((∏i,s.lo i)*wlo*wlo)^(-2/3:ℝ)/(seed.absNorm:ℝ)+
      Ctail*(plainControl s (p.profile 0) (p.profile 1))^2*
        SΦ.sup (schwartzSeminormFamily ℝ ℝ ℂ) W*Kphys*Z^(-saving):=by
  obtain ⟨J,Sprofile,hSp,Cexc,hCexc,hexc⟩:=
    CenteredMomentSecondExceptionalUniformSource.original_exceptional_energy
      wlo whi hwlo hwhi lo hi W ε δ θ B hε hδ hθ hB
  obtain ⟨Cdiag,hCdiag,hdiag⟩:=CenteredMomentSecondSourceDiagonal.actual_second_zero (Fintype.card ι) ε hε
  obtain ⟨SΦ,Ctail,hCtail,htail⟩:=second_input_tail_arbitrary_saving hi wlo whi B ξ saving hhi hwlo hwhi hB hξ
  refine ⟨J,Sprofile,SΦ,hSp,Cexc,Cdiag,Ctail,hCexc,hCdiag,hCtail,?_⟩
  intro Q hQ hQt hQ72
  obtain ⟨Kc,hKc,hexc⟩:=hexc Q hQ hQt hQ72
  refine ⟨Kc,hKc,?_⟩
  filter_upwards [hexc,htail] with Z hZ htZ
  refine ⟨hZ.1,?_⟩
  intro s p hlo hhis hP hw1 hw2 R0 seed hR0 hseed hseed0 hH0 hH hη hR0N S β χ₀ m hm hml hm2
    Tsec Kphys hKphys hVcap hTcap hnom R hR hRcap r hX1 hX2 hY1 hY2
  have hz (i:Fin 2):p.profile i 0=0:=by
    by_contra hn
    exact (not_le_of_gt hwlo) (p.support i hn).1
  have hz1:s.W₁ 0=0:=by rw [hw1];exact hz 0
  have hz2:s.W₂ 0=0:=by rw [hw2];exact hz 1
  have hboundI:∀I∈S,β I≠0→(I.absNorm:ℝ)≤sourceRadius s:=
    fun I _ hn=>(original_column_norm s R0 seed I hz1 hz2 hn).2
  have he:=sourceGaussEnergy_localized s.η s.t S β W Kphys Tsec Z ξ hKphys
  rw [original_energy_split s.η χ₀ Q m s.t S β W Kphys Tsec Z ξ (sourceRadius s) hKphys hboundI] at he
  have hrem:sourceGaussEnergy S β (heightCoeff s.η s.t) W Kphys-
      partEnergy false s.η χ₀ Q m s.t S β W Kphys Tsec Z ξ (sourceRadius s)=
      ((Kphys:ℂ)*paperRadialFourier W 0)*sourceSecondZero S β s.η s.t+
      partEnergy true s.η χ₀ Q m s.t S β W Kphys Tsec Z ξ (sourceRadius s)+
      secondDiscardedEnergy s.η s.t S β W Kphys Tsec Z ξ:=by rw [he];ring
  have hd:=hdiag (ι:=ι) le_rfl wlo whi hwlo hwhi s p hw1 hw2 R0 seed hseed0
    ((Kphys:ℂ)*paperRadialFourier W 0)
  simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hKphys] at hd
  have hhiEq:(∏i,max 0 (s.hi i))=∏i,hi i:=by
    apply Finset.prod_congr rfl
    intro i _
    rw [hhis i,max_eq_right (hhi i)]
  rw [hhiEq] at hd
  have hex:=hZ.2 s p hlo hhis hP hw1 hw2 R0 seed hR0 hseed hseed0 hH0 hH hη hR0N
    χ₀ m hm hml hm2 Tsec ξ Kphys hKphys hR hRcap r hX1 hX2 hY1 hY2
  have ht:=htZ.2 s (p.profile 0) (p.profile 1) hw1 hw2 (p.support 0) (p.support 1)
    (fun i=>(hhis i).le) R0 seed W Kphys Tsec hKphys hVcap hTcap hnom
  rw [hrem]
  calc
    _≤(‖((Kphys:ℂ)*paperRadialFourier W 0)*sourceSecondZero S β s.η s.t‖+
      ‖partEnergy true s.η χ₀ Q m s.t S β W Kphys Tsec Z ξ (sourceRadius s)‖+
      ‖secondDiscardedEnergy s.η s.t S β W Kphys Tsec Z ξ‖)/volume s.toData:=by
      exact div_le_div_of_nonneg_right ((norm_add_le _ _).trans
        (add_le_add (norm_add_le _ _) le_rfl)) (CenteredMomentExceptionalAmplitudePair.volume_pos s.toData).le
    _=_:=by rw [add_div,add_div]
    _≤_:=by
      apply add_le_add (add_le_add _ hex) ht
      simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hKphys]
      convert hd using 1 ; ring

end SevenEighths.CenteredMomentSecondSourceRemainder

end

end OAI
