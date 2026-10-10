import OAI.NumberTheory.DirichletL.Moments.FirstReferenceSource
import OAI.NumberTheory.DirichletL.Moments.FirstPhysicalOriginalMask
import OAI.NumberTheory.DirichletL.Moments.FirstPhysicalZeroRadius

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentFirstReferenceEnergy
open HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge CompletedGauss RayFourExpansion
open CenteredMomentCommonRadialData CenteredMomentOriginalCommonHarmonic
open CenteredMomentFirstReferenceSource CenteredMomentFirstReferenceBlock
open CenteredMomentFirstPhysicalSource CenteredMomentFirstPhysicalDyadicAssembly
open CenteredMomentFirstNonexceptionalWeightSum CenteredMomentFirstNonexceptionalLocalWeightSum
open CenteredMomentFirstSourceReduction CenteredMomentFirstInactiveRadicalMass
open CenteredMomentSecondRetainedAggregate CenteredMomentActiveSource CenteredMomentSourceRow
open CenteredMomentSourceMass CenteredMomentCanonicalFirst CenteredMomentFirstSectors
open CenteredMomentSecondRetainedRows CenteredMomentSectorLocalization CenteredMomentLogDyadic
open CenteredMomentExceptionalAmplitudePair CenteredMomentRankinRadical
open CenteredMomentAmplificationChildInput CenteredMomentGaussEnergy CenteredMomentChildAssembly
open CenteredMomentCommonSupport CenteredMomentMobiusRegroup CenteredMomentFirstCanonicalFamily
open CenteredMomentFirstMixedAllowance CenteredMomentSecondWindowBudget CenteredMomentSecondHeightFamily
local notation "O"=>HeckeFamily.O
variable {ι:Type*}[Fintype ι][DecidableEq ι]
local instance : DecidableEq (ι⊕Fin 2):=Classical.decEq _

abbrev supported (s:Input ι)(R seed:Ideal O)(p:Labels s R seed):=
  commonLabels_supported (activeSource (finiteColumns (Fintype.piFinset s.pools))
    (CenteredMomentOriginalCommonHarmonic.coefficient s R seed)) _ _ p.property

def ColumnBounds (s:Input ι)(R seed:Ideal O)(Z:ℝ)(J₁ J₂:ℕ)(EL ER:Fin 4→ℝ)
    (p:Labels s R seed)(E:Finset (CommonIndex p.val.1 p.val.2))(n:Fin 4→ℤ):Prop:=
  let C:=p.val.1; let D:=p.val.2; let h:=supported s R seed p
  let F:=fixedPair s.η C D h.1 E 1 1
  let V:=volume s.toData
  let refL:=(F.left.modulus.absNorm:ℝ)*(V/(C.absNorm:ℝ))^2*Z^(allowance C D Z)
  let refR:=(F.right.modulus.absNorm:ℝ)*(V/(D.absNorm:ℝ))^2*Z^(allowance D C Z)
  (∀L∈divisorPool (Finset.univ:Finset (columns C D h.2.1 (original s R seed).columns))
    (fun b=>Ideal.span {element C D h.2.1 (original s R seed).columns b}),
    (L.absNorm:ℝ)≤sourceRadius s/(D.absNorm:ℝ)→Squarefree L→∀χ:RayCharacter,∀v:ℝ,
    (commonEnergy (original s R seed) C h.1 (fixedPair s.η C D h.1 E χ χ).left v L
      CenteredMomentFirstAnnularMajorant.profile (dyadicScale (n 1))).re≤
      ((∑i,refL*EL i)/(L.absNorm:ℝ))*(1+‖v‖)^(2*J₁)) ∧
  (∀L∈divisorPool (Finset.univ:Finset (columns C D h.2.1 (original s R seed).columns))
    (fun b=>Ideal.span {element C D h.2.1 (original s R seed).columns b}),
    (L.absNorm:ℝ)≤sourceRadius s/(D.absNorm:ℝ)→Squarefree L→∀χ:RayCharacter,∀v:ℝ,
    (commonEnergy (original s R seed) D h.2 (fixedPair s.η C D h.1 E χ χ).right v L
      CenteredMomentFirstAnnularMajorant.profile (dyadicScale (n 1))).re≤
      ((∑i,refR*ER i)/(L.absNorm:ℝ))*(1+‖v‖)^(2*J₂))

def pairedBudget (J₁ J₂:ℕ)(t:ℝ)(EL ER:Fin 4→ℝ):ℝ:=
  ∑i:Fin 4,∑j:Fin 4,windowBudget J₁ t (EL i)*windowBudget J₂ t (ER j)
lemma pairedBudget_nonneg (J₁ J₂:ℕ)(t:ℝ)(EL ER:Fin 4→ℝ):0≤pairedBudget J₁ J₂ t EL ER:=
  Finset.sum_nonneg (fun _i _=>Finset.sum_nonneg (fun _j _=>mul_nonneg
    (windowBudget_nonneg _ _ _) (windowBudget_nonneg _ _ _)))

def sourceFactor (s:Input ι)(a₁ a₂ K:ℝ):ℝ:=
  (Real.exp (Real.log 4)/((∏i,s.lo i)*a₁*a₂))*fixedPresentationCost*K*(s.η.modulus.absNorm:ℝ)
omit [DecidableEq ι] in
lemma sourceFactor_nonneg (s:Input ι)(a₁ a₂ K:ℝ)(ha₁:0<a₁)(ha₂:0<a₂)(hK:0<K):
    0≤sourceFactor s a₁ a₂ K:=by
  have hlo:0<∏i,s.lo i:=Finset.prod_pos (fun i _=>s.lo_pos i)
  have hf:=fixedPresentationCost_pos
  unfold sourceFactor
  positivity

theorem actual_physical_mass (W:𝓢(ℝ,ℂ))(J₁ J₂:ℕ)(hi:ι→ℝ)(b₁ b₂ B ξ ε:ℝ)
    (hB:0≤B)(hξ:0≤ξ)(hε:0<ε):
    ∃C:ℝ,0<C ∧ ∀ᶠZ:ℝ in atTop,∀s:Input ι,∀R seed:Ideal O,
      Squarefree seed→seed≠0→(∀i,|s.hi i|≤hi i)→|s.b₁|≤b₁→|s.b₂|≤b₂→
      ∀a₁ a₂ K:ℝ,0<a₁→0<a₂→0<K→
      (∀x,s.W₁ x≠0→a₁≤x)→(∀x,s.W₂ x≠0→a₂≤x)→
      volume s.toData≤Z^B→K⁻¹≤Z^B→∀EL ER:Fin 4→ℝ,(∀i,0≤EL i)→(∀i,0≤ER i)→
      (∀p:Labels s R seed,∀E∈CenteredMomentFirstDiscardedEnergy.inactiveSubsets p.val.1 p.val.2,
        ∀n:SourceBlocks s R seed K Z ξ p E,
        CenteredMomentFirstReferenceSource.originalBlock s R seed W K Z ξ p E n≠0→ColumnBounds s R seed Z J₁ J₂ EL ER p E (fun i => (n i).val))→
      physicalMass s R seed fixedBadMask 1 W K Z ξ/volume s.toData≤
        C*Z^ε/(seed.absNorm:ℝ)*sourceFactor s a₁ a₂ K*pairedBudget J₁ J₂ s.t EL ER:=by
  obtain ⟨Cs,hCs,hsum⟩:=original_block_sum hi b₁ b₂ B ξ (ε/2) hB hξ (by linarith)
  obtain ⟨Cb,hCb,hblock⟩:=actual_reference_block W 0 J₁ J₂ (B+1) (ε/2) (by linarith) (by linarith)
  refine ⟨Cs*Cb,mul_pos hCs hCb,?_⟩
  filter_upwards [hsum,hblock,eventually_ge_atTop ((∏i,hi i)*b₁*b₂)] with Z hsum hblock hfixed
  intro s R seed hseed hseed0 hhi hb₁ hb₂ a₁ a₂ K ha₁ ha₂ hK hs₁ hs₂ hV hKi EL ER hEL hER hcol
  have hz₁:s.W₁ 0=0:=by by_contra hn;have hh:=hs₁ 0 hn;linarith
  have hz₂:s.W₂ 0=0:=by by_contra hn;have hh:=hs₂ 0 hn;linarith
  by_cases hH:0<sourceRadius s
  case neg =>
    rw [CenteredMomentFirstPhysicalZeroRadius.physicalMass_zero s R seed hz₁ hz₂ (le_of_not_gt hH)]
    simp only [zero_div]
    have hsF:=sourceFactor_nonneg s a₁ a₂ K ha₁ ha₂ hK
    have hsP:=pairedBudget_nonneg J₁ J₂ s.t EL ER
    have hZpos:0<Z:=zero_lt_one.trans hblock.1
    positivity
  let A:=Cb*Z^(ε/2)*sourceFactor s a₁ a₂ K*pairedBudget J₁ J₂ s.t EL ER
  have hA:0≤A:=mul_nonneg (mul_nonneg (mul_nonneg hCb.le (Real.rpow_nonneg (by linarith [hblock.1]) _))
    (sourceFactor_nonneg s a₁ a₂ K ha₁ ha₂ hK)) (pairedBudget_nonneg _ _ _ _ _)
  have hcap:=CenteredMomentFirstPhysicalDyadicCount.input_radius_cap hi b₁ b₂ B Z s hhi hb₁ hb₂ hblock.1.le hfixed hV
  have hpblock (p:Labels s R seed)(E:Finset (CommonIndex p.val.1 p.val.2))
      (hE:E∈CenteredMomentFirstDiscardedEnergy.inactiveSubsets p.val.1 p.val.2)
      (n:SourceBlocks s R seed K Z ξ p E):
      ‖CenteredMomentFirstReferenceSource.originalBlock s R seed W K Z ξ p E n‖/volume s.toData≤A*radicalWeight s R seed p E:=by
    by_cases hne:CenteredMomentFirstReferenceSource.originalBlock s R seed W K Z ξ p E n=0
    · rw [hne,norm_zero,zero_div]
      exact mul_nonneg hA (radicalWeight_nonneg s R seed p E)
    have hp:=supported s R seed p
    have hg:=actual_common_gates s R seed hseed hz₁ hz₂ p.val.1 p.val.2 p.property
    have hND:1≤(p.val.2.absNorm:ℝ):=by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hp.2.1)
    have hcapD:sourceRadius s/(p.val.2.absNorm:ℝ)≤Z^(B+1):=
      (div_le_self hH.le hND).trans hcap
    have hh:=hblock.2 s R seed a₁ a₂ ha₁ ha₂ hs₁ hs₂ p.val.1 p.val.2 hp.1 hp.2 hg.2.2.1 E 1 1
      (fixedPair s.η p.val.1 p.val.2 hp.1 E 1 1) (retainedRows (localRadius s R seed K Z ξ p E) 1)
      K hK (fun i => (n i).val) hcapD EL ER hEL hER (hcol p E hE n hne).1 (hcol p E hE n hne).2
    simp only [pow_zero,one_mul] at hh
    convert hh using 1 <;>
      simp only [CenteredMomentFirstReferenceSource.originalBlock,A,sourceFactor,pairedBudget,radicalWeight,
        CenteredMomentFirstInactiveRadicalMass.inactiveWeight,Real.rpow_zero,div_one,
        CenteredMomentFirstPhysicalSource.inactiveWeight, CenteredMomentAmplificationChildInput.original,
        CenteredMomentFirstAmplificationChoice.OriginalData.columns,
        CenteredMomentFirstAmplificationChoice.OriginalData.beta,
        CenteredMomentFirstAmplificationChoice.OriginalData.profile,
        CenteredMomentOriginalCommonHarmonic.coefficient,
        CenteredMomentAmplificationChildInput.volume,
        CenteredMomentExceptionalAmplitudePair.volume] ; ring
  have hh:=hsum s R seed hseed hseed0 hz₁ hz₂ hhi hb₁ hb₂ hH W K A hK hA hV hKi hpblock
  rw [CenteredMomentFirstPhysicalOriginalMask.original_physicalMass] at hh
  calc
    _≤_:=hh
    _=_:=by
      rw [show Z^ε=Z^(ε/2)*Z^(ε/2) by rw [←Real.rpow_add (by linarith [hblock.1]:0<Z)];congr 1;ring]
      dsimp [A]
      ring

end SevenEighths.CenteredMomentFirstReferenceEnergy

end

end OAI
