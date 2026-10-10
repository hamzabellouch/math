import OAI.NumberTheory.DirichletL.Moments.FirstCommonTransport

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentFirstCommonFourierTransport
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge CanonicalQuadraticSieve
open CenteredMomentCanonicalFirst CenteredMomentCompleteCommon CenteredMomentFirstReduced
open CenteredMomentSupportedCorrelation
open CenteredMomentCommonSupport CenteredMomentFirstLocalization CenteredMomentFirstScale
open CenteredMomentSectorLocalization CenteredMomentFirstCommonTransport
local notation "O"=>ActualEisensteinCubic.O

theorem quotient_function_heq (r r':O)(hr:r'=r)
    (G:Residue r→ℂ)(G':Residue r'→ℂ)
    (hG:∀z:O,G' (Ideal.Quotient.mk _ z)=G (Ideal.Quotient.mk _ z)):
    HEq G' G:=by
  subst r'
  apply heq_of_eq
  funext x
  obtain ⟨z,rfl⟩:=Ideal.Quotient.mk_surjective x
  exact hG z

def retainedFourierTerm (a b r:O)(ha:a≠0)(hb:b≠0)(hr:r≠0)
    (χa:MulChar (Residue a) ℂ)(χb:MulChar (Residue b) ℂ)(G:Residue r→ℂ)
    (e:O)(E:Ideal O)(W:𝓢(ℝ,ℂ))(K R:ℝ):ℂ:=
  let k:=K/normValue e
  (UniqueFactorizationMonoid.moebius E:ℂ)*tripleRow a b r χa χb G e*
    (((k/normValue (a*(b*r)):ℝ):ℂ)*∑'h:O,
      (retainedWeight R (normValue h):ℂ)*tripleFourier a b r ha hb hr χa χb G h*
        EisensteinSchwartzPoisson.paperRadialFourier W ((k/normValue (a*(b*r)))*normValue h))

theorem retainedFourierTerm_transport (a b r r':O)(ha:a≠0)(hb:b≠0)(hr:r≠0)(hr':r'≠0)
    (χa:MulChar (Residue a) ℂ)(χb:MulChar (Residue b) ℂ)(G:Residue r→ℂ)(G':Residue r'→ℂ)
    (he:r'=r)(hG:∀z:O,G' (Ideal.Quotient.mk _ z)=G (Ideal.Quotient.mk _ z))
    (e:O)(E:Ideal O)(W:𝓢(ℝ,ℂ))(K R:ℝ):
    retainedFourierTerm a b r' ha hb hr' χa χb G' e E W K R=
      retainedFourierTerm a b r ha hb hr χa χb G e E W K R:=by
  subst r'
  have hg:G'=G:=eq_of_heq (quotient_function_heq r r rfl G G' hG)
  subst G'
  rfl

def fixedRetainedTerm (C D:Ideal O)(hC:Supported C)(a b:O)
    (ha:Supported (Ideal.span {a}))(hb:Supported (Ideal.span {b}))
    (E:Finset (CommonIndex C D))(W:𝓢(ℝ,ℂ))(K X Z ξ:ℝ):ℂ:=
  retainedFourierTerm a b (activeConductor C D)
    (supported_element_ne_zero _ ha) (supported_element_ne_zero _ hb) (finitePrimeModulus_ne_zero _)
    (supportedModulusCharacter a ha) (supportedModulusCharacter b hb)⁻¹ (activeFunction C D hC)
    (primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E) (∏P∈E,P.val) W K
    (frequencyRadius (firstNominalScale C D (∏P∈E,P.val) K X) Z ξ)

theorem canonicalRetainedTerm_fixed (I J:Ideal O)(hI:Supported I)(hJ:Supported J)
    (E:Finset (CommonIndex I J))(W:𝓢(ℝ,ℂ))(K X Z ξ:ℝ):
    canonicalRetainedTerm I J hI hJ E W K
      (firstNominalScale I J (∏P∈E,P.val) K X) Z ξ=
    fixedRetainedTerm (commonPart I J) (commonPart J I) (commonPart_supported I J hI)
      (residualGenerator I J) (residualGenerator J I)
      (residualGenerator_supported I J hI) (residualGenerator_supported J I hJ)
      (mappedSubset I J E) W K X Z ξ:=by
  unfold fixedRetainedTerm
  rw [nominal_extracted,mappedSubset_generator,mappedSubset_product]
  have hh:=retainedFourierTerm_transport (residualGenerator I J) (residualGenerator J I)
    (activeConductor I J) (activeConductor (commonPart I J) (commonPart J I))
    (supported_element_ne_zero _ (residualGenerator_supported I J hI))
    (supported_element_ne_zero _ (residualGenerator_supported J I hJ))
    (finitePrimeModulus_ne_zero _) (finitePrimeModulus_ne_zero _)
    (residualCharacter I J hI) (residualCharacter J I hJ)⁻¹
    (activeFunction I J hI) (activeFunction (commonPart I J) (commonPart J I) (commonPart_supported I J hI))
    (activeConductor_extracted I J) (activeFunction_mk_extracted I J hI)
    (primeSubsetGenerator (fun P:CommonIndex I J=>P.val) E) (∏P∈E,P.val) W K
    (frequencyRadius (firstNominalScale I J (∏P∈E,P.val) K X) Z ξ)
  exact hh.symm

def inactiveEquiv (I J:Ideal O):
    CenteredMomentFirstDiscardedEnergy.inactiveSubsets I J ≃
      CenteredMomentFirstDiscardedEnergy.inactiveSubsets (commonPart I J) (commonPart J I):=
  (Equiv.finsetCongr (commonEquiv I J)).subtypeEquiv (fun E=>(mappedSubset_inactive I J E).symm)

@[simp] theorem inactiveEquiv_val (I J:Ideal O)
    (E:CenteredMomentFirstDiscardedEnergy.inactiveSubsets I J):
    (inactiveEquiv I J E).val=mappedSubset I J E.val:=rfl

theorem canonicalRetainedPair_fixed (I J:Ideal O)(hI:Supported I)(hJ:Supported J)
    (W:𝓢(ℝ,ℂ))(K X Z ξ:ℝ):
    CenteredMomentFirstSectorLocalization.retainedPair I J hI hJ W K X Z ξ=
    ∑E∈CenteredMomentFirstDiscardedEnergy.inactiveSubsets (commonPart I J) (commonPart J I),
      fixedRetainedTerm (commonPart I J) (commonPart J I) (commonPart_supported I J hI)
        (residualGenerator I J) (residualGenerator J I)
        (residualGenerator_supported I J hI) (residualGenerator_supported J I hJ) E W K X Z ξ:=by
  unfold CenteredMomentFirstSectorLocalization.retainedPair
  apply Finset.sum_bij (fun E _=>mappedSubset I J E)
  · intro E hE
    exact (mappedSubset_inactive I J E).mpr hE
  · intro E hE F hF he
    exact (Equiv.finsetCongr (commonEquiv I J)).injective he
  · intro F hF
    obtain ⟨E,he⟩:=(Equiv.finsetCongr (commonEquiv I J)).surjective F
    change mappedSubset I J E=F at he
    exact ⟨E,(mappedSubset_inactive I J E).mp (he.symm ▸ hF),he⟩
  · intro E hE
    exact canonicalRetainedTerm_fixed I J hI hJ E W K X Z ξ

end SevenEighths.CenteredMomentFirstCommonFourierTransport

end

end OAI
