import OAI.NumberTheory.DirichletL.Moments.FirstSectorLocalization
import OAI.NumberTheory.DirichletL.Moments.FirstSectorEnergy

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentFirstCommonTransport
open ActualEisensteinCubic ConcretePrimeRowBridge CanonicalQuadraticSieve
open CenteredMomentCanonicalFirst CenteredMomentCompleteCommon CenteredMomentActive
open CenteredMomentFirstSectorEnergy CompletedGauss
local notation "O"=>ActualEisensteinCubic.O

theorem extracted_support (I J:Ideal O):
    commonSupport (commonPart I J) (commonPart J I)=commonSupport I J:=by
  rw [commonSupport,commonPart_support,commonPart_support,commonSupport_comm J I,Finset.inter_self]

def commonEquiv (I J:Ideal O):CommonIndex I J ≃ CommonIndex (commonPart I J) (commonPart J I) where
  toFun P:=⟨P.val,by rw [extracted_support];exact P.property⟩
  invFun P:=⟨P.val,by rw [←extracted_support I J];exact P.property⟩
  left_inv _:=rfl
  right_inv _:=rfl

@[simp] theorem commonEquiv_val (I J:Ideal O)(P:CommonIndex I J):
    (commonEquiv I J P).val=P.val:=rfl

@[simp] theorem extracted_left (I J:Ideal O)(P:CommonIndex I J):
    leftExponent (commonPart I J) (commonPart J I) (commonEquiv I J P)=leftExponent I J P:=by
  simp only [leftExponent,commonEquiv_val,commonPart_valuation,ite_eq_left P.property]

@[simp] theorem extracted_right (I J:Ideal O)(P:CommonIndex I J):
    rightExponent (commonPart I J) (commonPart J I) (commonEquiv I J P)=rightExponent I J P:=by
  have hp:P.val∈commonSupport J I:=by rw [commonSupport_comm];exact P.property
  simp only [rightExponent,commonEquiv_val,commonPart_valuation,ite_eq_left hp]

def activeEquiv (I J:Ideal O):ActiveIndex I J ≃ ActiveIndex (commonPart I J) (commonPart J I) where
  toFun P:=⟨commonEquiv I J P.val,by
    simpa only [ActiveIndex,CenteredMomentActive.activeSupport,Finset.mem_filter,Finset.mem_univ,true_and,extracted_left,extracted_right]
      using P.property⟩
  invFun P:=⟨(commonEquiv I J).symm P.val,by
    have hp:=P.property
    have he:(commonEquiv I J) ((commonEquiv I J).symm P.val)=P.val:=(commonEquiv I J).apply_symm_apply _
    rw [←he] at hp
    simpa only [ActiveIndex,CenteredMomentActive.activeSupport,Finset.mem_filter,Finset.mem_univ,true_and,extracted_left,extracted_right]
      using hp⟩
  left_inv P:=by apply Subtype.ext;exact (commonEquiv I J).symm_apply_apply _
  right_inv P:=by apply Subtype.ext;exact (commonEquiv I J).apply_symm_apply _

@[simp] theorem activeEquiv_prime (I J:Ideal O)(P:ActiveIndex I J):
    activePrime (commonPart I J) (commonPart J I) (activeEquiv I J P)=activePrime I J P:=rfl

@[simp] theorem activeEquiv_exponent (I J:Ideal O)(P:ActiveIndex I J):
    activeExponent (commonPart I J) (commonPart J I) (activeEquiv I J P)=activeExponent I J P:=by
  change netExponent (leftExponent _ _ (commonEquiv I J P.val))
    (rightExponent _ _ (commonEquiv I J P.val))=_
  rw [extracted_left,extracted_right]
  rfl

theorem activeConductor_extracted (I J:Ideal O):
    activeConductor (commonPart I J) (commonPart J I)=activeConductor I J:=by
  unfold activeConductor finitePrimeModulus
  congr 1
  exact (Fintype.prod_equiv (activeEquiv I J) _ _ (fun P=>by rw [activeEquiv_prime])).symm

theorem activeRow_extracted (I J:Ideal O)(hI:Supported I)(z:O):
    finiteSexticRow (activePrime (commonPart I J) (commonPart J I))
      (activeGood _ _ (commonPart_supported I J hI))
      (activeExponent (commonPart I J) (commonPart J I)) z=
    finiteSexticRow (activePrime I J) (activeGood I J hI) (activeExponent I J) z:=by
  unfold finiteSexticRow
  apply (Fintype.prod_equiv (activeEquiv I J) _ _ ?_).symm
  intro P
  rw [activeEquiv_exponent]
  rfl

theorem activeFunction_mk_extracted (I J:Ideal O)(hI:Supported I)(z:O):
    activeFunction (commonPart I J) (commonPart J I) (commonPart_supported I J hI)
      (Ideal.Quotient.mk _ z)=activeFunction I J hI (Ideal.Quotient.mk _ z):=by
  simp only [activeFunction]
  exact activeRow_extracted I J hI z

def mappedSubset (I J:Ideal O)(E:Finset (CommonIndex I J)):
    Finset (CommonIndex (commonPart I J) (commonPart J I)):=E.map (commonEquiv I J).toEmbedding

theorem mappedSubset_product (I J:Ideal O)(E:Finset (CommonIndex I J)):
    (∏P∈mappedSubset I J E,P.val)=∏P∈E,P.val:=by
  simp only [mappedSubset,Finset.prod_map,Equiv.toEmbedding_apply,commonEquiv_val]

theorem mappedSubset_generator (I J:Ideal O)(E:Finset (CommonIndex I J)):
    primeSubsetGenerator (fun P:CommonIndex (commonPart I J) (commonPart J I)=>P.val)
      (mappedSubset I J E)=primeSubsetGenerator (fun P:CommonIndex I J=>P.val) E:=by
  unfold primeSubsetGenerator
  rw [mappedSubset_product]

theorem mappedSubset_inactive (I J:Ideal O)(E:Finset (CommonIndex I J)):
    mappedSubset I J E∈CenteredMomentFirstDiscardedEnergy.inactiveSubsets (commonPart I J) (commonPart J I) ↔
      E∈CenteredMomentFirstDiscardedEnergy.inactiveSubsets I J:=by
  simp only [CenteredMomentFirstDiscardedEnergy.inactiveSubsets,Finset.mem_powerset]
  constructor
  · intro h P hP
    have hp:=h (Finset.mem_map.mpr ⟨P,hP,rfl⟩)
    simpa only [Equiv.toEmbedding_apply,principalSupport,Finset.mem_filter,Finset.mem_univ,true_and,extracted_left,extracted_right]
      using hp
  · intro h P hP
    obtain ⟨R,hR,rfl⟩:=Finset.mem_map.mp hP
    have hr:=h hR
    simpa only [Equiv.toEmbedding_apply,principalSupport,Finset.mem_filter,Finset.mem_univ,true_and,extracted_left,extracted_right]
      using hr

theorem nominal_extracted (I J:Ideal O)(E:Finset (CommonIndex I J))(K X:ℝ):
    CenteredMomentFirstScale.firstNominalScale (commonPart I J) (commonPart J I)
      (∏P∈mappedSubset I J E,P.val) K X=
    CenteredMomentFirstScale.firstNominalScale I J (∏P∈E,P.val) K X:=by
  obtain ⟨hc,hd⟩:=fixed_common_parts (commonPart I J) (commonPart J I)
    (commonPart_ne_zero I J) (commonPart_ne_zero J I) (commonParts_equal_support I J)
  unfold CenteredMomentFirstScale.firstNominalScale
  rw [mappedSubset_product,activeConductor_extracted,hc,hd]

end SevenEighths.CenteredMomentFirstCommonTransport

end

end OAI
