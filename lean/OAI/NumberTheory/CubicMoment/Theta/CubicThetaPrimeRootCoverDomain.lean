import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeRootAutomorphism
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaFundamentalDomain
import Mathlib.GroupTheory.Complement

namespace OAI

/-! A measurable fundamental domain for the fractional-root cover, obtained from
finitely many translates of the original proved fundamental domain. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

def cubicThetaPrimeRootCoverGroup {p : Eisenstein} (_hp : primaryPrime p) :
    Subgroup cubicThetaPrincipalGroup := cubicThetaPrimeRootSubgroup p

instance cubicThetaPrimeRootCoverGroup_finiteIndex {p : Eisenstein} (hp : primaryPrime p) :
    (cubicThetaPrimeRootCoverGroup hp).FiniteIndex :=
  cubicThetaPrimeRootSubgroup_finiteIndex hp.2.ne_zero

instance cubicThetaPrimeRootCoverGroup_continuous {p : Eisenstein} (hp : primaryPrime p) :
    ContinuousConstSMul (cubicThetaPrimeRootCoverGroup hp) CubicThetaPoint where
  continuous_const_smul g := continuous_const_smul g.val

abbrev CubicThetaPrimeRootCover {p : Eisenstein} (hp : primaryPrime p) :=
  Quotient (MulAction.orbitRel (cubicThetaPrimeRootCoverGroup hp) CubicThetaPoint)

def cubicThetaPrimeRootCoverMap {p : Eisenstein} (hp : primaryPrime p) :
    CubicThetaPoint → CubicThetaPrimeRootCover hp :=
  Quotient.mk (MulAction.orbitRel (cubicThetaPrimeRootCoverGroup hp) CubicThetaPoint)

lemma cubicThetaPrimeRootCoverMap_open {p : Eisenstein} (hp : primaryPrime p) :
    IsOpenQuotientMap (cubicThetaPrimeRootCoverMap hp) :=
  MulAction.isOpenQuotientMap_quotientMk

lemma cubicThetaPrimeRootCover_covering {p : Eisenstein} (hp : primaryPrime p) :
    IsQuotientCoveringMap (cubicThetaPrimeRootCoverMap hp) (cubicThetaPrimeRootCoverGroup hp) :=
  isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul

def cubicThetaPrimeRootTransversal {p : Eisenstein} (hp : primaryPrime p) :
    Set cubicThetaPrincipalGroup :=
  Classical.choose ((cubicThetaPrimeRootCoverGroup hp).exists_isComplement_right 1)

lemma cubicThetaPrimeRootTransversal_complement {p : Eisenstein} (hp : primaryPrime p) :
    Subgroup.IsComplement (cubicThetaPrimeRootCoverGroup hp) (cubicThetaPrimeRootTransversal hp) :=
  (Classical.choose_spec ((cubicThetaPrimeRootCoverGroup hp).exists_isComplement_right 1)).1

instance cubicThetaPrimeRootTransversal_finite {p : Eisenstein} (hp : primaryPrime p) :
    Finite (cubicThetaPrimeRootTransversal hp) := by
  apply Nat.finite_of_card_ne_zero
  rw [(cubicThetaPrimeRootTransversal_complement hp).card_right]
  exact Subgroup.FiniteIndex.index_ne_zero

def cubicThetaPrimeRootCoverDomain {p : Eisenstein} (hp : primaryPrime p) : Set CubicThetaPoint :=
  ⋃ t : cubicThetaPrimeRootTransversal hp,
    (fun x : CubicThetaPoint => t.val • x) '' cubicThetaFundamentalDomain

lemma cubicThetaPrimeRootCoverDomain_measurable {p : Eisenstein} (hp : primaryPrime p) :
    MeasurableSet (cubicThetaPrimeRootCoverDomain hp) := by
  apply MeasurableSet.iUnion
  intro t
  exact (Homeomorph.smul t.val).measurableEmbedding.measurableSet_image'
    cubicThetaFundamentalDomain_measurable

theorem cubicThetaPrimeRootCoverDomain_unique {p : Eisenstein} (hp : primaryPrime p)
    (x : CubicThetaPoint) :
    ∃! g : cubicThetaPrimeRootCoverGroup hp, g • x∈cubicThetaPrimeRootCoverDomain hp := by
  obtain ⟨a,ha,hua⟩ := cubicThetaFundamentalDomain_unique x
  obtain ⟨⟨h,t⟩,he,hunique⟩ := (cubicThetaPrimeRootTransversal_complement hp).existsUnique a⁻¹
  have hmove : (h.val)⁻¹=t.val*a := by
    calc
      _ = h.val⁻¹*(a⁻¹*a) := by simp
      _ = h.val⁻¹*((h.val*t.val)*a) := by rw [he]
      _ = _ := by group
  refine ⟨h⁻¹,?_,?_⟩
  · apply mem_iUnion.mpr
    refine ⟨t,a • x,ha,?_⟩
    change t.val • (a • x)=h.val⁻¹ • x
    rw [←mul_smul,hmove]
  · intro k hk
    obtain ⟨u,hu⟩ := mem_iUnion.mp hk
    obtain ⟨y,hy,hky⟩ := hu
    have hya : u.val⁻¹*k.val=a := by
      apply hua
      rw [mul_smul]
      change u.val⁻¹ • (k • x)∈cubicThetaFundamentalDomain
      rw [←hky,inv_smul_smul]
      exact hy
    have hpair : ((k⁻¹,u) : cubicThetaPrimeRootCoverGroup hp × cubicThetaPrimeRootTransversal hp)=(h,t) := by
      apply hunique
      change k.val⁻¹*u.val=a⁻¹
      rw [←hya]
      group
    have hh : k⁻¹=h := congrArg Prod.fst hpair
    simpa only [inv_inv] using congrArg Inv.inv hh

theorem cubicThetaPrimeRootCoverDomain_isFundamentalDomain {p : Eisenstein}
    (hp : primaryPrime p) (μ : Measure CubicThetaPoint) :
    IsFundamentalDomain (cubicThetaPrimeRootCoverGroup hp) (cubicThetaPrimeRootCoverDomain hp) μ :=
  IsFundamentalDomain.mk' (cubicThetaPrimeRootCoverDomain_measurable hp).nullMeasurableSet
    (cubicThetaPrimeRootCoverDomain_unique hp)

instance cubicThetaPrimeRootCover_measurableSpace {p : Eisenstein} (hp : primaryPrime p) :
    MeasurableSpace (CubicThetaPrimeRootCover hp) := borel _

instance cubicThetaPrimeRootCover_borelSpace {p : Eisenstein} (hp : primaryPrime p) :
    BorelSpace (CubicThetaPrimeRootCover hp) := ⟨rfl⟩

def cubicThetaPrimeRootCoverMeasure {p : Eisenstein} (hp : primaryPrime p) :
    Measure (CubicThetaPrimeRootCover hp) :=
  (cubicThetaPointMeasure.restrict (cubicThetaPrimeRootCoverDomain hp)).map (cubicThetaPrimeRootCoverMap hp)

end CubicFirstMoment

end

end OAI
