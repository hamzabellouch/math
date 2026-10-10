import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeRootAutomorphism
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaFundamentalDomain
import Mathlib.GroupTheory.Complement

namespace OAI

/-! A measurable fundamental domain for the cubic-scale fractional-root cover, obtained from
finitely many translates of the original proved fundamental domain. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

def cubicThetaPrimeCubeRootCoverGroup {p : Eisenstein} (_hp : primaryPrime p) :
    Subgroup cubicThetaPrincipalGroup := cubicThetaPrimeCubeRootSubgroup p

instance cubicThetaPrimeCubeRootCoverGroup_finiteIndex {p : Eisenstein} (hp : primaryPrime p) :
    (cubicThetaPrimeCubeRootCoverGroup hp).FiniteIndex :=
  cubicThetaPrimeCubeRootSubgroup_finiteIndex hp

instance cubicThetaPrimeCubeRootCoverGroup_continuous {p : Eisenstein} (hp : primaryPrime p) :
    ContinuousConstSMul (cubicThetaPrimeCubeRootCoverGroup hp) CubicThetaPoint where
  continuous_const_smul g := continuous_const_smul g.val

abbrev CubicThetaPrimeCubeRootCover {p : Eisenstein} (hp : primaryPrime p) :=
  Quotient (MulAction.orbitRel (cubicThetaPrimeCubeRootCoverGroup hp) CubicThetaPoint)

def cubicThetaPrimeCubeRootCoverMap {p : Eisenstein} (hp : primaryPrime p) :
    CubicThetaPoint → CubicThetaPrimeCubeRootCover hp :=
  Quotient.mk (MulAction.orbitRel (cubicThetaPrimeCubeRootCoverGroup hp) CubicThetaPoint)

lemma cubicThetaPrimeCubeRootCoverMap_open {p : Eisenstein} (hp : primaryPrime p) :
    IsOpenQuotientMap (cubicThetaPrimeCubeRootCoverMap hp) :=
  MulAction.isOpenQuotientMap_quotientMk

lemma cubicThetaPrimeCubeRootCover_covering {p : Eisenstein} (hp : primaryPrime p) :
    IsQuotientCoveringMap (cubicThetaPrimeCubeRootCoverMap hp) (cubicThetaPrimeCubeRootCoverGroup hp) :=
  isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul

def cubicThetaPrimeCubeRootTransversal {p : Eisenstein} (hp : primaryPrime p) :
    Set cubicThetaPrincipalGroup :=
  Classical.choose ((cubicThetaPrimeCubeRootCoverGroup hp).exists_isComplement_right 1)

lemma cubicThetaPrimeCubeRootTransversal_complement {p : Eisenstein} (hp : primaryPrime p) :
    Subgroup.IsComplement (cubicThetaPrimeCubeRootCoverGroup hp) (cubicThetaPrimeCubeRootTransversal hp) :=
  (Classical.choose_spec ((cubicThetaPrimeCubeRootCoverGroup hp).exists_isComplement_right 1)).1

instance cubicThetaPrimeCubeRootTransversal_finite {p : Eisenstein} (hp : primaryPrime p) :
    Finite (cubicThetaPrimeCubeRootTransversal hp) := by
  apply Nat.finite_of_card_ne_zero
  rw [(cubicThetaPrimeCubeRootTransversal_complement hp).card_right]
  exact Subgroup.FiniteIndex.index_ne_zero

def cubicThetaPrimeCubeRootCoverDomain {p : Eisenstein} (hp : primaryPrime p) : Set CubicThetaPoint :=
  ⋃ t : cubicThetaPrimeCubeRootTransversal hp,
    (fun x : CubicThetaPoint => t.val • x) '' cubicThetaFundamentalDomain

lemma cubicThetaPrimeCubeRootCoverDomain_measurable {p : Eisenstein} (hp : primaryPrime p) :
    MeasurableSet (cubicThetaPrimeCubeRootCoverDomain hp) := by
  apply MeasurableSet.iUnion
  intro t
  exact (Homeomorph.smul t.val).measurableEmbedding.measurableSet_image'
    cubicThetaFundamentalDomain_measurable

theorem cubicThetaPrimeCubeRootCoverDomain_unique {p : Eisenstein} (hp : primaryPrime p)
    (x : CubicThetaPoint) :
    ∃! g : cubicThetaPrimeCubeRootCoverGroup hp, g • x∈cubicThetaPrimeCubeRootCoverDomain hp := by
  obtain ⟨a,ha,hua⟩ := cubicThetaFundamentalDomain_unique x
  obtain ⟨⟨h,t⟩,he,hunique⟩ := (cubicThetaPrimeCubeRootTransversal_complement hp).existsUnique a⁻¹
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
    have hpair : ((k⁻¹,u) : cubicThetaPrimeCubeRootCoverGroup hp × cubicThetaPrimeCubeRootTransversal hp)=(h,t) := by
      apply hunique
      change k.val⁻¹*u.val=a⁻¹
      rw [←hya]
      group
    have hh : k⁻¹=h := congrArg Prod.fst hpair
    simpa only [inv_inv] using congrArg Inv.inv hh

theorem cubicThetaPrimeCubeRootCoverDomain_isFundamentalDomain {p : Eisenstein}
    (hp : primaryPrime p) (μ : Measure CubicThetaPoint) :
    IsFundamentalDomain (cubicThetaPrimeCubeRootCoverGroup hp) (cubicThetaPrimeCubeRootCoverDomain hp) μ :=
  IsFundamentalDomain.mk' (cubicThetaPrimeCubeRootCoverDomain_measurable hp).nullMeasurableSet
    (cubicThetaPrimeCubeRootCoverDomain_unique hp)

instance cubicThetaPrimeCubeRootCover_measurableSpace {p : Eisenstein} (hp : primaryPrime p) :
    MeasurableSpace (CubicThetaPrimeCubeRootCover hp) := borel _

instance cubicThetaPrimeCubeRootCover_borelSpace {p : Eisenstein} (hp : primaryPrime p) :
    BorelSpace (CubicThetaPrimeCubeRootCover hp) := ⟨rfl⟩

def cubicThetaPrimeCubeRootCoverMeasure {p : Eisenstein} (hp : primaryPrime p) :
    Measure (CubicThetaPrimeCubeRootCover hp) :=
  (cubicThetaPointMeasure.restrict (cubicThetaPrimeCubeRootCoverDomain hp)).map (cubicThetaPrimeCubeRootCoverMap hp)

end CubicFirstMoment

end

end OAI
