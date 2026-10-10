import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCoverGroup
import Mathlib.GroupTheory.Complement

namespace OAI

/-! A measurable fundamental domain for the prime cover, obtained from
finitely many translates of the original proved fundamental domain. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

def cubicThetaPrimeTransversal {p : Eisenstein} (hp : primaryPrime p) :
    Set cubicThetaPrincipalGroup :=
  Classical.choose ((cubicThetaPrimeCoverGroup hp).exists_isComplement_right 1)

lemma cubicThetaPrimeTransversal_complement {p : Eisenstein} (hp : primaryPrime p) :
    Subgroup.IsComplement (cubicThetaPrimeCoverGroup hp) (cubicThetaPrimeTransversal hp) :=
  (Classical.choose_spec ((cubicThetaPrimeCoverGroup hp).exists_isComplement_right 1)).1

instance cubicThetaPrimeTransversal_finite {p : Eisenstein} (hp : primaryPrime p) :
    Finite (cubicThetaPrimeTransversal hp) := by
  apply Nat.finite_of_card_ne_zero
  rw [(cubicThetaPrimeTransversal_complement hp).card_right]
  exact Subgroup.FiniteIndex.index_ne_zero

def cubicThetaPrimeCoverDomain {p : Eisenstein} (hp : primaryPrime p) : Set CubicThetaPoint :=
  ⋃ t : cubicThetaPrimeTransversal hp,
    (fun x : CubicThetaPoint => t.val • x) '' cubicThetaFundamentalDomain

lemma cubicThetaPrimeCoverDomain_measurable {p : Eisenstein} (hp : primaryPrime p) :
    MeasurableSet (cubicThetaPrimeCoverDomain hp) := by
  apply MeasurableSet.iUnion
  intro t
  exact (Homeomorph.smul t.val).measurableEmbedding.measurableSet_image'
    cubicThetaFundamentalDomain_measurable

theorem cubicThetaPrimeCoverDomain_unique {p : Eisenstein} (hp : primaryPrime p)
    (x : CubicThetaPoint) :
    ∃! g : cubicThetaPrimeCoverGroup hp, g • x∈cubicThetaPrimeCoverDomain hp := by
  obtain ⟨a,ha,hua⟩ := cubicThetaFundamentalDomain_unique x
  obtain ⟨⟨h,t⟩,he,hunique⟩ := (cubicThetaPrimeTransversal_complement hp).existsUnique a⁻¹
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
    have hpair : ((k⁻¹,u) : cubicThetaPrimeCoverGroup hp × cubicThetaPrimeTransversal hp)=(h,t) := by
      apply hunique
      change k.val⁻¹*u.val=a⁻¹
      rw [←hya]
      group
    have hh : k⁻¹=h := congrArg Prod.fst hpair
    simpa only [inv_inv] using congrArg Inv.inv hh

theorem cubicThetaPrimeCoverDomain_isFundamentalDomain {p : Eisenstein}
    (hp : primaryPrime p) (μ : Measure CubicThetaPoint) :
    IsFundamentalDomain (cubicThetaPrimeCoverGroup hp) (cubicThetaPrimeCoverDomain hp) μ :=
  IsFundamentalDomain.mk' (cubicThetaPrimeCoverDomain_measurable hp).nullMeasurableSet
    (cubicThetaPrimeCoverDomain_unique hp)

instance cubicThetaPrimeCover_measurableSpace {p : Eisenstein} (hp : primaryPrime p) :
    MeasurableSpace (CubicThetaPrimeCover hp) := borel _

instance cubicThetaPrimeCover_borelSpace {p : Eisenstein} (hp : primaryPrime p) :
    BorelSpace (CubicThetaPrimeCover hp) := ⟨rfl⟩

def cubicThetaPrimeCoverMeasure {p : Eisenstein} (hp : primaryPrime p) :
    Measure (CubicThetaPrimeCover hp) :=
  (cubicThetaPointMeasure.restrict (cubicThetaPrimeCoverDomain hp)).map (cubicThetaPrimeCoverMap hp)

end CubicFirstMoment

end

end OAI
