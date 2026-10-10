import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeRootCoverDomain
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeCoverDomain

namespace OAI

/-! The actual intermediate cover from the cubic root subgroup to
Iwahori(p cubed), needed to transport the cubed-prime trace pairing. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

instance cubicThetaPrimeCubeIwahori_continuous {p : Eisenstein} :
    ContinuousConstSMul (cubicThetaPrimeIwahori (p^3)) CubicThetaPoint where
  continuous_const_smul g := continuous_const_smul g.val

lemma cubicThetaPrimeCubeRoot_le_hecke {p : Eisenstein} (hp : primaryPrime p) :
    cubicThetaPrimeCubeRootCoverGroup hp≤cubicThetaPrimeIwahori (p^3) := by
  intro g hg
  exact (cubicThetaPrimeCubeRootIwahori (⟨g,hg⟩ : cubicThetaPrimeCubeRootSubgroup p)).property

def cubicThetaPrimeCubeRootHeckeSubgroup {p : Eisenstein} (hp : primaryPrime p) :
    Subgroup (cubicThetaPrimeIwahori (p^3)) :=
  (cubicThetaPrimeCubeRootCoverGroup hp).comap (cubicThetaPrimeIwahori (p^3)).subtype

instance cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex {p : Eisenstein} (hp : primaryPrime p) :
    (cubicThetaPrimeCubeRootHeckeSubgroup hp).FiniteIndex := by
  unfold cubicThetaPrimeCubeRootHeckeSubgroup
  infer_instance

def cubicThetaPrimeCubeRootHeckeSubgroupEquiv {p : Eisenstein} (hp : primaryPrime p) :
    cubicThetaPrimeCubeRootHeckeSubgroup hp ≃* cubicThetaPrimeCubeRootCoverGroup hp where
  toFun h := ⟨h.val.val,h.property⟩
  invFun h := ⟨⟨h.val,cubicThetaPrimeCubeRoot_le_hecke hp h.property⟩,h.property⟩
  left_inv _h := rfl
  right_inv _h := rfl
  map_mul' _h _k := rfl

theorem cubicThetaPrimeCubeRootHecke_index {p : Eisenstein} (hp : primaryPrime p) :
    (cubicThetaPrimeCubeRootHeckeSubgroup hp).index*(cubicThetaPrimeIwahori (p^3)).index=
      (cubicThetaPrimeCubeRootCoverGroup hp).index :=
  Subgroup.relIndex_mul_index (cubicThetaPrimeCubeRoot_le_hecke hp)


def cubicThetaPrimeCubeRootHeckeTransversal {p : Eisenstein} (hp : primaryPrime p) :
    Set (cubicThetaPrimeIwahori (p^3)) :=
  Classical.choose ((cubicThetaPrimeCubeRootHeckeSubgroup hp).exists_isComplement_right 1)

lemma cubicThetaPrimeCubeRootHeckeTransversal_complement {p : Eisenstein} (hp : primaryPrime p) :
    Subgroup.IsComplement (cubicThetaPrimeCubeRootHeckeSubgroup hp) (cubicThetaPrimeCubeRootHeckeTransversal hp) :=
  (Classical.choose_spec ((cubicThetaPrimeCubeRootHeckeSubgroup hp).exists_isComplement_right 1)).1

instance cubicThetaPrimeCubeRootHeckeTransversal_finite {p : Eisenstein} (hp : primaryPrime p) :
    Finite (cubicThetaPrimeCubeRootHeckeTransversal hp) := by
  apply Nat.finite_of_card_ne_zero
  rw [(cubicThetaPrimeCubeRootHeckeTransversal_complement hp).card_right]
  exact Subgroup.FiniteIndex.index_ne_zero

def cubicThetaPrimeCubeRootHeckeDomain {p : Eisenstein} (hp : primaryPrime p) : Set CubicThetaPoint :=
  ⋃ t : cubicThetaPrimeCubeRootHeckeTransversal hp,
    (fun x : CubicThetaPoint => t.val • x) '' (cubicThetaPrimeCubeCoverDomain p)

lemma cubicThetaPrimeCubeRootHeckeDomain_measurable {p : Eisenstein} (hp : primaryPrime p) :
    MeasurableSet (cubicThetaPrimeCubeRootHeckeDomain hp) := by
  apply MeasurableSet.iUnion
  intro t
  exact (Homeomorph.smul t.val).measurableEmbedding.measurableSet_image'
    (cubicThetaPrimeCubeCoverDomain_measurable hp)

theorem cubicThetaPrimeCubeRootHeckeDomain_unique {p : Eisenstein} (hp : primaryPrime p)
    (x : CubicThetaPoint) :
    ∃! g : cubicThetaPrimeCubeRootHeckeSubgroup hp, g • x∈cubicThetaPrimeCubeRootHeckeDomain hp := by
  obtain ⟨a,ha,hua⟩ := cubicThetaPrimeCubeCoverDomain_unique p x
  obtain ⟨⟨h,t⟩,he,hunique⟩ := (cubicThetaPrimeCubeRootHeckeTransversal_complement hp).existsUnique a⁻¹
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
      change u.val⁻¹ • (k • x)∈(cubicThetaPrimeCubeCoverDomain p)
      rw [←hky,inv_smul_smul]
      exact hy
    have hpair : ((k⁻¹,u) : cubicThetaPrimeCubeRootHeckeSubgroup hp × cubicThetaPrimeCubeRootHeckeTransversal hp)=(h,t) := by
      apply hunique
      change k.val⁻¹*u.val=a⁻¹
      rw [←hya]
      group
    have hh : k⁻¹=h := congrArg Prod.fst hpair
    simpa only [inv_inv] using congrArg Inv.inv hh

theorem cubicThetaPrimeCubeRootHeckeDomain_isFundamentalDomain {p : Eisenstein}
    (hp : primaryPrime p) (μ : Measure CubicThetaPoint) :
    IsFundamentalDomain (cubicThetaPrimeCubeRootHeckeSubgroup hp) (cubicThetaPrimeCubeRootHeckeDomain hp) μ :=
  IsFundamentalDomain.mk' (cubicThetaPrimeCubeRootHeckeDomain_measurable hp).nullMeasurableSet
    (cubicThetaPrimeCubeRootHeckeDomain_unique hp)

theorem cubicThetaPrimeCubeRootHeckeDomain_root_fundamental {p : Eisenstein}
    (hp : primaryPrime p) (μ : Measure CubicThetaPoint) :
    IsFundamentalDomain (cubicThetaPrimeCubeRootCoverGroup hp)
      (cubicThetaPrimeCubeRootHeckeDomain hp) μ := by
  apply IsFundamentalDomain.mk' (cubicThetaPrimeCubeRootHeckeDomain_measurable hp).nullMeasurableSet
  intro x
  obtain ⟨k,hk,huniq⟩ := cubicThetaPrimeCubeRootHeckeDomain_unique hp x
  refine ⟨cubicThetaPrimeCubeRootHeckeSubgroupEquiv hp k,hk,?_⟩
  intro g hg
  have he := huniq ((cubicThetaPrimeCubeRootHeckeSubgroupEquiv hp).symm g) hg
  have hf := congrArg (cubicThetaPrimeCubeRootHeckeSubgroupEquiv hp) he
  simpa only [MulEquiv.apply_symm_apply] using hf


end CubicFirstMoment

end

end OAI
