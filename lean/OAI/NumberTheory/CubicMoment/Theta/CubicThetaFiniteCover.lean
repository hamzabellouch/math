import OAI.NumberTheory.CubicMoment.Theta.CubicThetaFundamentalDomain
import Mathlib.GroupTheory.Complement

namespace OAI

/-! Exact finite-cover domains in the fixed arithmetic action.  This is
used to compare the three root levels without postulating equality of
integrals on different covers. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

structure CubicThetaArithmeticCover where
  group : Subgroup cubicThetaPrincipalGroup
  domain : Set CubicThetaPoint
  measurable : MeasurableSet domain
  unique : ∀ x : CubicThetaPoint, ∃! g : group, g • x∈domain

instance (D : CubicThetaArithmeticCover) :
    ContinuousConstSMul D.group CubicThetaPoint where
  continuous_const_smul g := continuous_const_smul g.val

lemma CubicThetaArithmeticCover.fundamental (D : CubicThetaArithmeticCover)
    (μ : Measure CubicThetaPoint) : IsFundamentalDomain D.group D.domain μ :=
  IsFundamentalDomain.mk' D.measurable.nullMeasurableSet D.unique

def cubicThetaBaseCover : CubicThetaArithmeticCover where
  group := ⊤
  domain := cubicThetaFundamentalDomain
  measurable := cubicThetaFundamentalDomain_measurable
  unique x := by
    obtain ⟨g,hg,hu⟩ := cubicThetaFundamentalDomain_unique x
    refine ⟨⟨g,Subgroup.mem_top g⟩,hg,?_⟩
    intro k hk
    exact Subtype.ext (hu k.val hk)

variable (D : CubicThetaArithmeticCover) (K : Subgroup cubicThetaPrincipalGroup)
  (hle : K≤D.group) [K.FiniteIndex]

def cubicThetaRelativeSubgroup : Subgroup D.group := K.comap D.group.subtype

instance cubicThetaRelativeSubgroup_finiteIndex :
    (cubicThetaRelativeSubgroup D K).FiniteIndex := by
  unfold cubicThetaRelativeSubgroup
  infer_instance

def cubicThetaRelativeSubgroupEquiv : cubicThetaRelativeSubgroup D K ≃* K where
  toFun h := ⟨h.val.val,h.property⟩
  invFun h := ⟨⟨h.val,hle h.property⟩,h.property⟩
  left_inv _h := rfl
  right_inv _h := rfl
  map_mul' _h _k := rfl

def cubicThetaRelativeTransversal : Set D.group :=
  Classical.choose ((cubicThetaRelativeSubgroup D K).exists_isComplement_right 1)

omit [K.FiniteIndex] in
lemma cubicThetaRelativeTransversal_complement :
    Subgroup.IsComplement (cubicThetaRelativeSubgroup D K) (cubicThetaRelativeTransversal D K) :=
  (Classical.choose_spec ((cubicThetaRelativeSubgroup D K).exists_isComplement_right 1)).1

instance cubicThetaRelativeTransversal_finite : Finite (cubicThetaRelativeTransversal D K) := by
  apply Nat.finite_of_card_ne_zero
  rw [(cubicThetaRelativeTransversal_complement D K).card_right]
  exact Subgroup.FiniteIndex.index_ne_zero

def cubicThetaRelativeDomain : Set CubicThetaPoint :=
  ⋃ t : cubicThetaRelativeTransversal D K, (fun x : CubicThetaPoint => t.val • x) '' D.domain

lemma cubicThetaRelativeDomain_measurable : MeasurableSet (cubicThetaRelativeDomain D K) := by
  apply MeasurableSet.iUnion
  intro t
  exact (Homeomorph.smul t.val).measurableEmbedding.measurableSet_image' D.measurable

include hle in
omit [K.FiniteIndex] in
lemma cubicThetaRelativeDomain_unique (x : CubicThetaPoint) :
    ∃! g : K, g • x∈cubicThetaRelativeDomain D K := by
  obtain ⟨a,ha,hua⟩ := D.unique x
  obtain ⟨⟨h,t⟩,he,hu⟩ := (cubicThetaRelativeTransversal_complement D K).existsUnique a⁻¹
  have hmove : h.val⁻¹=t.val*a := by
    calc
      _ = h.val⁻¹*(a⁻¹*a) := by simp
      _ = h.val⁻¹*((h.val*t.val)*a) := by rw [he]
      _ = _ := by group
  have hraw : ∃! g : cubicThetaRelativeSubgroup D K, g • x∈cubicThetaRelativeDomain D K := by
    refine ⟨h⁻¹,?_,?_⟩
    · apply mem_iUnion.mpr
      refine ⟨t,a • x,ha,?_⟩
      change t.val • (a • x)=h.val⁻¹ • x
      rw [←mul_smul,hmove]
    · intro k hk
      obtain ⟨u,y,hy,hky⟩ := mem_iUnion.mp hk
      have hya : u.val⁻¹*k.val=a := by
        apply hua
        rw [mul_smul]
        change u.val⁻¹ • (k • x)∈D.domain
        rw [←hky,inv_smul_smul]
        exact hy
      have hpair : ((k⁻¹,u) : cubicThetaRelativeSubgroup D K × cubicThetaRelativeTransversal D K)=(h,t) := by
        apply hu
        change k.val⁻¹*u.val=a⁻¹
        rw [←hya]
        group
      have hh : k⁻¹=h := congrArg Prod.fst hpair
      simpa only [inv_inv] using congrArg Inv.inv hh
  obtain ⟨k,hk,huniq⟩ := hraw
  refine ⟨cubicThetaRelativeSubgroupEquiv D K hle k,hk,?_⟩
  intro g hg
  have he := huniq ((cubicThetaRelativeSubgroupEquiv D K hle).symm g) hg
  simpa only [MulEquiv.apply_symm_apply] using congrArg (cubicThetaRelativeSubgroupEquiv D K hle) he

def cubicThetaRelativeCover : CubicThetaArithmeticCover where
  group := K
  domain := cubicThetaRelativeDomain D K
  measurable := cubicThetaRelativeDomain_measurable D K
  unique := cubicThetaRelativeDomain_unique D K hle

end CubicFirstMoment

end

end OAI
