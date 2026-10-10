import Mathlib
import OAI.Probability.CriticalPercolation.Growth.CosetBounded

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical Pointwise

namespace CriticalPercolation.RelativeGrowth
variable {A : Type*} [Group A]

def subgroupCosetEmbedding (K H : Subgroup A) : H ⧸ K.subgroupOf H ↪ A ⧸ K where
  toFun := Quotient.map' Subtype.val (by
    intro a b h
    simpa only [QuotientGroup.leftRel_apply,Subgroup.mem_subgroupOf,Subgroup.coe_mul,Subgroup.coe_inv] using h)
  inj' := Quotient.ind₂' (by
    intro a b h
    change (QuotientGroup.mk a.val : A ⧸ K)=QuotientGroup.mk b.val at h
    apply QuotientGroup.eq.mpr
    change a.val⁻¹*b.val∈K
    exact QuotientGroup.eq.mp h)
@[simp] lemma subgroupCosetEmbedding_mk (K H : Subgroup A) (h : H) :
    subgroupCosetEmbedding K H (QuotientGroup.mk h)=QuotientGroup.mk h.val := rfl
lemma subgroupCosetEmbedding_range (K H : Subgroup A) :
    Set.range (subgroupCosetEmbedding K H)=(QuotientGroup.mk : A → A ⧸ K) '' (H:Set A) := by
  ext q
  constructor
  · rintro ⟨x,rfl⟩
    obtain ⟨h,rfl⟩ := QuotientGroup.mk_surjective x
    exact ⟨h,h.property,rfl⟩
  · rintro ⟨h,hh,rfl⟩
    exact ⟨QuotientGroup.mk (⟨h,hh⟩ : H),rfl⟩
lemma finite_coset_image_subgroup_iff (K H : Subgroup A) :
    ((QuotientGroup.mk : A → A ⧸ K) '' (H:Set A)).Finite ↔ K.relIndex H≠0 := by
  rw [←subgroupCosetEmbedding_range]
  rw [Set.finite_range_iff (subgroupCosetEmbedding K H).injective]
  change Finite (H ⧸ K.subgroupOf H) ↔ Nat.card (H ⧸ K.subgroupOf H)≠0
  exact ⟨fun h => by let := h; exact Nat.card_pos.ne',
    fun h => (Nat.finite_of_card_ne_zero h)⟩

lemma bounded_subgroup_iff (K H : Subgroup A) (S : Set A)
    (h1 : (1:A)∈S) (hi : S⁻¹=S) (hgen : Subgroup.closure S=⊤)
    (hK : Bounded S (K:Set A)) (hf : ∀ n, (ball K S n).Finite) :
    Bounded S (H:Set A) ↔ K.relIndex H≠0 := by
  rw [←finite_coset_image_subgroup_iff]
  exact ⟨finite_coset_image_of_bounded K S (H:Set A) hf,
    bounded_of_finite_coset_image S K h1 hi hgen hK (H:Set A)⟩

lemma subgroup_ball_image (K H : Subgroup A) (T : Set H) (n : ℕ) :
    (subgroupCosetEmbedding K H) '' ball (K.subgroupOf H) T n=
      ball K (H.subtype '' T) n := by
  rw [ball,Set.image_image,ball,←Set.image_pow]
  rw [Set.image_image]
  rfl
lemma HasDegree.subgroup_bounded {K : Subgroup A} {S : Set A} {d : ℕ}
    (h1 : (1:A)∈S) (hg : HasDegree K S d) (H : Subgroup A) (T : Set H)
    (hT : Bounded S (H.subtype '' T)) : HasDegree (K.subgroupOf H) T d := by
  have ht := hg.bounded_generators h1 hT
  have hf (n : ℕ) : (ball (K.subgroupOf H) T n).Finite := by
    apply Set.Finite.of_finite_image (f:=subgroupCosetEmbedding K H)
    rw [subgroup_ball_image]
    exact ht.1 n
    exact (subgroupCosetEmbedding K H).injective.injOn
  refine ⟨hf,?_⟩
  obtain ⟨C,hC⟩ := ht.2
  refine ⟨C,?_⟩
  intro R
  obtain ⟨n,hn,hb⟩ := hC R
  refine ⟨n,hn,?_⟩
  rw [←subgroup_ball_image,Set.ncard_image_of_injective _ (subgroupCosetEmbedding K H).injective] at hb
  exact hb

lemma finite_image_of_finite_coset_image {B : Type*} [Group B]
    (K : Subgroup A) (f : A →* B) (hK : (f '' (K:Set A)).Finite)
    (T : Set A) (hT : ((QuotientGroup.mk : A → A ⧸ K) '' T).Finite) :
    (f '' T).Finite := by
  obtain ⟨F,hF,hcov⟩ := (finite_coset_image_iff_cover K T).mp hT
  apply ((hF.image f).mul hK).subset
  rintro _ ⟨t,ht,rfl⟩
  obtain ⟨a,ha,k,hk,rfl⟩ := hcov ht
  rw [map_mul]
  exact Set.mul_mem_mul ⟨a,ha,rfl⟩ ⟨k,hk,rfl⟩

lemma finiteIndex_bounded_generators (S : Set A)
    (h1 : (1:A)∈S) (hi : S⁻¹=S) (hgen : Subgroup.closure S=⊤)
    (H : Subgroup A) [H.FiniteIndex] :
    ∃ T : Set H, (1:H)∈T ∧ T⁻¹=T ∧ Subgroup.closure T=⊤ ∧ Bounded S (H.subtype '' T) := by
  let := H.fintypeQuotientOfFiniteIndex
  obtain ⟨R,hR,hR1⟩ := H.exists_isComplement_right 1
  have hRf : R.Finite := by
    let : Fintype R := Fintype.ofEquiv _ hR.rightQuotientEquiv
    exact Set.toFinite R
  let U : Set H := (R*S).image (fun g => ⟨g*(hR.toRightFun g:A)⁻¹,hR.mul_inv_toRightFun_mem g⟩)
  have hUgen : Subgroup.closure U=⊤ := Subgroup.closure_mul_image_eq_top hR hR1 hgen
  have hUb : Bounded S (H.subtype '' U) := by
    have hRb := bounded_finite S h1 hi hgen hRf
    have hSb : Bounded S S := ⟨1,by simp⟩
    exact ((hRb.mul hSb).mul (hRb.inv hi)).mono (by
      rintro _ ⟨_,⟨g,hg,rfl⟩,rfl⟩
      exact Set.mul_mem_mul hg (Set.inv_mem_inv.mpr (hR.toRightFun g).property))
  let T := {1}∪(U∪U⁻¹)
  refine ⟨T,by simp [T],?_,?_,?_⟩
  · simp [T,Set.union_inv,Set.union_comm]
  · apply top_unique
    rw [←hUgen]
    exact Subgroup.closure_mono (by intro u hu; exact Or.inr (Or.inl hu))
  · have he : H.subtype '' T={1}∪((H.subtype '' U)∪(H.subtype '' U)⁻¹) := by
      simp only [T,Set.image_union,Set.image_singleton,map_one,Set.image_inv]
    rw [he]
    exact (bounded_singleton S h1 hi hgen 1).union h1 (hUb.union h1 (hUb.inv hi))

end CriticalPercolation.RelativeGrowth
end
end

end OAI
