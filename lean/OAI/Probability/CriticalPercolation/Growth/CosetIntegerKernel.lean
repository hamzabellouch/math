import Mathlib
import OAI.Probability.CriticalPercolation.Growth.CosetTransfer
import OAI.Probability.CriticalPercolation.Growth.CosetNormalClosure

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical Pointwise

namespace CriticalPercolation.RelativeGrowth
variable {A : Type*} [Group A]

lemma integer_kernel_normalClosure (S : Set A)
    (hgen : Subgroup.closure S=⊤)
    (f : A →* Multiplicative ℤ) (a : A) (ha : f a=Multiplicative.ofAdd 1) :
    f.ker=Subgroup.normalClosure ((fun s => s*a^(-Multiplicative.toAdd (f s))) '' S) := by
  let F := (fun s => s*a^(-Multiplicative.toAdd (f s))) '' S
  let N := Subgroup.normalClosure F
  have hN : N≤f.ker := by
    apply Subgroup.normalClosure_le_normal
    rintro y ⟨s,hs,rfl⟩
    change f (s*a^(-Multiplicative.toAdd (f s)))=1
    rw [map_mul,map_zpow,ha]
    apply Multiplicative.toAdd.injective
    simp
  let q := QuotientGroup.mk' N
  have hqa : ∀ x : A, q x=(q a)^Multiplicative.toAdd (f x) := by
    intro x
    have hx : x∈Subgroup.closure S := hgen.symm ▸ Subgroup.mem_top x
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      have hm : x*a^(-Multiplicative.toAdd (f x))∈N := Subgroup.subset_normalClosure ⟨x,hx,rfl⟩
      have he := (QuotientGroup.eq_one_iff _).mpr hm
      change q (x*a^(-Multiplicative.toAdd (f x)))=1 at he
      rw [map_mul,map_zpow,zpow_neg] at he
      exact mul_inv_eq_one.mp he
    | one => simp
    | mul x y _ _ hx hy => rw [map_mul,hx,hy,←zpow_add,map_mul,toAdd_mul]
    | inv x _ hx => rw [map_inv,hx,map_inv,toAdd_inv,zpow_neg]
  apply le_antisymm _ hN
  intro x hx
  apply (QuotientGroup.eq_one_iff _).mp
  change q x=1
  rw [hqa,MonoidHom.mem_ker.mp hx]
  simp

lemma HasDegree.integer_kernel_bounded_generators {K : Subgroup A} {S : Set A} {d : ℕ}
    (h1 : (1:A)∈S) (hi : S⁻¹=S) (hgen : Subgroup.closure S=⊤) (hg : HasDegree K S d)
    (hKS : (K:Set A)⊆S) (f : A →* Multiplicative ℤ) (hf : Surjective f) (hKf : K≤f.ker) :
    ∃ T : Set f.ker, (1:f.ker)∈T ∧ T⁻¹=T ∧ Subgroup.closure T=⊤ ∧
      Bounded S (f.ker.subtype '' T) ∧ (K.subgroupOf f.ker : Set f.ker)⊆T := by
  obtain ⟨a,ha⟩ := hf (Multiplicative.ofAdd 1)
  let F := (fun s => s*a^(-Multiplicative.toAdd (f s))) '' S
  have hFker : F⊆f.ker := by
    rintro y ⟨s,hs,rfl⟩
    change f (s*a^(-Multiplicative.toAdd (f s)))=1
    rw [map_mul,map_zpow,ha]
    apply Multiplicative.toAdd.injective
    simp
  have hKF : (K:Set A)⊆F := by
    intro k hk
    refine ⟨k,hKS hk,?_⟩
    dsimp only
    rw [MonoidHom.mem_ker.mp (hKf hk)]
    simp
  have hfi : (f '' (K:Set A)).Finite := by
    apply (Set.finite_singleton (1:Multiplicative ℤ)).subset
    rintro _ ⟨k,hk,rfl⟩
    exact MonoidHom.mem_ker.mp (hKf hk)
  have hfs : (f '' S).Finite := finite_image_of_finite_coset_image K f hfi S (by simpa only [ball,pow_one] using hg.1 1)
  have hFb : Bounded S F := by
    have hp := bounded_finite S h1 hi hgen (hfs.image (fun z => a^(-Multiplicative.toAdd z)))
    exact (Bounded.mul (show Bounded S S from ⟨1,by simp⟩) hp).mono (by
      rintro y ⟨s,hs,rfl⟩
      exact Set.mul_mem_mul hs ⟨f s,⟨s,hs,rfl⟩,rfl⟩)
  obtain ⟨L,hL⟩ := hFb
  obtain ⟨n,hn⟩ := exists_conjugateStage_stationary S F h1 hi K
    (fun k hk => Subgroup.subset_closure (hKF hk)) d hg L hL
  have hncl : f.ker=conjugateStage S F n :=
    (integer_kernel_normalClosure S hgen f a ha).trans (normalClosure_eq_conjugateStage_of_stationary S F h1 hi hgen n hn)
  let U := boundedConjugates S F n
  have hUk : U⊆f.ker := by
    intro u hu
    rw [hncl]
    exact Subgroup.subset_closure hu
  let T0 : Set f.ker := f.ker.subtype ⁻¹' U
  have hT0image : f.ker.subtype '' T0=U := by
    ext u
    exact ⟨fun ⟨x,hx,he⟩ => he ▸ hx,fun hu => ⟨⟨u,hUk hu⟩,hu,rfl⟩⟩
  have hT0gen : Subgroup.closure T0=⊤ := by
    apply Subgroup.map_injective f.ker.subtype_injective
    rw [MonoidHom.map_closure,hT0image,←MonoidHom.range_eq_map,Subgroup.range_subtype]
    exact hncl.symm
  have hT0b : Bounded S (f.ker.subtype '' T0) := by
    rw [hT0image]
    exact ⟨2*n+L,boundedConjugates_subset_pow S F hi L hL n⟩
  let T := {1}∪(T0∪T0⁻¹)
  refine ⟨T,by simp [T],?_,?_,?_,?_⟩
  · simp [T,Set.union_inv,Set.union_comm]
  · apply top_unique
    rw [←hT0gen]
    exact Subgroup.closure_mono (fun t ht => Or.inr (Or.inl ht))
  · have he : f.ker.subtype '' T={1}∪((f.ker.subtype '' T0)∪(f.ker.subtype '' T0)⁻¹) := by
      simp only [T,Set.image_union,Set.image_singleton,map_one,Set.image_inv]
    rw [he]
    exact (bounded_singleton S h1 hi hgen 1).union h1 (hT0b.union h1 (hT0b.inv hi))
  · intro k hk
    apply Or.inr ∘ Or.inl
    exact ⟨1,Set.one_mem_pow h1,k.val,hKF hk,by simp⟩

end CriticalPercolation.RelativeGrowth
end
end

end OAI
