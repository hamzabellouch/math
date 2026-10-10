import Mathlib
import OAI.Probability.CriticalPercolation.Growth.CosetTransfer

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical Pointwise

namespace CriticalPercolation.RelativeGrowth
variable {A B : Type*} [Group A] [Group B]

lemma exists_finite_coset_cover (K : Subgroup A) (T : Set A)
    (hf : ((QuotientGroup.mk : A → A ⧸ K) '' T).Finite) :
    ∃ F : Set A, F.Finite ∧ F.ncard=((QuotientGroup.mk : A → A ⧸ K) '' T).ncard ∧ T⊆F*(K:Set A) := by
  let Q := (QuotientGroup.mk : A → A ⧸ K) '' T
  have hh : ∀ q∈Q, ∃ a∈T, (QuotientGroup.mk a : A ⧸ K)=q := fun q hq => hq
  choose a ha he using hh
  let F := Set.range (fun q : Q => a q.val q.property)
  let : Finite Q := hf.to_subtype
  have hi : Injective (fun q : Q => a q.val q.property) := by
    intro q r h
    apply Subtype.ext
    rw [←he q.val q.property,←he r.val r.property]
    exact congrArg (QuotientGroup.mk : A → A ⧸ K) h
  refine ⟨F,Set.finite_range _,?_,?_⟩
  · rw [Set.ncard_range_of_injective hi]
    rfl
  · intro t ht
    let q : Q := ⟨QuotientGroup.mk t,⟨t,ht,rfl⟩⟩
    refine ⟨a q.val q.property,⟨q,rfl⟩,(a q.val q.property)⁻¹*t,?_,by simp⟩
    exact QuotientGroup.eq.mp (he q.val q.property)

lemma image_ncard_bound (K : Subgroup A) (f : A →* B) (hK : (f '' (K:Set A)).Finite)
    (T : Set A) (hT : ((QuotientGroup.mk : A → A ⧸ K) '' T).Finite) :
    (f '' T).ncard≤((QuotientGroup.mk : A → A ⧸ K) '' T).ncard*(f '' (K:Set A)).ncard := by
  obtain ⟨F,hF,hFc,hcov⟩ := exists_finite_coset_cover K T hT
  have hs : f '' T⊆(f '' F)*(f '' (K:Set A)) := by
    rintro _ ⟨t,ht,rfl⟩
    obtain ⟨a,ha,k,hk,rfl⟩ := hcov ht
    rw [map_mul]
    exact Set.mul_mem_mul ⟨a,ha,rfl⟩ ⟨k,hk,rfl⟩
  calc
    _ ≤ ((f '' F)*(f '' (K:Set A))).ncard := Set.ncard_le_ncard hs ((hF.image f).mul hK)
    _ ≤ (f '' F).ncard*(f '' (K:Set A)).ncard := by
      have hh := @Finset.card_mul_le B _ _ (hF.image f).toFinset hK.toFinset
      simpa only [←Set.ncard_coe_finset,Finset.coe_mul,Set.Finite.coe_toFinset] using hh
    _ ≤ F.ncard*(f '' (K:Set A)).ncard := Nat.mul_le_mul_right _ (Set.ncard_image_le hF)
    _ = _ := by rw [hFc]

lemma HasDegree.image_polynomial {K : Subgroup A} {S : Set A} {d : ℕ}
    (h1 : (1:A)∈S) (hi : S⁻¹=S) (hgen : Subgroup.closure S=⊤) (hg : HasDegree K S d)
    (f : A →* B) (hf : Surjective f) (hK : (f '' (K:Set A)).Finite) :
    SparseGrowth.HasPolynomialDegree B d := by
  have hSf : (f '' S).Finite := finite_image_of_finite_coset_image K f hK S (by simpa only [ball,pow_one] using hg.1 1)
  refine ⟨f '' S,hSf,⟨1,h1,map_one f⟩,?_,?_,?_,?_⟩
  · rw [←Set.image_inv,hi]
  · rw [←MonoidHom.map_closure,hgen]
    exact Subgroup.map_top_of_surjective f hf
  · exact hg.2.choose*(f '' (K:Set A)).ncard
  · intro R
    obtain ⟨n,hn,hb⟩ := hg.2.choose_spec R
    refine ⟨n,hn,?_⟩
    rw [←Set.image_pow]
    calc
      _ ≤ (ball K S n).ncard*(f '' (K:Set A)).ncard := image_ncard_bound K f hK (S^n) (hg.1 n)
      _ ≤ (hg.2.choose*n^d)*(f '' (K:Set A)).ncard := Nat.mul_le_mul_right _ hb
      _ = _ := by ring

end CriticalPercolation.RelativeGrowth
end
end

end OAI
