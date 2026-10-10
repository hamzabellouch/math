import Mathlib
import OAI.Probability.CriticalPercolation.Growth.CosetSparseGrowth

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical Pointwise

namespace CriticalPercolation.RelativeGrowth
variable {A : Type*} [Group A]

lemma ball_smaller_stabilizer_bound (K L : Subgroup A) (hLK : L≤K)
    [Finite (K ⧸ L.subgroupOf K)] (S : Set A) (n : ℕ)
    (hf : (ball K S n).Finite) :
    (ball L S n).Finite ∧ (ball L S n).ncard≤(ball K S n).ncard*Nat.card (K ⧸ L.subgroupOf K) := by
  let e := Subgroup.quotientEquivProdOfLE hLK
  have hsub : e '' ball L S n ⊆ ball K S n ×ˢ (Set.univ : Set (K ⧸ L.subgroupOf K)) := by
    rintro _ ⟨_,⟨g,hg,rfl⟩,rfl⟩
    exact ⟨⟨g,hg,rfl⟩,Set.mem_univ _⟩
  have hprod := hf.prod (Set.finite_univ : (Set.univ : Set (K ⧸ L.subgroupOf K)).Finite)
  have hfin : (ball L S n).Finite := (hprod.subset hsub).of_finite_image e.injective.injOn
  refine ⟨hfin,?_⟩
  have hc := Set.ncard_le_ncard hsub hprod
  rw [Set.ncard_image_of_injective _ e.injective,Set.ncard_prod,Set.ncard_univ] at hc
  exact hc

lemma HasDegree.smaller_stabilizer {K L : Subgroup A} (hLK : L≤K)
    [Finite (K ⧸ L.subgroupOf K)] {S : Set A} {d : ℕ} (hg : HasDegree K S d) :
    HasDegree L S d := by
  obtain ⟨hf,C,hC⟩ := hg
  refine ⟨fun n => (ball_smaller_stabilizer_bound K L hLK S n (hf n)).1,
    C*Nat.card (K ⧸ L.subgroupOf K),?_⟩
  intro R
  obtain ⟨n,hn,hbound⟩ := hC R
  refine ⟨n,hn,?_⟩
  have hh := (ball_smaller_stabilizer_bound K L hLK S n (hf n)).2
  calc
    _ ≤ (ball K S n).ncard*Nat.card (K ⧸ L.subgroupOf K) := hh
    _ ≤ (C*n^d)*Nat.card (K ⧸ L.subgroupOf K) := Nat.mul_le_mul_right _ hbound
    _ = _ := by ring

end CriticalPercolation.RelativeGrowth
end
end

end OAI
