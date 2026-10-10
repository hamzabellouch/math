import Mathlib
import OAI.Probability.CriticalPercolation.Growth.CosetBallIndex
import OAI.Probability.CriticalPercolation.Growth.CosetSparseGrowth

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical Pointwise

namespace CriticalPercolation.RelativeGrowth
variable {A : Type*} [Group A]

def Bounded (S T : Set A) : Prop := ∃ n : ℕ, T⊆S^n
lemma bounded_singleton (S : Set A) (h1 : (1:A)∈S) (hi : S⁻¹=S)
    (hg : Subgroup.closure S=⊤) (a : A) : Bounded S {a} := by
  have ha : a∈Subgroup.closure S := hg.symm ▸ Subgroup.mem_top a
  suffices ∃ n, a∈S^n by simpa [Bounded] using this
  induction ha using Subgroup.closure_induction with
  | mem a ha => exact ⟨1,by simpa using ha⟩
  | one => exact ⟨1,by simpa using h1⟩
  | mul a b _ _ ha hb =>
    obtain ⟨n,hn⟩ := ha; obtain ⟨m,hm⟩ := hb
    exact ⟨n+m,by rw [pow_add]; exact Set.mul_mem_mul hn hm⟩
  | inv a _ ha =>
    obtain ⟨n,hn⟩ := ha
    refine ⟨n,?_⟩
    rw [←hi,inv_pow]
    exact Set.inv_mem_inv.mpr hn
lemma bounded_finite (S : Set A) (h1 : (1:A)∈S) (hi : S⁻¹=S)
    (hg : Subgroup.closure S=⊤) {F : Set A} (hf : F.Finite) : Bounded S F := by
  have hh : ∀ f∈F, ∃ n, f∈S^n := by
    intro f hf
    obtain ⟨n,hn⟩ := bounded_singleton S h1 hi hg f
    exact ⟨n,hn (Set.mem_singleton _)⟩
  choose n hn using hh
  let L := hf.toFinset.sup (fun a => if ha : a∈F then n a ha else 0)
  refine ⟨L,?_⟩
  intro a ha
  apply Set.pow_subset_pow_right h1 (show n a ha≤L from ?_) (hn a ha)
  have hh := Finset.le_sup (f:=fun a => if ha : a∈F then n a ha else 0) (hf.mem_toFinset.mpr ha)
  simpa only [dite_eq_left ha] using hh
lemma Bounded.mono {S T U : Set A} (h : Bounded S T) (hUT : U⊆T) : Bounded S U :=
  ⟨h.choose,hUT.trans h.choose_spec⟩
lemma Bounded.mul {S T U : Set A} (hT : Bounded S T) (hU : Bounded S U) : Bounded S (T*U) := by
  obtain ⟨n,hn⟩ := hT; obtain ⟨m,hm⟩ := hU
  exact ⟨n+m,by rw [pow_add]; exact Set.mul_subset_mul hn hm⟩
lemma Bounded.inv {S T : Set A} (hi : S⁻¹=S) (hT : Bounded S T) : Bounded S T⁻¹ := by
  obtain ⟨n,hn⟩ := hT
  refine ⟨n,?_⟩
  rw [←hi,inv_pow]
  exact Set.inv_subset_inv.mpr hn
lemma Bounded.union {S T U : Set A} (h1 : (1:A)∈S)
    (hT : Bounded S T) (hU : Bounded S U) : Bounded S (T∪U) := by
  obtain ⟨n,hn⟩ := hT; obtain ⟨m,hm⟩ := hU
  exact ⟨max n m,Set.union_subset (hn.trans (Set.pow_subset_pow_right h1 (le_max_left _ _)))
    (hm.trans (Set.pow_subset_pow_right h1 (le_max_right _ _)))⟩

lemma finite_coset_image_iff_cover (K : Subgroup A) (T : Set A) :
    ((QuotientGroup.mk : A → A ⧸ K) '' T).Finite ↔
      ∃ F : Set A, F.Finite ∧ T⊆F*(K:Set A) := by
  constructor
  · intro hf
    let Q := (QuotientGroup.mk : A → A ⧸ K) '' T
    have hh : ∀ q∈Q, ∃ a∈T, (QuotientGroup.mk a : A ⧸ K)=q := fun q hq => hq
    choose a ha he using hh
    let F := Set.range (fun q : Q => a q.val q.property)
    let : Finite Q := hf.to_subtype
    refine ⟨F,Set.finite_range _,?_⟩
    intro t ht
    let q : Q := ⟨QuotientGroup.mk t,⟨t,ht,rfl⟩⟩
    refine ⟨a q.val q.property,⟨q,rfl⟩,(a q.val q.property)⁻¹*t,?_,by simp⟩
    exact QuotientGroup.eq.mp (he q.val q.property)
  · rintro ⟨F,hF,hcov⟩
    apply (hF.image (QuotientGroup.mk : A → A ⧸ K)).subset
    rintro _ ⟨t,ht,rfl⟩
    obtain ⟨f,hf,k,hk,rfl⟩ := hcov ht
    exact ⟨f,hf,QuotientGroup.eq.mpr (by simpa using hk)⟩

lemma bounded_of_finite_coset_image (S : Set A) (K : Subgroup A)
    (h1 : (1:A)∈S) (hi : S⁻¹=S) (hg : Subgroup.closure S=⊤) (hK : Bounded S (K:Set A))
    (T : Set A) (hf : ((QuotientGroup.mk : A → A ⧸ K) '' T).Finite) : Bounded S T := by
  obtain ⟨F,hF,hcov⟩ := (finite_coset_image_iff_cover K T).mp hf
  exact ((bounded_finite S h1 hi hg hF).mul hK).mono hcov
lemma finite_coset_image_of_bounded (K : Subgroup A) (S T : Set A)
    (hf : ∀ n, (ball K S n).Finite) (hT : Bounded S T) :
    ((QuotientGroup.mk : A → A ⧸ K) '' T).Finite := by
  obtain ⟨n,hn⟩ := hT
  exact (hf n).subset (Set.image_mono hn)

lemma HasDegree.bounded_generators {K : Subgroup A} {S T : Set A} {d : ℕ}
    (h1 : (1:A)∈S) (hg : HasDegree K S d) (hT : Bounded S T) : HasDegree K T d := by
  obtain ⟨L,hL⟩ := hT
  have hin (n : ℕ) : T^n⊆S^((L+1)*n) := by
    rw [pow_mul]
    exact Set.pow_subset_pow_left (hL.trans (Set.pow_subset_pow_right h1 (Nat.le_succ L)))
  refine ⟨fun n => (hg.1 _).subset (Set.image_mono (hin n)),?_⟩
  obtain ⟨C,hC⟩ := hg.2
  refine ⟨C*(2*(L+1))^d,?_⟩
  intro R
  obtain ⟨r,hr,hbound⟩ := hC ((L+1)*max R 1)
  let n := r/(L+1)
  have hn : max R 1≤n := (Nat.le_div_iff_mul_le (by omega : 0<L+1)).mpr (by simpa [Nat.mul_comm] using hr)
  have hnr : (L+1)*n≤r := by simpa only [n,Nat.mul_comm] using Nat.div_mul_le_self r (L+1)
  have hrn : r≤(2*(L+1))*n := by
    have hlt := Nat.lt_mul_div_succ r (by omega : 0<L+1)
    change r<(L+1)*(n+1) at hlt
    have hh : 1≤n := (le_max_right R 1).trans hn
    nlinarith
  refine ⟨n,(le_max_left R 1).trans hn,?_⟩
  calc
    _ ≤ (ball K S r).ncard := Set.ncard_le_ncard
      (Set.image_mono ((hin n).trans (Set.pow_subset_pow_right h1 hnr))) (hg.1 r)
    _ ≤ C*r^d := hbound
    _ ≤ C*((2*(L+1))*n)^d := Nat.mul_le_mul_left C (Nat.pow_le_pow_left hrn d)
    _ = _ := by rw [mul_pow]; ring

lemma HasDegree.zero_finiteIndex {K : Subgroup A} {S : Set A}
    (h1 : (1:A)∈S) (hi : S⁻¹=S) (hgen : Subgroup.closure S=⊤)
    (hg : HasDegree K S 0) : K.FiniteIndex := by
  obtain ⟨C,hC⟩ := hg.2
  obtain ⟨n,hn,hb⟩ := hC C
  apply CosetGrowth.finiteIndex_of_small_ball S K h1 hi hgen n (hg.1 n)
  exact (by simpa using hb : (ball K S n).ncard≤C).trans hn

end CriticalPercolation.RelativeGrowth
end
end

end OAI
