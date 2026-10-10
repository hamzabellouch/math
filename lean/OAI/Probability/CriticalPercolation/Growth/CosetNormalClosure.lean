import Mathlib
import OAI.Probability.CriticalPercolation.Growth.CosetSparseGrowth

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical Pointwise

namespace CriticalPercolation.RelativeGrowth
variable {A : Type*} [Group A]

def boundedConjugates (S F : Set A) (n : ℕ) : Set A :=
  {x | ∃ g∈S^n, ∃ f∈F, g*f*g⁻¹=x}

def conjugateStage (S F : Set A) (n : ℕ) : Subgroup A :=
  Subgroup.closure (boundedConjugates S F n : Set A)

lemma mem_boundedConjugates (S F : Set A) (n : ℕ) {x : A} :
    x∈boundedConjugates S F n ↔ ∃ g∈S^n, ∃ f∈F, g*f*g⁻¹=x := by
  rfl

lemma boundedConjugates_mono (S F : Set A) (h1 : (1:A)∈S) :
    Monotone (boundedConjugates S F) := by
  intro m n h x hx
  obtain ⟨g,hg,f,hf,rfl⟩ := (mem_boundedConjugates S F m).mp hx
  exact (mem_boundedConjugates S F n).mpr
    ⟨g,Set.pow_subset_pow_right h1 h hg,f,hf,rfl⟩

lemma conjugateStage_mono (S F : Set A) (h1 : (1:A)∈S) :
    Monotone (conjugateStage S F) := by
  intro m n h
  exact Subgroup.closure_mono (boundedConjugates_mono S F h1 h)

lemma boundedConjugates_subset_pow (S F : Set A) (hsym : S⁻¹=S)
    (L : ℕ) (hF : F⊆S^L) (n : ℕ) :
    boundedConjugates S F n ⊆ S^(2*n+L) := by
  intro x hx
  obtain ⟨g,hg,f,hf,rfl⟩ := (mem_boundedConjugates S F n).mp hx
  have hgi : g⁻¹∈S^n := by
    rw [←hsym,inv_pow]
    exact Set.inv_mem_inv.mpr hg
  have he : 2*n+L=n+L+n := by omega
  rw [he,pow_add,pow_add]
  exact Set.mul_mem_mul (Set.mul_mem_mul hg (hF hf)) hgi

lemma conjugateStage_le_normalClosure (S F : Set A) (n : ℕ) :
    conjugateStage S F n ≤ Subgroup.normalClosure (F : Set A) := by
  apply (Subgroup.closure_le _).mpr
  intro x hx
  obtain ⟨g,hg,f,hf,rfl⟩ := (mem_boundedConjugates S F n).mp hx
  exact Subgroup.normalClosure_normal.conj_mem f (Subgroup.subset_normalClosure hf) g

lemma conjugateStage_conj_generator (S F : Set A) (n : ℕ)
    (s : A) (hs : s∈S) {x : A} (hx : x∈conjugateStage S F n) :
    s*x*s⁻¹∈conjugateStage S F (n+1) := by
  change x∈Subgroup.closure _ at hx
  have hmap : conjugateStage S F n ≤
      (conjugateStage S F (n+1)).comap (MulAut.conj s) := by
    apply (Subgroup.closure_le _).mpr
    intro y hy
    obtain ⟨g,hg,f,hf,rfl⟩ := (mem_boundedConjugates S F n).mp hy
    apply Subgroup.subset_closure
    apply (mem_boundedConjugates S F (n+1)).mpr
    refine ⟨s*g,?_,f,hf,?_⟩
    · rw [pow_succ']
      exact Set.mul_mem_mul hs hg
    · simp [MulAut.conj_apply,mul_assoc]
  exact hmap hx

lemma conjugateStage_normal_of_stationary (S F : Set A) (hsym : S⁻¹=S)
    (hgen : Subgroup.closure (S : Set A)=⊤) (n : ℕ)
    (he : conjugateStage S F (n+1)=conjugateStage S F n) :
    (conjugateStage S F n).Normal := by
  rw [←Subgroup.normalizer_eq_top_iff]
  apply top_unique
  rw [←hgen]
  apply (Subgroup.closure_le _).mpr
  intro s hs
  change ∀ x, x∈conjugateStage S F n ↔ s*x*s⁻¹∈conjugateStage S F n
  intro x
  constructor
  · intro hx
    rw [←he]
    exact conjugateStage_conj_generator S F n s hs hx
  · intro hx
    have hsi : s⁻¹∈S := by rw [←hsym]; exact Set.inv_mem_inv.mpr hs
    have hy := conjugateStage_conj_generator S F n s⁻¹ hsi hx
    rw [he] at hy
    simpa only [inv_inv, mul_assoc, inv_mul_cancel_left, mul_inv_cancel_right, inv_mul_cancel, mul_one] using hy

lemma normalClosure_eq_conjugateStage_of_stationary (S F : Set A)
    (h1 : (1:A)∈S) (hsym : S⁻¹=S) (hgen : Subgroup.closure (S : Set A)=⊤)
    (n : ℕ) (he : conjugateStage S F (n+1)=conjugateStage S F n) :
    Subgroup.normalClosure (F : Set A)=conjugateStage S F n := by
  let _ := conjugateStage_normal_of_stationary S F hsym hgen n he
  apply le_antisymm
  · apply Subgroup.normalClosure_le_normal
    intro f hf
    apply Subgroup.subset_closure
    exact (mem_boundedConjugates S F n).mpr
      ⟨1,Set.one_mem_pow h1,f,hf,by simp⟩
  · exact conjugateStage_le_normalClosure S F n

theorem exists_conjugateStage_stationary (S F : Set A)
    (h1 : (1:A)∈S) (hsym : S⁻¹=S) (K : Subgroup A) (hK : K≤Subgroup.closure F) (d : ℕ) (hg : HasDegree K S d)
    (L : ℕ) (hF : F⊆S^L) :
    ∃ n : ℕ, conjugateStage S F (n+1)=conjugateStage S F n := by
  by_contra! hn
  have hw : ∀ n : ℕ, ∃ x∈boundedConjugates S F (n+1), x∉conjugateStage S F n := by
    intro n
    by_contra! h
    apply hn n
    apply le_antisymm ((Subgroup.closure_le _).mpr h)
    exact conjugateStage_mono S F h1 (Nat.le_succ n)
  choose g hgin hgout using hw
  have hbase : K≤conjugateStage S F 0 := hK.trans (Subgroup.closure_mono (by
    intro f hf
    exact ⟨1,by simp,f,hf,by simp⟩))
  apply no_linear_strict_chain K S h1 d hg (conjugateStage S F)
    (conjugateStage_mono S F h1) hbase g (fun n => Subgroup.subset_closure (hgin n))
    hgout (L+2) (by omega)
  intro n
  apply Set.pow_subset_pow_right h1 (show 2*(n+1)+L≤(L+2)*(n+1) by nlinarith)
  exact boundedConjugates_subset_pow S F hsym L hF (n+1) (hgin n)

end CriticalPercolation.RelativeGrowth
end
end

end OAI
