import Mathlib

namespace OAI

section
noncomputable section
open Set Function
open scoped Pointwise

namespace CriticalPercolation.CosetGrowth
variable {A : Type*} [Group A]

def ball (S : Set A) (L : Subgroup A) (n : ℕ) : Set (A ⧸ L) :=
  (QuotientGroup.mk : A → A ⧸ L) '' (S^n)

lemma ball_zero (S : Set A) (L : Subgroup A) : ball S L 0={QuotientGroup.mk (1 : A)} := by
  simp [ball]

lemma ball_step (S : Set A) (L : Subgroup A) (n : ℕ) :
    ball S L (n+1)=⋃ s∈S, (fun q : A ⧸ L => s • q) '' ball S L n := by
  ext q
  simp only [ball,pow_succ',Set.mem_image,Set.mem_mul,Set.mem_iUnion]
  constructor
  · rintro ⟨_,⟨s,hs,a,ha,rfl⟩,rfl⟩
    exact ⟨s,hs,QuotientGroup.mk a,⟨a,ha,rfl⟩,rfl⟩
  · rintro ⟨s,hs,_,⟨a,ha,rfl⟩,rfl⟩
    exact ⟨s*a,⟨s,hs,a,ha,rfl⟩,rfl⟩

lemma ball_mono (S : Set A) (L : Subgroup A) (h1 : (1 : A)∈S) :
    Monotone (ball S L) := fun _ _ h => Set.image_mono (Set.pow_subset_pow_right h1 h)

lemma ball_one_mem (S : Set A) (L : Subgroup A) (h1 : (1 : A)∈S) (n : ℕ) :
    QuotientGroup.mk (1 : A)∈ball S L n := by
  apply ball_mono S L h1 (Nat.zero_le n)
  rw [ball_zero]
  exact Set.mem_singleton _

lemma ball_eq_univ_of_stationary (S : Set A) (L : Subgroup A)
    (h1 : (1 : A)∈S) (hinv : S⁻¹=S) (hgen : Subgroup.closure S=⊤)
    (n : ℕ) (hstop : ball S L (n+1)=ball S L n) : ball S L n=Set.univ := by
  have hstable : ∀ s∈S, ∀ q∈ball S L n, s • q∈ball S L n := by
    intro s hs q hq
    rw [←hstop,ball_step]
    exact Set.mem_iUnion.mpr ⟨s,Set.mem_iUnion.mpr ⟨hs,⟨q,hq,rfl⟩⟩⟩
  have hS : S⊆MulAction.stabilizer A (ball S L n) := by
    intro s hs
    change (fun q : A ⧸ L => s • q) '' ball S L n=ball S L n
    apply Set.Subset.antisymm
    · rintro _ ⟨q,hq,rfl⟩
      exact hstable s hs q hq
    · intro q hq
      have hi : s⁻¹∈S := by rw [←hinv]; simpa only [Set.mem_inv,inv_inv] using hs
      exact ⟨s⁻¹ • q,hstable _ hi _ hq,smul_inv_smul s q⟩
  have hall : ∀ g : A, g • ball S L n=ball S L n := by
    have hh := (Subgroup.closure_le (MulAction.stabilizer A (ball S L n))).mpr hS
    rw [hgen] at hh
    exact fun g => hh (Subgroup.mem_top g)
  apply Set.eq_univ_of_forall
  intro q
  obtain ⟨g,rfl⟩ := QuotientGroup.mk_surjective q
  have hh : g • (QuotientGroup.mk (1 : A) : A ⧸ L)∈ball S L n := by
    rw [←hall g]
    exact ⟨_,ball_one_mem S L h1 n,rfl⟩
  simpa only [MulAction.Quotient.smul_mk,smul_eq_mul,mul_one] using hh

lemma finiteIndex_of_small_ball (S : Set A) (L : Subgroup A)
    (h1 : (1 : A)∈S) (hinv : S⁻¹=S) (hgen : Subgroup.closure S=⊤)
    (n : ℕ) (hfin : (ball S L n).Finite) (hsmall : (ball S L n).ncard≤n) :
    L.FiniteIndex := by
  have hmon := ball_mono S L h1
  have hfi : ∀ i≤n, (ball S L i).Finite := fun i hi => hfin.subset (hmon hi)
  have hs : ∃ i<n, ball S L (i+1)=ball S L i := by
    by_contra! h
    have hg : ∀ i≤n, i+1≤(ball S L i).ncard := by
      intro i hi
      induction i with
      | zero => simp [ball_zero]
      | succ i ih =>
        have hle := ih (by omega)
        have hlt : (ball S L i).ncard<(ball S L (i+1)).ncard := by
          apply Set.ncard_lt_ncard
          · exact Set.ssubset_iff_subset_ne.mpr ⟨hmon (Nat.le_succ i),Ne.symm (h i (by omega))⟩
          · exact hfi _ hi
        omega
    have := hg n le_rfl
    omega
  obtain ⟨i,hi,he⟩ := hs
  have heq := ball_eq_univ_of_stationary S L h1 hinv hgen i he
  have hf : (Set.univ : Set (A ⧸ L)).Finite := heq ▸ hfi i (by omega)
  let _ : Finite (A ⧸ L) := Set.finite_univ_iff.mp hf
  exact Subgroup.finiteIndex_of_finite_quotient

lemma ball_subset_coset_representatives (S : Set A) (L : Subgroup A)
    (n : ℕ) (F : Finset A) (hcover : S^n⊆(F : Set A)*(L : Set A)) :
    ball S L n⊆(QuotientGroup.mk : A → A ⧸ L) '' (F : Set A) := by
  rintro q ⟨a,ha,rfl⟩
  obtain ⟨g,hg,l,hl,rfl⟩ := hcover ha
  refine ⟨g,hg,?_⟩
  apply (@QuotientGroup.eq A _ L g (g*l)).mpr
  rw [inv_mul_cancel_left]
  exact hl

theorem finiteIndex_of_few_cosets (S : Set A) (L : Subgroup A)
    (h1 : (1 : A)∈S) (hinv : S⁻¹=S) (hgen : Subgroup.closure S=⊤)
    (n : ℕ) (F : Finset A) (hF : F.card≤n)
    (hcover : S^n⊆(F : Set A)*(L : Set A)) : L.FiniteIndex := by
  have hi := ball_subset_coset_representatives S L n F hcover
  have hfin := (F.finite_toSet.image (QuotientGroup.mk : A → A ⧸ L)).subset hi
  apply finiteIndex_of_small_ball S L h1 hinv hgen n hfin
  apply (Set.ncard_le_ncard hi (F.finite_toSet.image _)).trans
  apply (Set.ncard_image_le F.finite_toSet).trans
  simpa using hF

end CriticalPercolation.CosetGrowth
end
end

end OAI
