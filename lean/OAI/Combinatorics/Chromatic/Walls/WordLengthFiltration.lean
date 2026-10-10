import Mathlib

namespace OAI

section
namespace ElementaryPositivity
open scoped BigOperators
variable {J A : Type*} [Ring A]

noncomputable def wordProduct (b : J → A) (l : List J) : A := (l.map b).prod
lemma wordProduct_nil (b : J → A) : wordProduct b []=1 := rfl
lemma wordProduct_cons (b : J → A) (i : J) (l : List J) :
    wordProduct b (i::l)=b i*wordProduct b l := rfl
lemma wordProduct_append (b : J → A) (l m : List J) :
    wordProduct b (l++m)=wordProduct b l*wordProduct b m := by
  simp only [wordProduct,List.map_append,List.prod_append]

variable [Algebra ℚ A]

noncomputable def wordLengthFiltration (b : J → A) (n : ℕ) : Submodule ℚ A :=
  Submodule.span ℚ {x | ∃ l : List J,l.length ≤ n ∧ wordProduct b l=x}

lemma wordLengthFiltration_word (b : J → A) (l : List J) (n : ℕ) (h : l.length≤n) :
    wordProduct b l ∈ wordLengthFiltration b n := Submodule.subset_span ⟨l,h,rfl⟩

lemma wordLengthFiltration_mono (b : J → A) {m n : ℕ} (h : m≤n) :
    wordLengthFiltration b m ≤ wordLengthFiltration b n :=
  Submodule.span_mono (fun _ ⟨l,hl,hx⟩=>⟨l,hl.trans h,hx⟩)

lemma wordLengthFiltration_letter (b : J → A) (i : J) : b i ∈ wordLengthFiltration b 1 := by
  simpa only [wordProduct_cons,wordProduct_nil,mul_one] using wordLengthFiltration_word b [i] 1 le_rfl

lemma wordLengthFiltration_one (b : J → A) (n : ℕ) : (1:A) ∈ wordLengthFiltration b n :=
  wordLengthFiltration_word b [] n (Nat.zero_le n)

lemma wordLengthFiltration_mul (b : J → A) {m n : ℕ} {x y : A}
    (hx : x ∈ wordLengthFiltration b m) (hy : y ∈ wordLengthFiltration b n) :
    x*y ∈ wordLengthFiltration b (m+n) := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨l,hl,rfl⟩ := hx
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨k,hk,rfl⟩ := hy
      rw [← wordProduct_append]
      exact wordLengthFiltration_word b (l++k) (m+n) (by simpa using Nat.add_le_add hl hk)
    | zero => simpa only [mul_zero] using (wordLengthFiltration b (m+n)).zero_mem
    | add x y hx hy hxi hyi => simpa only [mul_add] using (wordLengthFiltration b (m+n)).add_mem hxi hyi
    | smul r x hx hxi => simpa only [Algebra.mul_smul_comm] using (wordLengthFiltration b (m+n)).smul_mem r hxi
  | zero => simpa only [zero_mul] using (wordLengthFiltration b (m+n)).zero_mem
  | add x z hx hz hxi hzi => simpa only [add_mul] using (wordLengthFiltration b (m+n)).add_mem hxi hzi
  | smul r x hx hxi => simpa only [Algebra.smul_mul_assoc] using (wordLengthFiltration b (m+n)).smul_mem r hxi

lemma wordLengthFiltration_span_range (b : J → A) :
    Submodule.span ℚ (Set.range b) ≤ wordLengthFiltration b 1 := by
  apply Submodule.span_le.mpr
  rintro x ⟨i,rfl⟩
  exact wordLengthFiltration_letter b i

lemma adjoin_le_span_words (b : J → A) :
    (Algebra.adjoin ℚ (Set.range b)).toSubmodule ≤
      Submodule.span ℚ (Set.range (wordProduct b)) := by
  let S := Submodule.span ℚ (Set.range (wordProduct b))
  have hm : ∀ x∈S,∀ y∈S,x*y∈S := by
    intro x hx y hy
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨l,rfl⟩ := hx
      induction hy using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨k,rfl⟩ := hy
        rw [←wordProduct_append]
        exact Submodule.subset_span ⟨l++k,rfl⟩
      | zero => simpa only [mul_zero] using S.zero_mem
      | add x y hx hy hxi hyi => simpa only [mul_add] using S.add_mem hxi hyi
      | smul r x hx hxi => simpa only [Algebra.mul_smul_comm] using S.smul_mem r hxi
    | zero => simpa only [zero_mul] using S.zero_mem
    | add x z hx hz hxi hzi => simpa only [add_mul] using S.add_mem hxi hzi
    | smul r x hx hxi => simpa only [Algebra.smul_mul_assoc] using S.smul_mem r hxi
  let T : Subalgebra ℚ A :=
    { S with
      one_mem' := Submodule.subset_span ⟨[],rfl⟩
      mul_mem' := fun hx hy=>hm _ hx _ hy
      algebraMap_mem' := fun r=>by
        rw [Algebra.algebraMap_eq_smul_one]
        exact S.smul_mem r (Submodule.subset_span ⟨[],rfl⟩) }
  have h : Algebra.adjoin ℚ (Set.range b) ≤ T := by
    apply Algebra.adjoin_le
    rintro x ⟨i,rfl⟩
    change b i∈S
    have hi : wordProduct b [i]∈S := Submodule.subset_span ⟨[i],rfl⟩
    simpa only [wordProduct_cons,wordProduct_nil,mul_one] using hi
  exact h

end ElementaryPositivity

end

end OAI
