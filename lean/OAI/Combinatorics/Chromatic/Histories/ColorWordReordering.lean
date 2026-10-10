import Mathlib
import OAI.Combinatorics.Chromatic.Walls.WordLengthFiltration

namespace OAI

section
namespace ElementaryPositivity
variable {J A : Type*} [Ring A] [Algebra ℚ A]
variable (b : J → A) (ε : J → J → ℚ)

lemma wordProduct_perm_mod_lower
    (hε : ∀ i j,ε i j ≠ 0)
    (hcomm : ∀ i j,b i*b j-ε i j • (b j*b i) ∈ wordLengthFiltration b 1)
    {l m : List J} (h : l.Perm m) :
    ∃ r : ℚ,r ≠ 0 ∧ wordProduct b l-r • wordProduct b m ∈ wordLengthFiltration b (l.length-1) := by
  induction h with
  | nil => exact ⟨1,one_ne_zero,by simp⟩
  | @cons i l m hp ih =>
    by_cases hl : l=[]
    · subst l
      have hm : m=[] := List.nil_perm.mp hp
      subst m
      exact ⟨1,one_ne_zero,by simp⟩
    obtain ⟨r,hr,hd⟩ := ih
    refine ⟨r,hr,?_⟩
    have hh := wordLengthFiltration_mul b (wordLengthFiltration_letter b i) hd
    have he : 1+(l.length-1)=(i::l).length-1 := by
      have hn := List.length_pos_iff.mpr hl
      simp only [List.length_cons]
      omega
    rw [he] at hh
    simpa only [wordProduct_cons,mul_sub,Algebra.mul_smul_comm] using hh
  | swap i j l =>
    refine ⟨ε j i,hε j i,?_⟩
    have hh := wordLengthFiltration_mul b (hcomm j i) (wordLengthFiltration_word b l l.length le_rfl)
    have he : 1+l.length=(j::i::l).length-1 := by simp; omega
    rw [he] at hh
    simpa only [wordProduct_cons,sub_mul,Algebra.smul_mul_assoc,mul_assoc] using hh
  | @trans l m n hlm hmn ihl ihm =>
    obtain ⟨r,hr,hdl⟩ := ihl
    obtain ⟨s,hs,hdm⟩ := ihm
    refine ⟨r*s,mul_ne_zero hr hs,?_⟩
    rw [←hlm.length_eq] at hdm
    have hh := (wordLengthFiltration b (l.length-1)).add_mem hdl
      ((wordLengthFiltration b (l.length-1)).smul_mem r hdm)
    simpa only [smul_sub,smul_smul,sub_add_sub_cancel] using hh

section Ordered
variable [LinearOrder J]

def ColorAdmissible (l : List J) : Prop :=
  l.Pairwise (fun i j=>i≤j ∧ (i=j → ε i i=1))

lemma colorAdmissible_sorted {l : List J} (h : ColorAdmissible ε l) : l.Pairwise (· ≤ ·) :=
  h.imp (fun h=>h.1)

lemma sorted_not_colorAdmissible {l : List J} (hl : l.Pairwise (· ≤ ·))
    (hn : ¬ColorAdmissible ε l) : ∃ i t,ε i i ≠ 1 ∧ l.Perm (i::i::t) := by
  induction l with
  | nil => exact (hn (by simp [ColorAdmissible])).elim
  | cons j l ih =>
    have hlc := List.pairwise_cons.mp hl
    by_cases ht : ColorAdmissible ε l
    · have hj : ¬∀ i∈l,j ≤ i ∧ (j=i → ε j j=1) := by
        intro hh
        exact hn (List.pairwise_cons.mpr ⟨hh,ht⟩)
      obtain ⟨i,hi⟩ := not_forall.mp hj
      obtain ⟨hi,hbad⟩ := Classical.not_imp.mp hi
      have heq : j=i := by
        by_contra hne
        exact hbad ⟨hlc.1 i hi,fun h=>False.elim (hne h)⟩
      subst i
      have he : ε j j ≠ 1 := fun h=>hbad ⟨le_rfl,fun _=>h⟩
      obtain ⟨u,v,rfl⟩ := List.mem_iff_append.mp hi
      exact ⟨j,u++v,he,List.Perm.cons j List.perm_middle⟩
    · obtain ⟨i,t,he,hp⟩ := ih hlc.2 ht
      refine ⟨i,j::t,he,?_⟩
      exact (hp.cons j).trans ((List.Perm.swap i j (i::t)).trans
        (List.Perm.cons i (List.Perm.swap i j t)))

noncomputable def colorWordSpan : Submodule ℚ A :=
  Submodule.span ℚ {x | ∃ l : List J,ColorAdmissible ε l ∧ wordProduct b l=x}

lemma colorWordSpan_admissible (l : List J) (hl : ColorAdmissible ε l) :
    wordProduct b l ∈ colorWordSpan b ε := Submodule.subset_span ⟨l,hl,rfl⟩

theorem colorWordSpan_word
    (hε : ∀ i j,ε i j ≠ 0)
    (hcomm : ∀ i j,b i*b j-ε i j • (b j*b i) ∈ wordLengthFiltration b 1)
    (hsquare : ∀ i,ε i i ≠ 1 → b i*b i ∈ wordLengthFiltration b 1)
    (l : List J) : wordProduct b l ∈ colorWordSpan b ε := by
  have hmain : ∀ n,∀ l : List J,l.length=n → wordProduct b l ∈ colorWordSpan b ε := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro l hl
      by_cases hn : n=0
      · have hnil : l=[] := List.length_eq_zero_iff.mp (hl.trans hn)
        rw [hnil]
        exact colorWordSpan_admissible b ε [] (by simp [ColorAdmissible])
      have hlow : wordLengthFiltration b (n-1) ≤ colorWordSpan b ε := by
        apply Submodule.span_le.mpr
        rintro x ⟨t,ht,rfl⟩
        exact ih t.length (by omega) t rfl
      let m := l.insertionSort (· ≤ ·)
      have hm : m.Pairwise (· ≤ ·) := List.pairwise_insertionSort _ _
      have hpm : l.Perm m := (List.perm_insertionSort _ l).symm
      have htransfer : ∀ t : List J,l.Perm t → wordProduct b t ∈ colorWordSpan b ε →
          wordProduct b l ∈ colorWordSpan b ε := by
        intro t hp ht
        obtain ⟨r,hr,hd⟩ := wordProduct_perm_mod_lower b ε hε hcomm hp
        rw [hl] at hd
        have hh := (colorWordSpan b ε).add_mem (hlow hd) ((colorWordSpan b ε).smul_mem r ht)
        simpa only [sub_add_cancel] using hh
      by_cases ha : ColorAdmissible ε m
      · exact htransfer m hpm (colorWordSpan_admissible b ε m ha)
      · obtain ⟨i,t,hi,hpt⟩ := sorted_not_colorAdmissible ε hm ha
        apply htransfer (i::i::t) (hpm.trans hpt)
        have hh := wordLengthFiltration_mul b (hsquare i hi) (wordLengthFiltration_word b t t.length le_rfl)
        have hlen : 1+t.length=n-1 := by
          have he := (hpm.trans hpt).length_eq
          simp only [List.length_cons] at he
          omega
        rw [hlen] at hh
        apply hlow
        simpa only [wordProduct_cons,mul_assoc] using hh
  exact hmain l.length l rfl

lemma colorWordSpan_top
    (hε : ∀ i j,ε i j ≠ 0)
    (hcomm : ∀ i j,b i*b j-ε i j • (b j*b i) ∈ wordLengthFiltration b 1)
    (hsquare : ∀ i,ε i i ≠ 1 → b i*b i ∈ wordLengthFiltration b 1)
    (hgen : Algebra.adjoin ℚ (Set.range b)=⊤) : colorWordSpan b ε=⊤ := by
  apply top_unique
  have ha := adjoin_le_span_words b
  rw [hgen] at ha
  apply le_trans ha
  apply Submodule.span_le.mpr
  rintro x ⟨l,rfl⟩
  exact colorWordSpan_word b ε hε hcomm hsquare l

end Ordered
end ElementaryPositivity

end

end OAI
