import Mathlib

namespace OAI

/-! Locally finite real exponent supports, finite convolution and negative words. -/

noncomputable section
open Set Filter Topology Metric Polynomial
open scoped BigOperators NNReal ENNReal

open Set
namespace DegeneratingTrees.Clock

def exponentSum (E F : Set ℝ) : Set ℝ := (fun p : ℝ×ℝ => p.1+p.2) '' (E ×ˢ F)
def exponentPairs (E F : Set ℝ) (B : ℝ) : Set (ℝ×ℝ) :=
  {p | p.1 ∈ E ∧ p.2 ∈ F ∧ B ≤ p.1+p.2}
def exponentFiber (E F : Set ℝ) (δ : ℝ) : Set (ℝ×ℝ) :=
  {p | p.1 ∈ E ∧ p.2 ∈ F ∧ p.1+p.2=δ}

lemma exponentPairs_finite {E F : Set ℝ} (hE : BddAbove E) (hF : BddAbove F)
    (hEl : ∀ B : ℝ, (E ∩ Ici B).Finite) (hFl : ∀ B : ℝ, (F ∩ Ici B).Finite) (B : ℝ) :
    (exponentPairs E F B).Finite := by
  obtain ⟨A,hA⟩ := hE
  obtain ⟨C,hC⟩ := hF
  apply ((hEl (B-C)).prod (hFl (B-A))).subset
  intro p hp
  exact ⟨⟨hp.1,by change B-C ≤ p.1; have := hC hp.2.1; linarith [hp.2.2]⟩,
    ⟨hp.2.1,by change B-A ≤ p.2; have := hA hp.1; linarith [hp.2.2]⟩⟩

lemma exponentFiber_finite {E F : Set ℝ} (hE : BddAbove E) (hF : BddAbove F)
    (hEl : ∀ B : ℝ, (E ∩ Ici B).Finite) (hFl : ∀ B : ℝ, (F ∩ Ici B).Finite) (δ : ℝ) :
    (exponentFiber E F δ).Finite :=
  (exponentPairs_finite hE hF hEl hFl δ).subset (fun _ hp => ⟨hp.1,hp.2.1,hp.2.2.ge⟩)

lemma exponentSum_bddAbove {E F : Set ℝ} (hE : BddAbove E) (hF : BddAbove F) :
    BddAbove (exponentSum E F) := by
  obtain ⟨A,hA⟩ := hE
  obtain ⟨C,hC⟩ := hF
  refine ⟨A+C,?_⟩
  rintro _ ⟨p,hp,rfl⟩
  exact add_le_add (hA hp.1) (hC hp.2)

lemma exponentSum_finite {E F : Set ℝ} (hE : BddAbove E) (hF : BddAbove F)
    (hEl : ∀ B : ℝ, (E ∩ Ici B).Finite) (hFl : ∀ B : ℝ, (F ∩ Ici B).Finite) (B : ℝ) :
    (exponentSum E F ∩ Ici B).Finite := by
  apply ((exponentPairs_finite hE hF hEl hFl B).image (fun p => p.1+p.2)).subset
  rintro δ ⟨⟨p,hp,rfl⟩,hB⟩
  exact ⟨p,⟨hp.1,hp.2,hB⟩,rfl⟩

 

lemma exponentPairs_subset_rectangle {E F : Set ℝ} {A C B U V : ℝ}
    (hA : ∀ β ∈ E, β ≤ A) (hC : ∀ γ ∈ F, γ ≤ C)
    (hU : U ≤ B-C) (hV : V ≤ B-A) :
    exponentPairs E F B ⊆ (E ∩ Ici U) ×ˢ (F ∩ Ici V) := by
  intro p hp
  exact ⟨⟨hp.1,by change U ≤ p.1; have := hC _ hp.2.1; linarith [hp.2.2]⟩,
    ⟨hp.2.1,by change V ≤ p.2; have := hA _ hp.1; linarith [hp.2.2]⟩⟩

end DegeneratingTrees.Clock

 

 

 

open Set
namespace DegeneratingTrees.Clock

private def prependPair (p : ℝ × List ℝ) : List ℝ := p.1::p.2
private lemma prependPair_injective : Function.Injective prependPair := by
  intro a b h
  exact Prod.ext (List.cons.inj h).1 (List.cons.inj h).2

def wordsOfLength (S : Finset ℝ) : ℕ → Finset (List ℝ)
  | 0 => {[]}
  | n+1 => (S ×ˢ wordsOfLength S n).image prependPair

lemma mem_wordsOfLength {S : Finset ℝ} {n : ℕ} {w : List ℝ} :
    w ∈ wordsOfLength S n ↔ w.length=n ∧ ∀ β ∈ w, β ∈ S := by
  induction n generalizing w with
  | zero =>
    simp only [wordsOfLength, Finset.mem_singleton, List.length_eq_zero_iff]
    constructor
    · intro h; subst w; simp
    · exact And.left
  | succ n ih =>
    cases w with
    | nil => simp [wordsOfLength,prependPair]
    | cons β w =>
      simp only [wordsOfLength,Finset.mem_image,Finset.mem_product]
      constructor
      · rintro ⟨⟨γ,v⟩,⟨hγ,hv⟩,he⟩
        have hh := List.cons.inj he
        dsimp [prependPair] at hh
        rcases hh with ⟨rfl,rfl⟩
        exact ⟨by simpa using congrArg Nat.succ (ih.mp hv).1,
          by simpa using And.intro hγ (ih.mp hv).2⟩
      · rintro ⟨hlen,hmem⟩
        refine ⟨(β,w),⟨hmem β (by simp),ih.mpr ⟨by simpa using hlen,?_⟩⟩,rfl⟩
        exact fun γ hγ => hmem γ (List.mem_cons_of_mem _ hγ)

def wordsUpTo (S : Finset ℝ) (N : ℕ) : Finset (List ℝ) :=
  (Finset.range (N+1)).biUnion (wordsOfLength S)

lemma mem_wordsUpTo {S : Finset ℝ} {N : ℕ} {w : List ℝ} :
    w ∈ wordsUpTo S N ↔ w.length ≤ N ∧ ∀ β ∈ w, β ∈ S := by
  simp only [wordsUpTo,Finset.mem_biUnion,Finset.mem_range,mem_wordsOfLength]
  constructor
  · rintro ⟨n,hn,he,hm⟩
    exact ⟨by omega,hm⟩
  · rintro ⟨hl,hm⟩
    exact ⟨w.length,by omega,rfl,hm⟩

def exponentWords (E : Set ℝ) : Set (List ℝ) := {w | ∀ β ∈ w, β ∈ E}
def wordCut (E : Set ℝ) (B : ℝ) : Set (List ℝ) := {w | w ∈ exponentWords E ∧ B ≤ w.sum}
def wordFiber (E : Set ℝ) (β : ℝ) : Set (List ℝ) := {w | w ∈ exponentWords E ∧ w.sum=β}
def wordSupport (E : Set ℝ) : Set ℝ := List.sum '' exponentWords E

lemma list_sum_le_length {E : Set ℝ} {δ : ℝ} (hE : ∀ β ∈ E, β ≤ -δ)
    {w : List ℝ} (hw : w ∈ exponentWords E) : w.sum ≤ -δ*(w.length:ℝ) := by
  induction w with
  | nil => simp
  | cons a w ih =>
    have ha := hE a (hw a (by simp))
    have hi := ih (fun β hβ => hw β (List.mem_cons_of_mem _ hβ))
    simp only [List.sum_cons,List.length_cons,Nat.cast_add,Nat.cast_one]
    nlinarith

lemma list_sum_le_member {E : Set ℝ} (hE : ∀ β ∈ E, β ≤ 0)
    {w : List ℝ} (hw : w ∈ exponentWords E) {β : ℝ} (hβ : β ∈ w) : w.sum ≤ β := by
  induction w with
  | nil => simp at hβ
  | cons a w ih =>
    have hwa : ∀ γ ∈ w, γ ∈ E := fun γ hγ => hw γ (List.mem_cons_of_mem _ hγ)
    have hw0 : w.sum ≤ 0 := by
      simpa using list_sum_le_length (δ := 0) (by simpa using hE) hwa
    rcases List.mem_cons.mp hβ with rfl | hβ
    · simpa only [List.sum_cons] using add_le_of_nonpos_right hw0
    · have hi := ih hwa hβ
      have ha := hE a (hw a (by simp))
      simp only [List.sum_cons]
      linarith

lemma wordCut_subset_words {E : Set ℝ} {δ B : ℝ} {N : ℕ} (hδ : 0 < δ)
    (hE : ∀ β ∈ E, β ≤ -δ) (hEl : (E ∩ Ici B).Finite)
    (hN : -δ*((N:ℝ)+1) < B) :
    wordCut E B ⊆ (wordsUpTo hEl.toFinset N : Set (List ℝ)) := by
  intro w hw
  apply mem_wordsUpTo.mpr
  constructor
  · have hs := list_sum_le_length hE hw.1
    have hlen : (w.length:ℝ) < (N:ℝ)+1 := by
      have hB : B ≤ w.sum := hw.2
      nlinarith
    exact Nat.lt_succ_iff.mp (by exact_mod_cast hlen)
  · intro β hβ
    exact hEl.mem_toFinset.mpr ⟨hw.1 β hβ,hw.2.trans
      (list_sum_le_member (fun γ hγ => (hE γ hγ).trans (by linarith)) hw.1 hβ)⟩

lemma wordCut_finite {E : Set ℝ} {δ : ℝ} (hδ : 0 < δ)
    (hE : ∀ β ∈ E, β ≤ -δ) (hEl : ∀ B : ℝ, (E ∩ Ici B).Finite) (B : ℝ) :
    (wordCut E B).Finite := by
  obtain ⟨N,hN⟩ := exists_nat_gt (-B/δ)
  have hN' : -δ*((N:ℝ)+1) < B := by
    have hn := (div_lt_iff₀ hδ).mp hN
    nlinarith
  exact (wordsUpTo (hEl B).toFinset N).finite_toSet.subset
    (wordCut_subset_words hδ hE (hEl B) hN')

lemma wordFiber_finite {E : Set ℝ} {δ : ℝ} (hδ : 0 < δ)
    (hE : ∀ β ∈ E, β ≤ -δ) (hEl : ∀ B : ℝ, (E ∩ Ici B).Finite) (β : ℝ) :
    (wordFiber E β).Finite :=
  (wordCut_finite hδ hE hEl β).subset (fun _ hw => ⟨hw.1,hw.2.ge⟩)

lemma wordSupport_bddAbove {E : Set ℝ} {δ : ℝ} (hδ : 0 ≤ δ)
    (hE : ∀ β ∈ E, β ≤ -δ) : BddAbove (wordSupport E) := by
  refine ⟨0,?_⟩
  rintro _ ⟨w,hw,rfl⟩
  exact (list_sum_le_length hE hw).trans (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hδ) (by positivity))

lemma wordSupport_finite {E : Set ℝ} {δ : ℝ} (hδ : 0 < δ)
    (hE : ∀ β ∈ E, β ≤ -δ) (hEl : ∀ B : ℝ, (E ∩ Ici B).Finite) (B : ℝ) :
    (wordSupport E ∩ Ici B).Finite := by
  apply ((wordCut_finite hδ hE hEl B).image List.sum).subset
  rintro β ⟨⟨w,hw,rfl⟩,hB⟩
  exact ⟨w,⟨hw,hB⟩,rfl⟩

end DegeneratingTrees.Clock
end

end OAI
