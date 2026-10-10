import Mathlib
import OAI.Probability.SKGap.Matrix.MarkedWordIBP

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius SchwartzMap
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma matrix_word_contraction_left (U V Q : Matrix ι ι ℝ) (i : ι) :
    (∑ a,∑ b,(U*symmetricElementary a b*V) i a*Q b i)=
      (U*Q) i i*trace V+(U*Vᵀ*Q) i i := by
  simp_rw [mul_symmetricElementary_mul,add_mul]
  simp only [Finset.sum_add_distrib]
  have h1 : (∑ a,∑ b,(U i a*V b a)*Q b i)=(U*Vᵀ*Q) i i := by
    simp only [Matrix.mul_apply,transpose_apply,Finset.sum_mul]
    rw [Finset.sum_comm]
  have h2 : (∑ a,∑ b,(U i b*V a a)*Q b i)=(U*Q) i i*trace V := by
    simp only [Matrix.mul_apply,Matrix.trace,Finset.sum_mul,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _;apply Finset.sum_congr rfl
    intro b _;dsimp only [Matrix.diag];ring
  rw [h1,h2,add_comm]

def markedContraction (U V Q : Matrix ι ι ℝ) (i : ι) : ℝ :=
  (U*Q) i i*trace V+(U*Vᵀ*Q) i i

def WordCut.leftContraction (f : 𝓢(ℝ,ℂ)) {R : ℝ} (hR : 0≤R) (j : ℝ) (a : ι→ℝ) (z : ℝ)
    (M Q : Matrix ι ι ℝ) (i : ι) (c : WordCut ι) : ℝ :=
  (if c.inversePartner then z else 1)*markedContraction
    (actualWord f R hR j a z c.left M) (actualWord f R hR j a z c.right M) Q i

def WordCut.rightContraction (f : 𝓢(ℝ,ℂ)) {R : ℝ} (hR : 0≤R) (j : ℝ) (a : ι→ℝ) (z : ℝ)
    (M U : Matrix ι ι ℝ) (i : ι) (c : WordCut ι) : ℝ :=
  (if c.inversePartner then z else 1)*markedContraction U
    (actualWord f R hR j a z c.left M) (actualWord f R hR j a z c.right M) i

lemma WordCut.leftContraction_eq (f : 𝓢(ℝ,ℂ)) {R : ℝ} (hR : 0≤R) (j : ℝ) (a : ι→ℝ) (z : ℝ)
    (M Q : Matrix ι ι ℝ) (i : ι) (c : WordCut ι) :
    (∑ u,∑ v,(c.value f hR j a z M (symmetricElementary u v)) i u*Q v i)=
      c.leftContraction f hR j a z M Q i := by
  have hh : (∑ u,∑ v,(c.value f hR j a z M (symmetricElementary u v)) i u*Q v i)=
      (if c.inversePartner then z else 1)*(∑ u,∑ v,
        (actualWord f R hR j a z c.left M*symmetricElementary u v*
          actualWord f R hR j a z c.right M) i u*Q v i) := by
    simp only [WordCut.value,Matrix.smul_apply,smul_eq_mul,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro u _;apply Finset.sum_congr rfl
    intro v _;ring
  rw [hh,matrix_word_contraction_left]
  rfl

lemma WordCut.rightContraction_eq (f : 𝓢(ℝ,ℂ)) {R : ℝ} (hR : 0≤R) (j : ℝ) (a : ι→ℝ) (z : ℝ)
    (M U : Matrix ι ι ℝ) (i : ι) (c : WordCut ι) :
    (∑ u,∑ v,U i u*(c.value f hR j a z M (symmetricElementary u v)) v i)=
      c.rightContraction f hR j a z M U i := by
  have hh : (∑ u,∑ v,U i u*(c.value f hR j a z M (symmetricElementary u v)) v i)=
      (if c.inversePartner then z else 1)*(∑ u,∑ v,
        U i u*(actualWord f R hR j a z c.left M*symmetricElementary u v*
          actualWord f R hR j a z c.right M) v i) := by
    simp only [WordCut.value,Matrix.smul_apply,smul_eq_mul,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro u _;apply Finset.sum_congr rfl
    intro v _;ring
  rw [hh,matrix_word_contraction]
  rfl

lemma partnerList_leftContract (f : 𝓢(ℝ,ℂ)) {R : ℝ} (hR : 0≤R) (j : ℝ) (a : ι→ℝ) (z : ℝ)
    (M Q : Matrix ι ι ℝ) (i : ι) (C : List (WordCut ι)) :
    (∑ u,∑ v,((C.map (WordCut.value f hR j a z M (symmetricElementary u v))).sum) i u*Q v i)=
      (C.map (WordCut.leftContraction f hR j a z M Q i)).sum := by
  induction C with
  | nil => simp
  | cons c C ih =>
    simp only [List.map_cons,List.sum_cons,Matrix.add_apply,add_mul,Finset.sum_add_distrib]
    rw [WordCut.leftContraction_eq,ih]

lemma partnerList_rightContract (f : 𝓢(ℝ,ℂ)) {R : ℝ} (hR : 0≤R) (j : ℝ) (a : ι→ℝ) (z : ℝ)
    (M U : Matrix ι ι ℝ) (i : ι) (C : List (WordCut ι)) :
    (∑ u,∑ v,U i u*((C.map (WordCut.value f hR j a z M (symmetricElementary u v))).sum) v i)=
      (C.map (WordCut.rightContraction f hR j a z M U i)).sum := by
  induction C with
  | nil => simp
  | cons c C ih =>
    simp only [List.map_cons,List.sum_cons,Matrix.add_apply,mul_add,Finset.sum_add_distrib]
    rw [WordCut.rightContraction_eq,ih]

theorem actualWord_partner_contractions (f : 𝓢(ℝ,ℂ)) {R : ℝ} (hR : 0≤R) (j : ℝ)
    (a : ι→ℝ) (z : ℝ) (M : Matrix ι ι ℝ) (P Q : List (WordLetter ι)) (i : ι) :
    (∑ u,∑ v,((actualWordDirection f R hR j a z M (symmetricElementary u v) P) i u*
      actualWord f R hR j a z Q M v i+actualWord f R hR j a z P M i u*
        (actualWordDirection f R hR j a z M (symmetricElementary u v) Q) v i))=
    ((wordPartners a P).map (WordCut.leftContraction f hR j a z M (actualWord f R hR j a z Q M) i)).sum+
    ((wordPartners a Q).map (WordCut.rightContraction f hR j a z M (actualWord f R hR j a z P M) i)).sum := by
  simp only [Finset.sum_add_distrib,actualWordDirection_partners,partnerList_leftContract,partnerList_rightContract]
end SKGap
end
end

section
noncomputable section
namespace SKGap
open scoped BigOperators
variable {ι : Type*}

@[simp] lemma ordinaryCount_append (P Q : List (WordLetter ι)) :
    ordinaryCount (P++Q)=ordinaryCount P+ordinaryCount Q := by simp [ordinaryCount]
@[simp] lemma inverseCount_append (P Q : List (WordLetter ι)) :
    inverseCount (P++Q)=inverseCount P+inverseCount Q := by simp [inverseCount]
@[simp] lemma ordinaryCount_noise (Q : List (WordLetter ι)) :
    ordinaryCount (.noise::Q)=ordinaryCount Q+1 := by simp [ordinaryCount]
@[simp] lemma inverseCount_noise (Q : List (WordLetter ι)) :
    inverseCount (.noise::Q)=inverseCount Q := by simp [inverseCount]

lemma wordPartners_inverse_sides (a : ι→ℝ) (F : List (WordLetter ι)) (c : WordCut ι)
    (hc : c∈wordPartners a F) (hi : c.inversePartner=true) :
    1≤ inverseCount c.left ∧ 1≤ inverseCount c.right := by
  induction F generalizing c with
  | nil => simp [wordPartners] at hc
  | cons l F ih =>
    rw [wordPartners_cons,List.mem_append] at hc
    rcases hc with hc|hc
    · cases l with
      | diag d => simp at hc
      | noise => simp only [List.mem_singleton] at hc;subst c;contradiction
      | inverse =>
        simp only [List.mem_singleton] at hc
        subst c
        simp [inverseCount]
    · obtain ⟨d,hd,rfl⟩ := List.mem_map.mp hc
      have hh := ih d hd hi
      cases l <;> simp [WordCut.prepend,inverseCount] at * <;> tauto

structure WordRecursionTerm (ι : Type*) where
  outer : List (WordLetter ι)
  inner : List (WordLetter ι)
  inversePartner : Bool

def WordCut.asLeft (Q : List (WordLetter ι)) (c : WordCut ι) : WordRecursionTerm ι :=
  ⟨c.left++Q,c.right,c.inversePartner⟩
def WordCut.asRight (P : List (WordLetter ι)) (c : WordCut ι) : WordRecursionTerm ι :=
  ⟨P++c.right,c.left,c.inversePartner⟩
def wordRecursionAt (a : ι→ℝ) (P Q : List (WordLetter ι)) : List (WordRecursionTerm ι) :=
  ((wordPartners a P).map (WordCut.asLeft Q))++((wordPartners a Q).map (WordCut.asRight P))

lemma wordRecursionAt_decreases (a : ι→ℝ) (P Q : List (WordLetter ι))
    (t : WordRecursionTerm ι) (ht : t∈wordRecursionAt a P Q) :
    ordinaryCount t.outer<ordinaryCount (P++(.noise::Q)) ∧
    ordinaryCount t.inner<ordinaryCount (P++(.noise::Q)) := by
  dsimp only [wordRecursionAt] at ht
  rw [List.mem_append] at ht
  rcases ht with ht|ht
  · obtain ⟨c,hc,rfl⟩ := List.mem_map.mp ht
    have hh := (wordPartners_counts a P c hc).1
    cases hi : c.inversePartner <;> simp [WordCut.asLeft,hi] at * <;> omega
  · obtain ⟨c,hc,rfl⟩ := List.mem_map.mp ht
    have hh := (wordPartners_counts a Q c hc).1
    cases hi : c.inversePartner <;> simp [WordCut.asRight,hi] at * <;> omega

lemma wordRecursionAt_one_inverse (a : ι→ℝ) (P Q : List (WordLetter ι))
    (hI : inverseCount (P++(.noise::Q))≤1)
    (t : WordRecursionTerm ι) (ht : t∈wordRecursionAt a P Q) :
    inverseCount t.outer≤1 ∧ inverseCount t.inner≤1 := by
  dsimp only [wordRecursionAt] at ht
  rw [List.mem_append] at ht
  simp only [inverseCount_append,inverseCount_noise] at hI
  rcases ht with ht|ht
  · obtain ⟨c,hc,rfl⟩ := List.mem_map.mp ht
    have hh := (wordPartners_counts a P c hc).2
    cases hi : c.inversePartner
    · simp [WordCut.asLeft,hi] at *;omega
    · have hs := wordPartners_inverse_sides a P c hc hi
      simp [WordCut.asLeft,hi] at *;omega
  · obtain ⟨c,hc,rfl⟩ := List.mem_map.mp ht
    have hh := (wordPartners_counts a Q c hc).2
    cases hi : c.inversePartner
    · simp [WordCut.asRight,hi] at *;omega
    · have hs := wordPartners_inverse_sides a Q c hc hi
      simp [WordCut.asRight,hi] at *;omega

def firstNoiseSplit : List (WordLetter ι)→Option (List (WordLetter ι)×List (WordLetter ι))
  | [] => none
  | .noise::F => some ([],F)
  | l::F => (firstNoiseSplit F).map (fun pq=>(l::pq.1,pq.2))

lemma firstNoiseSplit_some (F P Q : List (WordLetter ι)) (h : firstNoiseSplit F=some (P,Q)) :
    F=P++(.noise::Q) := by
  induction F generalizing P Q with
  | nil => simp [firstNoiseSplit] at h
  | cons l F ih =>
    cases l with
    | noise => simp only [firstNoiseSplit,Option.some.injEq,Prod.mk.injEq] at h;rcases h with ⟨rfl,rfl⟩;rfl
    | diag d =>
      simp only [firstNoiseSplit,Option.map_eq_some_iff] at h
      obtain ⟨⟨P',Q'⟩,h1,h2⟩ := h
      simp only [Prod.mk.injEq] at h2
      rcases h2 with ⟨rfl,rfl⟩
      simpa only [List.cons_append] using congrArg (List.cons (.diag d)) (ih P' Q' h1)
    | inverse =>
      simp only [firstNoiseSplit,Option.map_eq_some_iff] at h
      obtain ⟨⟨P',Q'⟩,h1,h2⟩ := h
      simp only [Prod.mk.injEq] at h2
      rcases h2 with ⟨rfl,rfl⟩
      simpa only [List.cons_append] using congrArg (List.cons (.inverse)) (ih P' Q' h1)

lemma firstNoiseSplit_none (F : List (WordLetter ι)) : firstNoiseSplit F=none ↔ ordinaryCount F=0 := by
  induction F with
  | nil => simp [firstNoiseSplit,ordinaryCount]
  | cons l F ih => cases l <;> simp [firstNoiseSplit,ordinaryCount] at * <;> exact ih

def wordRecursionTerms (a : ι→ℝ) (F : List (WordLetter ι)) : List (WordRecursionTerm ι) :=
  match firstNoiseSplit F with
  | none => []
  | some (P,Q) => wordRecursionAt a P Q

lemma wordRecursionTerms_decreases (a : ι→ℝ) (F : List (WordLetter ι))
    (t : WordRecursionTerm ι) (ht : t∈wordRecursionTerms a F) :
    ordinaryCount t.outer<ordinaryCount F ∧ ordinaryCount t.inner<ordinaryCount F := by
  unfold wordRecursionTerms at ht
  cases hs : firstNoiseSplit F with
  | none => simp [hs] at ht
  | some pq =>
    rcases pq with ⟨P,Q⟩
    have he := firstNoiseSplit_some F P Q hs
    simp only [hs] at ht
    simpa only [he] using wordRecursionAt_decreases a P Q t ht

lemma wordRecursionTerms_one_inverse (a : ι→ℝ) (F : List (WordLetter ι))
    (hI : inverseCount F≤1) (t : WordRecursionTerm ι) (ht : t∈wordRecursionTerms a F) :
    inverseCount t.outer≤1 ∧ inverseCount t.inner≤1 := by
  unfold wordRecursionTerms at ht
  cases hs : firstNoiseSplit F with
  | none => simp [hs] at ht
  | some pq =>
    rcases pq with ⟨P,Q⟩
    have he := firstNoiseSplit_some F P Q hs
    simp only [hs] at ht
    exact wordRecursionAt_one_inverse a P Q (by simpa only [he] using hI) t ht

def wordDiagonal (F : List (WordLetter ι)) (i : ι) : ℝ :=
  ((F.map (fun l=>match l with | .diag d=>d i | _=>1))).prod

def wordPrediction [Fintype ι] (j : ℝ) (a : ι→ℝ) (z : ℝ)
    (F : List (WordLetter ι)) (i : ι) : ℝ :=
  if ordinaryCount F=0 then wordDiagonal F i else
    ((wordRecursionTerms a F).attach.map (fun th=>
      (if th.val.inversePartner then z else 1)*j*
        ((∑ k,wordPrediction j a z th.val.inner k)/(Fintype.card ι:ℝ))*
          wordPrediction j a z th.val.outer i)).sum
termination_by ordinaryCount F
decreasing_by
  · exact (wordRecursionTerms_decreases a F th.val th.property).2
  · exact (wordRecursionTerms_decreases a F th.val th.property).1

end SKGap
end
end

end OAI
