import Mathlib
import OAI.Probability.SKGap.Localization.Bilinear
import OAI.Probability.SKGap.Matrix.WordPartnerContraction
import OAI.Probability.SKGap.Localization.ProjectedMarkedIBP

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix Real MeasureTheory ProbabilityTheory Set
open RealComplex
open scoped BigOperators Matrix.Norms.Frobenius NNReal ENNReal SchwartzMap
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def wordDifferentialBound (B : NNReal) (A z : ℝ) (k : ℕ) : ℝ :=
  (1+|z| *A*(B:ℝ)^2)*(wordParameterCoeff B k:ℝ)*2

lemma actualWord_elementary_bound [Nonempty ι] (f : 𝓢(ℝ,ℂ)) {R j A D z : ℝ}
    (hR : 0≤R) (hj : 0≤j) (hA : 0≤A) (hD : 0≤D) {a : ι→ℝ}
    (ha : ∀ i,0≤a i) (haA : ∀ i,a i≤A) (hz : z∈Icc (0:ℝ) 1)
    (F : List (WordLetter ι)) (hF : ∀ l∈F,l.bounded D) (M : Matrix ι ι ℝ) (u v : ι) :
    opNorm (actualWordDirection f R hR j a z M (symmetricElementary u v) F)≤
      wordDifferentialBound ⟨actualWordBound f R j A D,(actualWordBound_pos f hR hj hA hD).le⟩ A z F.length := by
  apply (actualWordDirection_bound f hR hj hA hD ha haA hz F hF M (symmetricElementary u v)).trans
  apply mul_le_mul_of_nonneg_left ((operator_le_frobenius _).trans (symmetricElementary_norm_le u v))
  positivity

def actualWordLoop (f : 𝓢(ℝ,ℂ)) {R : ℝ} (hR : 0≤R) (j : ℝ) (a : ι→ℝ) (z : ℝ)
    (P Q : List (WordLetter ι)) (M : Matrix ι ι ℝ) (i : ι) : ℝ :=
    ((wordPartners a P).map (WordCut.leftContraction f hR j a z M (actualWord f R hR j a z Q M) i)).sum+
    ((wordPartners a Q).map (WordCut.rightContraction f hR j a z M (actualWord f R hR j a z P M) i)).sum

theorem actualWord_loop [Nonempty ι] (f : 𝓢(ℝ,ℂ)) {lo hi : ℝ} (hlo : 0<lo)
    (hf : ∀ x∈Icc lo hi,f x=(x:ℂ)⁻¹) {R j A D z r : ℝ}
    (hR : 0≤R) (hj : 0≤j) (hA : 0≤A) (hD : 0≤D) (hr : 0≤r) {a : ι→ℝ}
    (ha : ∀ i,0≤a i) (haA : ∀ i,a i≤A) (hz : z∈Icc (0:ℝ) 1)
    (P Q : List (WordLetter ι)) (hP : ∀ l∈P,l.bounded D) (hQ : ∀ l∈Q,l.bounded D) (i : ι) :
    let B : NNReal := ⟨actualWordBound f R j A D,(actualWordBound_pos f hR hj hA hD).le⟩
    let μ := Measure.pi (fun _ : MatrixCoordinates ι=>gaussianReal 0 1)
    let s := truncationGoodSet r R lo hi (pathDiagonal a z) (pathShift z ((j/(Fintype.card ι:ℝ))*∑ k,a k))
    |(∫ g,actualWord f R hR j a z (P++(.noise::Q)) (goeMatrix r g) i i ∂μ)-
      r*(∫ g,actualWordLoop f hR j a z P Q (goeMatrix r g) i ∂μ)|≤
      markedError (ι:=ι) r R ((P.length:NNReal)*B^P.length) ((Q.length:NNReal)*B^Q.length)
        (B^P.length) (B^Q.length) (wordDifferentialBound B A z P.length)
          (wordDifferentialBound B A z Q.length) (μ.real sᶜ) := by
  intro B μ s
  let U := actualWord f R hR j a z P
  let V := actualWord f R hR j a z Q
  let DU := fun u v M=>actualWordDirection f R hR j a z M (symmetricElementary u v) P
  let DV := fun u v M=>actualWordDirection f R hR j a z M (symmetricElementary u v) Q
  have hu := actualWord_bounds f hR hj hA hD ha haA hz P hP
  have hv := actualWord_bounds f hR hj hA hD ha haA hz Q hQ
  have hu' : ∀ M,opNorm (U M)≤(B^P.length:NNReal) := by simpa only [B,NNReal.coe_pow,NNReal.coe_mk] using! hu.1
  have hv' : ∀ M,opNorm (V M)≤(B^Q.length:NNReal) := by simpa only [B,NNReal.coe_pow,NNReal.coe_mk] using! hv.1
  have hdu (u v : ι) : Continuous (DU u v) := actualWordDirection_continuous f hR hj hA hD ha haA hz P hP _
  have hdv (u v : ι) : Continuous (DV u v) := actualWordDirection_continuous f hR hj hA hD ha haA hz Q hQ _
  have hdub (u v : ι) (M : Matrix ι ι ℝ) : opNorm (DU u v M)≤wordDifferentialBound B A z P.length :=
    actualWord_elementary_bound f hR hj hA hD ha haA hz P hP M u v
  have hdvb (u v : ι) (M : Matrix ι ι ℝ) : opNorm (DV u v M)≤wordDifferentialBound B A z Q.length :=
    actualWord_elementary_bound f hR hj hA hD ha haA hz Q hQ M u v
  have hpd (F : List (WordLetter ι)) (u v : ι) (g : MatrixCoordinates ι→ℝ) (hg : g∈s) :
      HasDerivAt (fun t : ℝ=>actualWord f R hR j a z F (goeMatrix r g+t • symmetricElementary u v))
        (actualWordDirection f R hR j a z (goeMatrix r g) (symmetricElementary u v) F) 0 :=
    actualWord_hasDerivAt f hlo hf hR j ha hz.1 _ _ (goeMatrix_transpose _ _) (symmetricElementary_transpose _ _)
      hg.1 hg.2.1 hg.2.2 F
  have hh := projected_marked_product_IBP hr hR U V DU DV hu.2 hv.2 hu' hv' hdu hdv hdub hdvb
    (truncationGoodSet_measurable r R lo hi _ _) (fun g (hg : g∈s)=>hg.1.le) (hpd P) (hpd Q) i
  simpa only [U,V,DU,DV,actualWord_append,actualWord_cons,WordLetter.eval,mul_assoc,
    actualWord_partner_contractions,actualWordLoop] using! hh
end SKGap
end
end

section
noncomputable section
namespace SKGap
variable {ι : Type*}

lemma wordPartners_lengths (a : ι→ℝ) (F : List (WordLetter ι)) (c : WordCut ι)
    (hc : c∈wordPartners a F) :
    c.left.length+c.right.length+(if c.inversePartner then 0 else 1)=
      F.length+(if c.inversePartner then 2 else 0) := by
  induction F generalizing c with
  | nil => simp [wordPartners] at hc
  | cons l F ih =>
    rw [wordPartners_cons,List.mem_append] at hc
    rcases hc with hc|hc
    · cases l with
      | diag d => simp at hc
      | noise => simp only [List.mem_singleton] at hc;subst c;simp
      | inverse => simp only [List.mem_singleton] at hc;subst c;simp;omega
    · obtain ⟨d,hd,rfl⟩ := List.mem_map.mp hc
      have hh := ih d hd
      simp only [WordCut.prepend,List.length_cons] at *
      by_cases hi : d.inversePartner=true <;> simp [hi] at hh ⊢ <;> omega

lemma wordPartners_preserves_bound {a : ι→ℝ} {D : ℝ} (ha : ∀ i,|a i|≤D)
    (F : List (WordLetter ι)) (hF : ∀ l∈F,l.bounded D) (c : WordCut ι)
    (hc : c∈wordPartners a F) :
    (∀ l∈c.left,l.bounded D) ∧ (∀ l∈c.right,l.bounded D) := by
  induction F generalizing c with
  | nil => simp [wordPartners] at hc
  | cons l F ih =>
    have hFt : ∀ l∈F,l.bounded D := fun m hm=>hF m (List.mem_cons_of_mem _ hm)
    rw [wordPartners_cons,List.mem_append] at hc
    rcases hc with hc|hc
    · cases l with
      | diag d => simp at hc
      | noise =>
        simp only [List.mem_singleton] at hc;subst c
        simpa using hFt
      | inverse =>
        simp only [List.mem_singleton] at hc;subst c
        constructor
        · intro m hm
          simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
          rcases hm with rfl|rfl
          · trivial
          · exact ha
        · intro m hm
          rcases List.mem_cons.mp hm with rfl|hm
          · trivial
          · exact hFt m hm
    · obtain ⟨d,hd,rfl⟩ := List.mem_map.mp hc
      have hh := ih hFt d hd
      constructor
      · intro m hm
        rcases List.mem_cons.mp hm with rfl|hm
        · exact hF m List.mem_cons_self
        · exact hh.1 m hm
      · exact hh.2

lemma wordPartners_card_bound (a : ι→ℝ) (F : List (WordLetter ι)) :
    (wordPartners a F).length≤F.length := by
  induction F with
  | nil => simp [wordPartners]
  | cons l F ih => cases l <;> simp [wordPartners] <;> omega

lemma wordRecursionAt_lengths (a : ι→ℝ) (P Q : List (WordLetter ι))
    (t : WordRecursionTerm ι) (ht : t∈wordRecursionAt a P Q) :
    t.outer.length≤(P++(.noise::Q)).length ∧ t.inner.length≤(P++(.noise::Q)).length := by
  dsimp only [wordRecursionAt] at ht
  rw [List.mem_append] at ht
  rcases ht with ht|ht
  · obtain ⟨c,hc,rfl⟩ := List.mem_map.mp ht
    have hh := wordPartners_lengths a P c hc
    cases hi : c.inversePartner
    · simp [WordCut.asLeft,hi] at *;omega
    · have hs := wordPartners_inverse_sides a P c hc hi
      have hL : inverseCount c.left≤c.left.length := List.countP_le_length
      have hR : inverseCount c.right≤c.right.length := List.countP_le_length
      simp [WordCut.asLeft,hi] at *;omega
  · obtain ⟨c,hc,rfl⟩ := List.mem_map.mp ht
    have hh := wordPartners_lengths a Q c hc
    cases hi : c.inversePartner
    · simp [WordCut.asRight,hi] at *;omega
    · have hs := wordPartners_inverse_sides a Q c hc hi
      have hL : inverseCount c.left≤c.left.length := List.countP_le_length
      have hR : inverseCount c.right≤c.right.length := List.countP_le_length
      simp [WordCut.asRight,hi] at *;omega

lemma wordRecursionAt_bounds {a : ι→ℝ} {D : ℝ} (ha : ∀ i,|a i|≤D)
    (P Q : List (WordLetter ι)) (hP : ∀ l∈P,l.bounded D) (hQ : ∀ l∈Q,l.bounded D)
    (t : WordRecursionTerm ι) (ht : t∈wordRecursionAt a P Q) :
    (∀ l∈t.outer,l.bounded D) ∧ (∀ l∈t.inner,l.bounded D) := by
  dsimp only [wordRecursionAt] at ht
  rw [List.mem_append] at ht
  rcases ht with ht|ht
  · obtain ⟨c,hc,rfl⟩ := List.mem_map.mp ht
    have hh := wordPartners_preserves_bound ha P hP c hc
    exact ⟨fun l hl=>(List.mem_append.mp hl).elim (hh.1 l) (hQ l),hh.2⟩
  · obtain ⟨c,hc,rfl⟩ := List.mem_map.mp ht
    have hh := wordPartners_preserves_bound ha Q hQ c hc
    exact ⟨fun l hl=>(List.mem_append.mp hl).elim (hP l) (hh.2 l),hh.1⟩

lemma wordRecursionTerms_lengths (a : ι→ℝ) (F : List (WordLetter ι))
    (t : WordRecursionTerm ι) (ht : t∈wordRecursionTerms a F) :
    t.outer.length≤F.length ∧ t.inner.length≤F.length := by
  unfold wordRecursionTerms at ht
  cases hs : firstNoiseSplit F with
  | none => simp [hs] at ht
  | some pq =>
    rcases pq with ⟨P,Q⟩
    have he := firstNoiseSplit_some F P Q hs
    simp only [hs] at ht
    simpa only [he] using wordRecursionAt_lengths a P Q t ht

lemma wordRecursionTerms_bounds {a : ι→ℝ} {D : ℝ} (ha : ∀ i,|a i|≤D)
    (F : List (WordLetter ι)) (hF : ∀ l∈F,l.bounded D)
    (t : WordRecursionTerm ι) (ht : t∈wordRecursionTerms a F) :
    (∀ l∈t.outer,l.bounded D) ∧ (∀ l∈t.inner,l.bounded D) := by
  unfold wordRecursionTerms at ht
  cases hs : firstNoiseSplit F with
  | none => simp [hs] at ht
  | some pq =>
    rcases pq with ⟨P,Q⟩
    have he := firstNoiseSplit_some F P Q hs
    simp only [hs] at ht
    have hP : ∀ l∈P,l.bounded D := fun l hl=>hF l (by rw [he];exact List.mem_append_left _ hl)
    have hQ : ∀ l∈Q,l.bounded D := fun l hl=>hF l (by rw [he];exact List.mem_append_right _ (List.mem_cons_of_mem _ hl))
    exact wordRecursionAt_bounds ha P Q hP hQ t ht

lemma wordRecursionTerms_card_bound (a : ι→ℝ) (F : List (WordLetter ι)) :
    (wordRecursionTerms a F).length≤F.length := by
  unfold wordRecursionTerms
  cases hs : firstNoiseSplit F with
  | none => simp
  | some pq =>
    rcases pq with ⟨P,Q⟩
    have he := firstNoiseSplit_some F P Q hs
    simp only [wordRecursionAt,List.length_append,List.length_map,he,List.length_cons]
    have h1 := wordPartners_card_bound a P
    have h2 := wordPartners_card_bound a Q
    omega
end SKGap
end
end

end OAI
