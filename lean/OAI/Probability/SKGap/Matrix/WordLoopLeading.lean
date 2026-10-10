import Mathlib
import OAI.Probability.SKGap.Matrix.WordLeading
import OAI.Probability.SKGap.Matrix.WordLoop

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix Real MeasureTheory ProbabilityTheory Set
open scoped BigOperators Matrix.Norms.Frobenius SchwartzMap
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma actualWord_marked_integrable [Nonempty ι] (f : 𝓢(ℝ,ℂ)) {R j A D z r : ℝ}
    (hR : 0≤R) (hj : 0≤j) (hA : 0≤A) (hD : 0≤D) {a : ι→ℝ}
    (ha : ∀ i,0≤a i) (haA : ∀ i,a i≤A) (hz : z∈Icc (0:ℝ) 1)
    (U V Q : List (WordLetter ι)) (hU : ∀ l∈U,l.bounded D)
    (hV : ∀ l∈V,l.bounded D) (hQ : ∀ l∈Q,l.bounded D) (i : ι) :
    Integrable (fun g : MatrixCoordinates ι→ℝ=>markedContraction
      (actualWord f R hR j a z U (goeMatrix r g))
      (actualWord f R hR j a z V (goeMatrix r g))
      (actualWord f R hR j a z Q (goeMatrix r g)) i)
        (Measure.pi (fun _=>gaussianReal 0 1)) := by
  let B := actualWordBound f R j A D
  have hB : 0≤B := (actualWordBound_pos f hR hj hA hD).le
  have hb (F : List (WordLetter ι)) (hF : ∀ l∈F,l.bounded D) :=
    actualWord_bounds f hR hj hA hD ha haA hz F hF
  have hc (F : List (WordLetter ι)) (hF : ∀ l∈F,l.bounded D) :=
    (hb F hF).2.continuous.comp (goeMatrix_pi_lipschitz (ι:=ι) r).continuous
  have he : Continuous (fun g : MatrixCoordinates ι→ℝ=>markedContraction
      (actualWord f R hR j a z U (goeMatrix r g))
      (actualWord f R hR j a z V (goeMatrix r g))
      (actualWord f R hR j a z Q (goeMatrix r g)) i) := by
    have huc := hc U hU
    have hvc := hc V hV
    have hqc := hc Q hQ
    unfold markedContraction Matrix.trace
    fun_prop
  apply (integrable_const ((Fintype.card ι:ℝ)*B^U.length*B^V.length*B^Q.length+
    B^U.length*B^V.length*B^Q.length)).mono' he.aestronglyMeasurable
  filter_upwards [] with g
  let u := actualWord f R hR j a z U (goeMatrix r g)
  let v := actualWord f R hR j a z V (goeMatrix r g)
  let q := actualWord f R hR j a z Q (goeMatrix r g)
  have hu : opNorm u≤B^U.length := (hb U hU).1 _
  have hv : opNorm v≤B^V.length := (hb V hV).1 _
  have hq : opNorm q≤B^Q.length := (hb Q hQ).1 _
  have ht : |trace v|≤(Fintype.card ι:ℝ)*B^V.length := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply (Finset.sum_le_sum (fun k _=>(matrix_entry_le_opNorm v k k).trans hv)).trans_eq
    simp
  have huq : |(u*q) i i|≤B^U.length*B^Q.length :=
    (matrix_entry_le_opNorm _ i i).trans ((opNorm_mul _ _).trans
      (mul_le_mul hu hq (norm_nonneg _) (pow_nonneg hB _)))
  have hzq : |(u*vᵀ*q) i i|≤B^U.length*B^V.length*B^Q.length :=
    (matrix_word_reverse_bound u v q i).trans
      (mul_le_mul (mul_le_mul hu hv (norm_nonneg _) (pow_nonneg hB _)) hq
        (norm_nonneg _) (by positivity))
  change |(u*q) i i*trace v+(u*vᵀ*q) i i|≤_
  apply (abs_add_le _ _).trans
  rw [abs_mul]
  apply (add_le_add (mul_le_mul huq ht (abs_nonneg _) (by positivity)) hzq).trans_eq
  ring

omit [Fintype ι] [DecidableEq ι] in
lemma integrable_list_map_sum {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (C : List ι) (F : ι→Ω→ℝ) (hF : ∀ c∈C,Integrable (F c) μ) :
    Integrable (fun x=>(C.map (fun c=>F c x)).sum) μ := by
  induction C with
  | nil => simp
  | cons c C ih =>
    simpa only [List.map_cons,List.sum_cons,Pi.add_apply] using!
      (hF c List.mem_cons_self).add (ih (fun c hc=>hF c (List.mem_cons_of_mem _ hc)))

omit [Fintype ι] [DecidableEq ι] in
lemma integral_list_sum_bound {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (r : ℝ) (C : List ι) (F : ι→Ω→ℝ) (p e : ι→ℝ)
    (hF : ∀ c∈C,Integrable (F c) μ)
    (hb : ∀ c∈C,|r*(∫ x,F c x ∂μ)-p c|≤e c) :
    |r*(∫ x,(C.map (fun c=>F c x)).sum ∂μ)-(C.map p).sum|≤(C.map e).sum := by
  induction C with
  | nil => simp
  | cons c C ih =>
    have hFi := integrable_list_map_sum μ C F (fun c hc=>hF c (List.mem_cons_of_mem _ hc))
    simp only [List.map_cons,List.sum_cons]
    rw [integral_add (hF c List.mem_cons_self) hFi,mul_add]
    have ht := ih (fun c hc=>hF c (List.mem_cons_of_mem _ hc))
      (fun c hc=>hb c (List.mem_cons_of_mem _ hc))
    calc
      |r*(∫ x,F c x ∂μ)+r*(∫ x,(C.map (fun c=>F c x)).sum ∂μ)-(p c+(C.map p).sum)| =
        |(r*(∫ x,F c x ∂μ)-p c)+(r*(∫ x,(C.map (fun c=>F c x)).sum ∂μ)-(C.map p).sum)| := by
          congr 1
          ring
      _ ≤ _ := (abs_add_le _ _).trans (add_le_add (hb c List.mem_cons_self) ht)

def wordExpectedRecursion (f : 𝓢(ℝ,ℂ)) {R : ℝ} (hR : 0≤R) (j : ℝ)
    (a : ι→ℝ) (z : ℝ) (F : List (WordLetter ι)) (i : ι) : ℝ :=
  ((wordRecursionTerms a F).map (fun t=>(if t.inversePartner then z else 1)*j*
    wordAverageExpected f hR j a z t.inner*wordExpected f hR j a z t.outer i)).sum

omit [Fintype ι] [DecidableEq ι] in
lemma weighted_integral_error {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (F : Ω→ℝ) (c r p e : ℝ) (h : |r*(∫ x,F x ∂μ)-p|≤e) :
    |r*(∫ x,c*F x ∂μ)-c*p|≤|c| *e := by
  rw [integral_const_mul]
  have he : r*(c*(∫ x,F x ∂μ))-c*p=c*(r*(∫ x,F x ∂μ)-p) := by ring
  rw [he,abs_mul]
  exact mul_le_mul_of_nonneg_left h (abs_nonneg c)

def wordRecursionAtExpected (f : 𝓢(ℝ,ℂ)) {R : ℝ} (hR : 0≤R) (j : ℝ)
    (a : ι→ℝ) (z : ℝ) (P Q : List (WordLetter ι)) (i : ι) : ℝ :=
  ((wordRecursionAt a P Q).map (fun t=>(if t.inversePartner then z else 1)*j*
    wordAverageExpected f hR j a z t.inner*wordExpected f hR j a z t.outer i)).sum

def wordRecursionAtCost (j B z : ℝ) (a : ι→ℝ) (P Q : List (WordLetter ι)) : ℝ :=
  ((wordPartners a P).map (fun c=>|if c.inversePartner then z else 1| *
    wordLeadingCost j B c.left.length c.right.length Q.length)).sum+
  ((wordPartners a Q).map (fun c=>|if c.inversePartner then z else 1| *
    wordLeadingCost j B P.length c.left.length c.right.length)).sum

theorem actualWord_loop_leading {n : ℕ} (hn : 0<n) (f : 𝓢(ℝ,ℂ)) {R j A D z : ℝ}
    (hR : 0≤R) (hj : 0<j) (hA : 0≤A) (hD : 0≤D) {a : Fin n→ℝ}
    (ha : ∀ i,0≤a i) (haA : ∀ i,a i≤A) (haD : ∀ i,|a i|≤D) (hz : z∈Icc (0:ℝ) 1)
    (P Q : List (WordLetter (Fin n))) (hP : ∀ l∈P,l.bounded D)
    (hQ : ∀ l∈Q,l.bounded D) (i : Fin n) :
    let μ := Measure.pi (fun _ : MatrixCoordinates (Fin n)=>gaussianReal 0 1)
    |(j/(n:ℝ))*(∫ g,actualWordLoop f hR j a z P Q (goeMatrix (j/n) g) i ∂μ)-
      wordRecursionAtExpected f hR j a z P Q i|≤
        wordRecursionAtCost j (actualWordBound f R j A D) z a P Q/(n:ℝ) := by
  let : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  intro μ
  let B := actualWordBound f R j A D
  let L := fun (c : WordCut (Fin n)) (g : MatrixCoordinates (Fin n)→ℝ)=>
    c.leftContraction f hR j a z (goeMatrix (j/n) g)
      (actualWord f R hR j a z Q (goeMatrix (j/n) g)) i
  let Rf := fun (c : WordCut (Fin n)) (g : MatrixCoordinates (Fin n)→ℝ)=>
    c.rightContraction f hR j a z (goeMatrix (j/n) g)
      (actualWord f R hR j a z P (goeMatrix (j/n) g)) i
  let pL := fun c : WordCut (Fin n)=>(if c.inversePartner then z else 1)*j*
    wordAverageExpected f hR j a z c.right*wordExpected f hR j a z (c.left++Q) i
  let pR := fun c : WordCut (Fin n)=>(if c.inversePartner then z else 1)*j*
    wordAverageExpected f hR j a z c.left*wordExpected f hR j a z (P++c.right) i
  let eL := fun c : WordCut (Fin n)=>|if c.inversePartner then z else 1| *
    wordLeadingCost j B c.left.length c.right.length Q.length/(n:ℝ)
  let eR := fun c : WordCut (Fin n)=>|if c.inversePartner then z else 1| *
    wordLeadingCost j B P.length c.left.length c.right.length/(n:ℝ)
  have hLb (c : WordCut (Fin n)) (hc : c∈wordPartners a P) := wordPartners_preserves_bound haD P hP c hc
  have hRb (c : WordCut (Fin n)) (hc : c∈wordPartners a Q) := wordPartners_preserves_bound haD Q hQ c hc
  have hLi : ∀ c∈wordPartners a P,Integrable (L c) μ := by
    intro c hc
    exact (actualWord_marked_integrable f hR hj.le hA hD ha haA hz c.left c.right Q
      (hLb c hc).1 (hLb c hc).2 hQ i).const_mul _
  have hRi : ∀ c∈wordPartners a Q,Integrable (Rf c) μ := by
    intro c hc
    exact (actualWord_marked_integrable f hR hj.le hA hD ha haA hz P c.left c.right
      hP (hRb c hc).1 (hRb c hc).2 i).const_mul _
  have hLe : ∀ c∈wordPartners a P,|(j/(n:ℝ))*(∫ g,L c g ∂μ)-pL c|≤eL c := by
    intro c hc
    have hh := weighted_integral_error μ _ (if c.inversePartner then z else 1) _ _ _
      (actualWord_leading hn f hR hj hA hD ha haA hz c.left c.right Q
        (hLb c hc).1 (hLb c hc).2 hQ i)
    simpa only [L,pL,eL,WordCut.leftContraction,mul_assoc,mul_div_assoc,B] using hh
  have hRe : ∀ c∈wordPartners a Q,|(j/(n:ℝ))*(∫ g,Rf c g ∂μ)-pR c|≤eR c := by
    intro c hc
    have hh := weighted_integral_error μ _ (if c.inversePartner then z else 1) _ _ _
      (actualWord_leading hn f hR hj hA hD ha haA hz P c.left c.right
        hP (hRb c hc).1 (hRb c hc).2 i)
    simpa only [Rf,pR,eR,WordCut.rightContraction,mul_assoc,mul_div_assoc,B] using hh
  have hL := integral_list_sum_bound μ (j/(n:ℝ)) (wordPartners a P) L pL eL hLi hLe
  have hR' := integral_list_sum_bound μ (j/(n:ℝ)) (wordPartners a Q) Rf pR eR hRi hRe
  have hI1 := integrable_list_map_sum μ (wordPartners a P) L hLi
  have hI2 := integrable_list_map_sum μ (wordPartners a Q) Rf hRi
  have heI : (∫ g,actualWordLoop f hR j a z P Q (goeMatrix (j/n) g) i ∂μ)=
      (∫ g,((wordPartners a P).map (fun c=>L c g)).sum ∂μ)+
        (∫ g,((wordPartners a Q).map (fun c=>Rf c g)).sum ∂μ) :=
    integral_add hI1 hI2
  have heP : wordRecursionAtExpected f hR j a z P Q i=
      ((wordPartners a P).map pL).sum+((wordPartners a Q).map pR).sum := by
    simp [wordRecursionAtExpected,wordRecursionAt,List.map_map,Function.comp_def,WordCut.asLeft,WordCut.asRight,pL,pR]
    rfl
  have heE : ((wordPartners a P).map eL).sum+((wordPartners a Q).map eR).sum=
      wordRecursionAtCost j B z a P Q/(n:ℝ) := by
    simp only [eL,eR,wordRecursionAtCost,add_div]
    congr 1 <;> induction wordPartners a _ with
    | nil => simp
    | cons c C ih => simp only [List.map_cons,List.sum_cons,add_div,ih]
  rw [heI,heP]
  have hsum := (abs_add_le ((j/(n:ℝ))*(∫ g,((wordPartners a P).map (fun c=>L c g)).sum ∂μ)-((wordPartners a P).map pL).sum)
    ((j/(n:ℝ))*(∫ g,((wordPartners a Q).map (fun c=>Rf c g)).sum ∂μ)-((wordPartners a Q).map pR).sum)).trans
      (add_le_add hL hR')
  rw [heE] at hsum
  have he : (j/(n:ℝ))*((∫ g,((wordPartners a P).map (fun c=>L c g)).sum ∂μ)+
      (∫ g,((wordPartners a Q).map (fun c=>Rf c g)).sum ∂μ))-
      (((wordPartners a P).map pL).sum+((wordPartners a Q).map pR).sum)=
      ((j/(n:ℝ))*(∫ g,((wordPartners a P).map (fun c=>L c g)).sum ∂μ)-((wordPartners a P).map pL).sum)+
      ((j/(n:ℝ))*(∫ g,((wordPartners a Q).map (fun c=>Rf c g)).sum ∂μ)-((wordPartners a Q).map pR).sum) := by ring
  rw [he]
  exact hsum

end SKGap
end
end

end OAI
