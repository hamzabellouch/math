import Mathlib
import OAI.Probability.SKGap.Matrix.WordLoop

namespace OAI

section
noncomputable section
namespace SKGap
open Real Matrix Set
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [Nonempty ι]

def wordAverage (e : List (WordLetter ι)→ι→ℝ) (F : List (WordLetter ι)) : ℝ :=
  (∑ k,e F k)/(Fintype.card ι:ℝ)
def wordRecursionValue (j : ℝ) (a : ι→ℝ) (z : ℝ)
    (e : List (WordLetter ι)→ι→ℝ) (F : List (WordLetter ι)) (i : ι) : ℝ :=
  ((wordRecursionTerms a F).map (fun t=>(if t.inversePartner then z else 1)*j*
    wordAverage e t.inner*e t.outer i)).sum

lemma wordAverage_abs_le (e : List (WordLetter ι)→ι→ℝ) (F : List (WordLetter ι))
    {B : ℝ} (hB : ∀ i,|e F i|≤B) : |wordAverage e F|≤B := by
  have hn : (0:ℝ)<Fintype.card ι := Nat.cast_pos.mpr Fintype.card_pos
  rw [wordAverage,abs_div,abs_of_pos hn]
  apply (div_le_iff₀ hn).mpr
  calc
    |∑ k,e F k| ≤ ∑ k,|e F k| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _ : ι,B := Finset.sum_le_sum (fun i _=>hB i)
    _ = _ := by simp [mul_comm]

lemma wordAverage_sub_abs_le (e p : List (WordLetter ι)→ι→ℝ) (F : List (WordLetter ι))
    {E : ℝ} (hE : ∀ i,|e F i-p F i|≤E) : |wordAverage e F-wordAverage p F|≤E := by
  have hh := wordAverage_abs_le (fun G i=>e G i-p G i) F hE
  simpa only [wordAverage,Finset.sum_sub_distrib,sub_div] using hh

omit [Fintype ι] [Nonempty ι] in
lemma abs_list_difference_le (C : List ι) (p q : ι→ℝ) {E : ℝ}
    (h : ∀ c∈C,|p c-q c|≤E) : |(C.map p).sum-(C.map q).sum|≤(C.length:ℝ)*E := by
  induction C with
  | nil => simp
  | cons c C ih =>
    have hh := ih (fun c hc=>h c (List.mem_cons_of_mem _ hc))
    simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.cast_add,Nat.cast_one]
    calc
      |(p c+(C.map p).sum)-(q c+(C.map q).sum)|=
        |(p c-q c)+((C.map p).sum-(C.map q).sum)| := by congr 1;ring
      _ ≤ |p c-q c|+|(C.map p).sum-(C.map q).sum| := abs_add_le _ _
      _ ≤ E+(C.length:ℝ)*E := add_le_add (h c List.mem_cons_self) hh
      _ = _ := by ring

omit [Nonempty ι] in
lemma wordPrediction_recursion (j : ℝ) (a : ι→ℝ) (z : ℝ) (F : List (WordLetter ι)) (i : ι)
    (hO : ordinaryCount F≠0) :
    wordPrediction j a z F i=wordRecursionValue j a z (wordPrediction j a z) F i := by
  rw [wordPrediction,ite_eq_right hO]
  simp only [wordRecursionValue,wordAverage]
  apply congrArg List.sum
  exact List.attach_map_val (l:=wordRecursionTerms a F) (f:=fun (t : WordRecursionTerm ι)=>
    (if t.inversePartner then z else 1)*j*((∑ k,wordPrediction j a z t.inner k)/(Fintype.card ι:ℝ))*wordPrediction j a z t.outer i)

omit [Nonempty ι] in
lemma wordPrediction_base (j : ℝ) (a : ι→ℝ) (z : ℝ) (F : List (WordLetter ι)) (i : ι)
    (hO : ordinaryCount F=0) : wordPrediction j a z F i=wordDiagonal F i := by
  rw [wordPrediction,ite_eq_left hO]

omit [Fintype ι] [Nonempty ι] in
lemma scalar_product_prediction_error {u v p q B δ E : ℝ}
    (hB : 0≤B) (hδ : 0≤δ) (hE : δ≤E)
    (hu : |u|≤B) (hv : |v|≤B) (hup : |u-p|≤δ) (hvq : |v-q|≤δ) :
    |u*v-p*q|≤(2*B+E)*δ := by
  have he : u*v-p*q=u*(v-q)+(u-p)*q := by ring
  have hq : |q|≤B+δ := by
    calc
      |q|=|v-(v-q)| := by congr 1;ring
      _ ≤ |v|+|v-q| := abs_sub _ _
      _ ≤ B+δ := add_le_add hv hvq
  rw [he]
  calc
    |u*(v-q)+(u-p)*q| ≤ |u*(v-q)|+|(u-p)*q| := abs_add_le _ _
    _ = |u| *|v-q|+|u-p| *|q| := by rw [abs_mul,abs_mul]
    _ ≤ B*δ+δ*(B+δ) := add_le_add (mul_le_mul hu hvq (abs_nonneg _) hB)
      (mul_le_mul hup hq (abs_nonneg _) hδ)
    _ ≤ (2*B+E)*δ := by nlinarith [mul_nonneg hδ (sub_nonneg.mpr hE)]

theorem wordRecursionValue_stability {j z n B E : ℝ} (hj : 0≤j)
    (hz : z∈Icc (0:ℝ) 1) (hn : 1≤n) (hB : 0≤B) (hE : 0≤E)
    (a : ι→ℝ) (F : List (WordLetter ι)) (p q : List (WordLetter ι)→ι→ℝ)
    (hb : ∀ t∈wordRecursionTerms a F,∀ i,|p t.inner i|≤B ∧ |p t.outer i|≤B)
    (he : ∀ t∈wordRecursionTerms a F,∀ i,|p t.inner i-q t.inner i|≤E/n ∧
      |p t.outer i-q t.outer i|≤E/n) (i : ι) :
    |wordRecursionValue j a z p F i-wordRecursionValue j a z q F i|≤
      (F.length:ℝ)*j*(2*B+E)*E/n := by
  have hn0 : 0<n := zero_lt_one.trans_le hn
  have hd : 0≤E/n := div_nonneg hE hn0.le
  have hdn : E/n≤E := div_le_self hE hn
  have hterm (t : WordRecursionTerm ι) (ht : t∈wordRecursionTerms a F) :
      |(if t.inversePartner then z else 1)*j*wordAverage p t.inner*p t.outer i-
        (if t.inversePartner then z else 1)*j*wordAverage q t.inner*q t.outer i|≤
          j*(2*B+E)*E/n := by
    have hp := wordAverage_abs_le p t.inner (fun k=>(hb t ht k).1)
    have hep := wordAverage_sub_abs_le p q t.inner (fun k=>(he t ht k).1)
    have hh := scalar_product_prediction_error hB hd hdn hp (hb t ht i).2 hep (he t ht i).2
    have hcoef : |if t.inversePartner then z else 1|≤1 := by
      split
      · rw [abs_of_nonneg hz.1]; exact hz.2
      · simp
    have hcj : |(if t.inversePartner then z else 1)*j|≤j := by
      rw [abs_mul,abs_of_nonneg hj]
      exact (mul_le_mul_of_nonneg_right hcoef hj).trans_eq (one_mul _)
    calc
      _=|(if t.inversePartner then z else 1)*j| *
        |wordAverage p t.inner*p t.outer i-wordAverage q t.inner*q t.outer i| := by
          rw [← abs_mul]
          congr 1
          ring
      _ ≤ j*((2*B+E)*(E/n)) := mul_le_mul hcj hh (abs_nonneg _) hj
      _ = _ := by ring
  have hh := abs_list_difference_le (wordRecursionTerms a F) _ _ hterm
  have hcard : ((wordRecursionTerms a F).length:ℝ)≤F.length := by
    exact_mod_cast wordRecursionTerms_card_bound a F
  apply hh.trans
  have hm := mul_le_mul_of_nonneg_right hcard (show 0≤j*(2*B+E)*E/n by positivity)
  simpa only [mul_div_assoc,mul_assoc] using hm
end SKGap
end
end

end OAI
