import Mathlib
import OAI.Probability.SKGap.Localization.Letter

namespace OAI

section
noncomputable section
namespace SKGap.Noncrossing
universe u v
namespace Diagram
variable {D : Type*}

def separateCut {F : List (Letter D)} {k : ℕ} (c : CutAt F k) : Separated F k :=
  ⟨shapeOfCut c,⟨c.val.inside,rfl⟩,
    ⟨c.val.outside,(List.take_append_drop _ _).symm⟩⟩

def joinCut {F : List (Letter D)} {k : ℕ} (z : Separated F k) : CutAt F k := by
  have hb : z.1.before.length≤z.2.2.val.size := by
    rw [← word_length,z.2.2.property,List.length_append]
    omega
  refine ⟨⟨z.1.before.length,z.2.1.val,z.2.2.val,z.1.closing⟩,hb,?_,?_⟩
  · have hs : z.2.1.val.size=z.1.between.length := by rw [← word_length,z.2.1.property]
    simpa only [hs] using z.1.mark_eq
  · rw [insert_word _ _ _ hb,z.2.2.property,z.2.1.property]
    simpa using z.1.word_eq.symm

@[simp] lemma join_separate {F : List (Letter D)} {k : ℕ} (c : CutAt F k) :
    joinCut (separateCut c) = c := by
  apply Subtype.ext
  rcases c with ⟨⟨p,a,b,cl⟩,hp,hk,hF⟩
  dsimp [joinCut,separateCut,shapeOfCut]
  simp only [List.length_take,word_length,Nat.min_eq_left hp]

lemma pair_heq {α γ : Type u} {β δ : Type v} {a : α} {b : β} {c : γ} {d : δ}
    (ha : a ≍ c) (hb : b ≍ d) : (a,b) ≍ (c,d) := by
  cases ha
  cases hb
  rfl

@[simp] lemma separate_join {F : List (Letter D)} {k : ℕ} (z : Separated F k) :
    separateCut (joinCut z) = z := by
  rcases z with ⟨s,a,b⟩
  have hs : shapeOfCut (joinCut (⟨s,a,b⟩ : Separated F k)) = s := by
    apply PairShape.ext <;>
      simp [shapeOfCut,joinCut,a.property,b.property]
  apply Sigma.ext hs
  apply pair_heq
  · refine (Subtype.heq_iff_coe_eq (fun d => ?_)).mpr ?_
    · rw [hs]
    · rfl
  · refine (Subtype.heq_iff_coe_eq (fun d => ?_)).mpr ?_
    · rw [hs]
    · rfl

def separateEquiv (F : List (Letter D)) (k : ℕ) : CutAt F k ≃ Separated F k where
  toFun := separateCut
  invFun := joinCut
  left_inv := join_separate
  right_inv := separate_join

section Value
variable {ι : Type*} [Fintype ι]

def mean (a : ι→ℝ) : ℝ := (∑ i,a i)/(Fintype.card ι:ℝ)

def value (j : ℝ) : Diagram (ι→ℝ) → ι→ℝ
  | nil => fun _ => 1
  | diag a d => fun i => a i * d.value j i
  | arch a b => fun i => j * mean (a.value j) * b.value j i

lemma mean_const_mul (c : ℝ) (a : ι→ℝ) :
    mean (fun i => c*a i) = c*mean a := by
  simp only [mean,← Finset.mul_sum,mul_div_assoc]

lemma value_insert (j : ℝ) (d e : Diagram (ι→ℝ)) (p : ℕ) (i : ι) :
    (d.insert p e).value j i = j*mean (e.value j)*d.value j i := by
  induction d generalizing p i with
  | nil => simp only [insert,value]; split_ifs <;> rfl
  | diag a d ih =>
    by_cases hp : p=0
    · simp [hp,value]
    · simp only [insert,hp,↓reduceIte,value,ih]; ring
  | arch a b ia ib =>
    by_cases hp : p=0
    · simp [hp,value]
    · simp only [insert,hp,↓reduceIte]
      split_ifs
      · have hh : value j (a.insert (p-1) e) = fun k => j*mean (e.value j)*a.value j k := funext (ia (p-1))
        simp only [value,hh,mean_const_mul]; ring
      · simp only [value,ib]; ring

lemma value_cut (j : ℝ) (d : Diagram (ι→ℝ)) (k : ℕ) (c : Cut (ι→ℝ))
    (hc : d.cut k=some c) (i : ι) :
    d.value j i = j*mean (c.inside.value j)*c.outside.value j i := by
  rw [← (cut_spec d k c hc).2.2]
  exact value_insert j c.outside c.inside c.start i

def prediction (j : ℝ) (F : List (Letter (ι→ℝ))) (i : ι) : ℝ :=
  ∑ d : Paired F, d.val.value j i

lemma mean_prediction (j : ℝ) (F : List (Letter (ι→ℝ))) :
    mean (prediction j F) = ∑ d : Paired F, mean (d.val.value j) := by
  simp only [mean,prediction]
  rw [Finset.sum_comm,Finset.sum_div]

theorem prediction_cut (j : ℝ) (F : List (Letter (ι→ℝ))) (k : ℕ)
    (hk : F[k]?=some .noise) (i : ι) :
    prediction j F i = ∑ s : PairShape F k,
      j * mean (prediction j s.between) * prediction j (s.before++s.after) i := by
  let e := (cutEquiv F k hk).trans (separateEquiv F k)
  have he : prediction j F i = ∑ z : Separated F k,
      j*mean (z.2.1.val.value j)*z.2.2.val.value j i := by
    apply Fintype.sum_equiv e
    intro d
    have hd : d.val.word[k]?=some .noise := by rw [d.property]; exact hk
    exact value_cut j d.val k (d.val.markedCut k hd) (cut_markedCut _ _ _) i
  rw [he]
  change (∑ z : Σ s : PairShape F k, Paired s.between × Paired (s.before++s.after),
    j*mean (z.2.1.val.value j)*z.2.2.val.value j i) = _
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro s _
  rw [Fintype.sum_prod_type]
  change (∑ a : Paired s.between, ∑ b : Paired (s.before++s.after),
    j*mean (a.val.value j)*b.val.value j i) = _
  simp_rw [← Finset.mul_sum]
  rw [← Finset.sum_mul, ← Finset.mul_sum, ← mean_prediction]
  rfl

end Value

end Diagram
end SKGap.Noncrossing

noncomputable section
open scoped BigOperators

end
end
end

end OAI
