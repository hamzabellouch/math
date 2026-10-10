import Mathlib
import OAI.Probability.SKGap.Localization.Append
import OAI.Probability.SKGap.Localization.SeparateCut

namespace OAI

section
noncomputable section
noncomputable section
open scoped BigOperators
noncomputable section
noncomputable section
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
namespace SKGap.Noncrossing
namespace Diagram
variable {D : Type*}

@[ext] structure NoiseSplit (F : List (Letter D)) where
  before : List (Letter D)
  after : List (Letter D)
  word_eq : F=before++(.noise::after)

lemma NoiseSplit.before_take {F : List (Letter D)} (s : NoiseSplit F) :
    s.before=F.take s.before.length := by
  simpa using (congrArg (List.take s.before.length) s.word_eq).symm
lemma NoiseSplit.after_drop {F : List (Letter D)} (s : NoiseSplit F) :
    s.after=F.drop (s.before.length+1) := by
  simpa using (congrArg (List.drop (s.before.length+1)) s.word_eq).symm
lemma NoiseSplit.length_bound {F : List (Letter D)} (s : NoiseSplit F) :
    s.before.length<F.length := by
  have h := congrArg List.length s.word_eq
  simp only [List.length_append,List.length_cons] at h
  omega

def NoiseSplit.code {F : List (Letter D)} (s : NoiseSplit F) : Fin F.length :=
  ⟨s.before.length,s.length_bound⟩
lemma NoiseSplit.code_injective (F : List (Letter D)) :
    Function.Injective (NoiseSplit.code (F := F)) := by
  intro a b h
  have hh : a.before.length=b.before.length := congrArg Fin.val h
  apply NoiseSplit.ext
  · rw [a.before_take,b.before_take,hh]
  · rw [a.after_drop,b.after_drop,hh]
instance noiseSplitFinite (F : List (Letter D)) : Finite (NoiseSplit F) :=
  Finite.of_injective _ (NoiseSplit.code_injective F)
instance noiseSplitFintype (F : List (Letter D)) : Fintype (NoiseSplit F) :=
  Fintype.ofFinite _

def shapeAt (P Q : List (Letter D)) :
    NoiseSplit P ⊕ NoiseSplit Q → PairShape (P++(.noise::Q)) P.length
  | .inl s => ⟨s.before,s.after,Q,true,by
      simpa only [List.append_assoc,List.cons_append] using
        congrArg (fun f => f++(.noise::Q)) s.word_eq,by
      have h := congrArg List.length s.word_eq
      simpa using h⟩
  | .inr s => ⟨P,s.before,s.after,false,congrArg (fun f => P++(.noise::f)) s.word_eq,by simp⟩

lemma shapeAt_bijective (P Q : List (Letter D)) : Function.Bijective (shapeAt P Q) := by
  constructor
  · intro a b he
    cases a with
    | inl a =>
      cases b with
      | inl b =>
        apply congrArg Sum.inl
        exact NoiseSplit.ext (congrArg PairShape.before he) (congrArg PairShape.between he)
      | inr b => have hh := congrArg PairShape.closing he; cases hh
    | inr a =>
      cases b with
      | inl b => have hh := congrArg PairShape.closing he; cases hh
      | inr b =>
        apply congrArg Sum.inr
        exact NoiseSplit.ext (congrArg PairShape.between he) (congrArg PairShape.after he)
  · intro s
    cases hc : s.closing with
    | false =>
      have hlen : P.length=s.before.length := by simpa [hc] using s.mark_eq
      have hparts := List.append_inj s.word_eq hlen
      have hP : P=s.before := hparts.1
      have hQ : Q=s.between++(.noise::s.after) := List.cons.inj hparts.2 |>.2
      refine ⟨.inr ⟨s.between,s.after,hQ⟩,?_⟩
      apply PairShape.ext <;> simp [shapeAt,hP,hc]
    | true =>
      have hlen : P.length=(s.before++(.noise::s.between)).length := by
        simpa [hc] using s.mark_eq
      have hw : P++(.noise::Q)=(s.before++(.noise::s.between))++(.noise::s.after) := by
        simpa only [List.append_assoc,List.cons_append] using s.word_eq
      have hparts := List.append_inj hw hlen
      have hP := hparts.1
      have hQ : Q=s.after := List.cons.inj hparts.2 |>.2
      refine ⟨.inl ⟨s.before,s.between,hP⟩,?_⟩
      apply PairShape.ext <;> simp [shapeAt,hQ,hc]

def shapeAtEquiv (P Q : List (Letter D)) :
    (NoiseSplit P ⊕ NoiseSplit Q) ≃ PairShape (P++(.noise::Q)) P.length :=
  Equiv.ofBijective (shapeAt P Q) (shapeAt_bijective P Q)

section Evaluate
variable {ι : Type*} [Fintype ι]

def evaluate (j : ℝ) (v : D→ι→ℝ) (d : Diagram D) : ι→ℝ := (d.map v).value j

@[simp] lemma evaluate_nil (j : ℝ) (v : D→ι→ℝ) (i : ι) :
    evaluate j v .nil i=1 := rfl
@[simp] lemma evaluate_diag (j : ℝ) (v : D→ι→ℝ) (a : D) (d : Diagram D) (i : ι) :
    evaluate j v (.diag a d) i=v a i*evaluate j v d i := rfl
@[simp] lemma evaluate_arch (j : ℝ) (v : D→ι→ℝ) (d e : Diagram D) (i : ι) :
    evaluate j v (.arch d e) i=j*mean (evaluate j v d)*evaluate j v e i := rfl

lemma evaluate_insert (j : ℝ) (v : D→ι→ℝ) (d e : Diagram D) (p : ℕ) (i : ι) :
    evaluate j v (d.insert p e) i = j*mean (evaluate j v e)*evaluate j v d i := by
  induction d generalizing p i with
  | nil => simp only [insert]; split_ifs <;> rfl
  | diag a d ih =>
    by_cases hp : p=0
    · simp [hp]
    · simp only [insert,hp,↓reduceIte,evaluate_diag,ih]; ring
  | arch a b ia ib =>
    by_cases hp : p=0
    · simp [hp]
    · simp only [insert,hp,↓reduceIte]
      split_ifs
      · have hh : evaluate j v (a.insert (p-1) e) =
            fun k => j*mean (evaluate j v e)*evaluate j v a k := funext (ia (p-1))
        simp only [evaluate_arch,hh,mean_const_mul]; ring
      · simp only [evaluate_arch,ib]; ring

def expect (j : ℝ) (v : D→ι→ℝ) (F : List (Letter D)) (i : ι) : ℝ :=
  ∑ d : Paired F, evaluate j v d.val i

lemma mean_expect (j : ℝ) (v : D→ι→ℝ) (F : List (Letter D)) :
    mean (expect j v F) = ∑ d : Paired F, mean (evaluate j v d.val) := by
  simp only [mean,expect]
  rw [Finset.sum_comm,Finset.sum_div]

lemma expect_cut (j : ℝ) (v : D→ι→ℝ) (F : List (Letter D)) (k : ℕ)
    (hk : F[k]?=some .noise) (i : ι) :
    expect j v F i = ∑ s : PairShape F k,
      j * mean (expect j v s.between) * expect j v (s.before++s.after) i := by
  let e := (cutEquiv F k hk).trans (separateEquiv F k)
  have he : expect j v F i = ∑ z : Separated F k,
      j*mean (evaluate j v z.2.1.val)*evaluate j v z.2.2.val i := by
    apply Fintype.sum_equiv e
    intro d
    have hd : d.val.word[k]?=some .noise := by rw [d.property]; exact hk
    have hc := cut_spec d.val k _ (cut_markedCut d.val k hd)
    change evaluate j v d.val i =
      j*mean (evaluate j v (d.val.markedCut k hd).inside)*
        evaluate j v (d.val.markedCut k hd).outside i
    exact (congrArg (fun a => evaluate j v a i) hc.2.2).symm.trans
      (evaluate_insert j v _ _ _ i)
  rw [he]
  change (∑ z : Σ s : PairShape F k, Paired s.between × Paired (s.before++s.after),
    j*mean (evaluate j v z.2.1.val)*evaluate j v z.2.2.val i) = _
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro s _
  rw [Fintype.sum_prod_type]
  change (∑ a : Paired s.between, ∑ b : Paired (s.before++s.after),
    j*mean (evaluate j v a.val)*evaluate j v b.val i) = _
  simp_rw [← Finset.mul_sum]
  rw [← Finset.sum_mul,← Finset.mul_sum,← mean_expect]
  rfl

theorem expect_at (j : ℝ) (v : D→ι→ℝ) (P Q : List (Letter D)) (i : ι) :
    expect j v (P++(.noise::Q)) i =
      (∑ s : NoiseSplit P, j*mean (expect j v s.after)*expect j v (s.before++Q) i) +
      (∑ s : NoiseSplit Q, j*mean (expect j v s.before)*expect j v (P++s.after) i) := by
  rw [expect_cut j v _ P.length (by simp)]
  have hh := Fintype.sum_equiv (shapeAtEquiv P Q)
    (fun s : NoiseSplit P ⊕ NoiseSplit Q => match s with
      | .inl s => j*mean (expect j v s.after)*expect j v (s.before++Q) i
      | .inr s => j*mean (expect j v s.before)*expect j v (P++s.after) i)
    (fun s => j*mean (expect j v s.between)*expect j v (s.before++s.after) i)
    (by intro s; cases s <;> rfl)
  rw [← hh,Fintype.sum_sum_type]

end Evaluate
end Diagram
end SKGap.Noncrossing

noncomputable section
open scoped BigOperators

end
end
end
end
end
end
end
end

end OAI
