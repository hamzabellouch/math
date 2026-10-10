import OAI.Analysis.FreeEntropy.WickTensor

namespace OAI

noncomputable section
namespace FiniteEntropySeparation
open Finset FreeSeries
namespace FreeSeries
variable {α : Type} [DecidableEq α]
def monomial (v : List α) : Series α := fun w => if w=v then 1 else 0
@[simp] theorem monomial_nil : monomial ([] : List α) = unit := by
  funext w; cases w <;> simp [monomial, unit]
@[simp] theorem monomial_cons_nil (a : α) (v : List α) : monomial (a::v) [] = 0 := by simp [monomial]
 theorem deriv_monomial (a b : α) (v : List α) :
    FreeSeries.deriv b (monomial (a::v)) = if b=a then monomial v else 0 := by
  funext w
  by_cases h : b=a <;> simp [FreeSeries.deriv, monomial, h]
 theorem monomial_append (v q : List α) : monomial (v++q) = conv (monomial v) (monomial q) := by
  funext w
  induction v generalizing w with
  | nil => simp
  | cons a v ih =>
    cases w with
    | nil => simp
    | cons b w =>
      rw [conv_cons, monomial_cons_nil, zero_mul, zero_add, deriv_monomial]
      by_cases h : b=a
      · subst b; simpa [monomial] using ih w
      · simp [h, monomial]
 theorem monomial_single (i : α) : monomial [i] = letter i := by
  funext w
  cases w with
  | nil => rfl
  | cons a w => cases w <;> simp [monomial, letter]
 theorem conv_subst_letter (F M : Series α) (i : α) (w : List α) :
    conv F (subst M (letter i)) w = ∑ r : Fin w.length, if w[r.val] = i then
      F (w.take r.val) * M (w.drop (r.val+1)) else 0 := by
  rw [conv_sum_splits, sum_range_succ]
  simp only [List.take_length, List.drop_length, subst_nil, letter_nil, mul_zero, add_zero]
  rw [← Fin.sum_univ_eq_sum_range (fun k => F (w.take k) * subst M (letter i) (w.drop k))]
  apply sum_congr rfl
  intro k hk
  rw [List.drop_eq_getElem_cons k.isLt, subst_letter_cons]
  split_ifs <;> simp

variable [Fintype α]
def wordBall (d : ℕ) : Finset (List α) :=
  (range (d+1)).biUnion (fun m => univ.image (fun v : List.Vector α m => v.val))
@[simp] theorem mem_wordBall (v : List α) (d : ℕ) : v ∈ wordBall d ↔ v.length ≤ d := by
  simp only [wordBall, mem_biUnion, mem_range, mem_image, mem_univ, true_and]
  constructor
  · rintro ⟨m,hm,q,rfl⟩; rw [q.prop]; omega
  · intro h; exact ⟨v.length, by omega, ⟨v,rfl⟩, rfl⟩
 theorem monomial_expansion (f : Series α) (d : ℕ) :
    Agree d f (∑ v ∈ wordBall d, f v • monomial v) := by
  intro w hw
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single w]
  · simp [monomial]
  · intro v hv hne; simp [monomial, Ne.symm hne]
  · intro hn; exact (hn ((mem_wordBall w d).mpr hw)).elim

omit [Fintype α] in
theorem monomial_large_agree [Fintype α] (v : List α) (d : ℕ) (h : d < v.length) :
    Agree d (monomial v) 0 := by
  intro w hw
  have hn : w ≠ v := by intro he; subst w; omega
  simp [monomial, hn]
 theorem conv_subst_monomial_large (M : Series α) (v w : List α) (h : w.length < v.length) :
    conv M (subst M (monomial v)) w = 0 := by
  have he := conv_agree (Agree.refl w.length M)
    (subst_agree (Agree.refl _ M) (monomial_large_agree v w.length h)) w le_rfl
  simpa using he
 theorem conv_subst_hasSum (M f : Series α) (w : List α) :
    HasSum (fun v => f v * conv M (subst M (monomial v)) w) (conv M (subst M f) w) := by
  have he := conv_agree (Agree.refl w.length M)
    (subst_agree (Agree.refl _ M) (monomial_expansion f w.length)) w le_rfl
  rw [subst_sum, conv_sum_right] at he
  simp only [subst_smul, conv_smul_right, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at he
  rw [he]
  apply hasSum_sum_of_ne_finset_zero
  intro v hv
  rw [conv_subst_monomial_large M v w (by simpa using hv), mul_zero]
end FreeSeries

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
 theorem reverseDerivativeMoment_monomial {M : VonNeumannAlgebra H} (τ : TracialVector M)
    {n : ℕ} (X : Fin n → H →L[ℂ] H) (js w : List (Fin n)) :
    reverseDerivativeMoment τ X js w =
      conv (wordMoment τ X) (subst (wordMoment τ X) (monomial js.reverse)) w := by
  induction js generalizing w with
  | nil => simp [reverseDerivativeMoment]
  | cons i js ih =>
    rw [List.reverse_cons, monomial_append, subst_mul, ← conv_assoc, monomial_single,
      conv_subst_letter, reverseDerivativeMoment]
    apply sum_congr rfl
    intro r hr
    split_ifs <;> simp [ih]
end FiniteEntropySeparation

end

end OAI
