import OAI.Analysis.FourierLLogL.Finite.Entropy
/-! # Comparison, data processing and Pinsker -/

open Function Filter Set
open scoped BigOperators
noncomputable section

namespace OAI

namespace FourierLLogL.Law
open Real
universe u v w w'
variable {α : Type u} {β : Type v} {γ : Type w} {η : Type w'}
  [Fintype α] [Fintype β] [Fintype γ] [Fintype η]

lemma kl_ex (P Q : Law α) :
    P.kl Q = P.Ex (fun x => log (P x) - log (Q x)) := by
  unfold kl entropy crossE
  simp only [Ex_sub, Ex_neg]
  ring

lemma after_dominated {P Q : Law α} (h : P.dominated Q) (X : α → β)
    {x : β} (hx : 0 < P.send X x) : (P.after X x).dominated (Q.after X x) := by
  intro a ha
  obtain ⟨rfl, hp⟩ := (after_mem hx).mp ha
  exact Q.after_self_pos X (h a hp)

lemma kl_chain {P Q : Law α} (h : P.dominated Q) (X : α → β) :
    P.kl Q = (P.send X).kl (Q.send X) +
      (P.send X).Ex (fun x => (P.after X x).kl (Q.after X x)) := by
  classical
  simp_rw [kl_ex]
  have hA := P.after_Ex_sum X (fun x a => log ((P.after X x) a)-log ((Q.after X x) a))
  rw [hA,Ex_send, ← Ex_add]
  apply Ex_congr_mem
  intro a ha
  have hh (P : Law α) (ha : 0 < P a) :
      log (P a) = log (P.send X (X a)) + log (P.after X (X a) a) := by
    rw [← log_mul (P.send_pos X ha).ne' (P.after_self_pos X ha).ne',
      send_mul_after, ite_eq_left rfl]

  linarith [hh P ha,hh Q (h a ha)]

lemma kl_data_processing {P Q : Law α} (h : P.dominated Q) (X : α → β) :
    (P.send X).kl (Q.send X) ≤ P.kl Q := by
  rw [kl_chain h X]
  have hh : 0 ≤ (P.send X).Ex (fun x => (P.after X x).kl (Q.after X x)) := by
    rw [← Ex_const (P.send X) 0]
    apply Ex_mono_mem
    exact fun x hx => kl_nonneg (after_dominated h _ hx)
  linarith

def tv (P Q : Law α) := (∑ a, |P a - Q a|) / 2

lemma tv_nonneg (P Q : Law α) : 0 ≤ P.tv Q := by unfold tv; positivity

lemma tv_comm (P Q : Law α) : P.tv Q = Q.tv P := by unfold tv; simp_rw [abs_sub_comm (P _)]

lemma tv_common (P Q : Law α) :
    (∑ a, min (P a) (Q a)) = 1 - P.tv Q := by
  have H (a : α) : min (P a) (Q a) = (P a + Q a - |P a - Q a|)/2 := by grind
  simp_rw [H, ← Finset.sum_div, Finset.sum_sub_distrib, Finset.sum_add_distrib, Law.total]
  unfold tv; ring

lemma tv_le_one (P Q : Law α) : P.tv Q ≤ 1 := by
  have hh : 0 ≤ ∑ a, min (P a) (Q a) :=
    Finset.sum_nonneg fun a _ => le_min (P.nonneg _) (Q.nonneg _)
  rw [tv_common] at hh; linarith

lemma tv_data_processing (P Q : Law α) (X : α → β) :
    (P.send X).tv (Q.send X) ≤ P.tv Q := by
  classical
  suffices H : (∑ y : β, |P.send X y - Q.send X y|) ≤ ∑ x : α, |P x-Q x| by
    unfold tv
    exact div_le_div_of_nonneg_right H (by norm_num)
  simp_rw [send_apply,prob_eq, ← Finset.sum_sub_distrib]
  refine (Finset.sum_le_sum (fun y _ => Finset.abs_sum_le_sum_abs _ _)).trans ?_
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum fun x _ => ?_
  rw [Finset.sum_eq_single (X x)] <;> intros <;> simp_all [eq_comm]

/-- Pinsker (only need numerical constant). Use log tangent inequality on square roots. -/
lemma tv_sq_le_kl {P Q : Law α} (h : P.dominated Q) :
    (P.tv Q)^2 ≤ P.kl Q := by
  let a (x) := √(P x)
  let b (x) := √(Q x)
  have ha (x : α) : (a x)^2 = P x := sq_sqrt (P.nonneg x)
  have hb (x : α) : (b x)^2 = Q x := sq_sqrt (Q.nonneg x)
  have hkl : ∑ x, (a x - b x)^2 ≤ P.kl Q := by
    have H (x : α) :
        (a x - b x)^2 ≤ P x * (log (P x)-log (Q x)) - P x + Q x := by
      obtain hx | hx := eq_or_lt_of_le (P.nonneg x)
      · have hh : a x = 0 := by simp only [a, ← hx,sqrt_zero]
        rw [hh, ← hx]; nlinarith [hb x]
      have hu : 0 < a x := sqrt_pos.mpr hx
      have hv : 0 < b x := sqrt_pos.mpr (h x hx)
      have hh := log_le_sub_one_of_pos (div_pos hv hu)
      rw [log_div hv.ne' hu.ne'] at hh
      have heq (c : ℝ) : log (c^2) = 2*log c := by rw [Real.log_pow]; norm_num
      have hg := mul_le_mul_of_nonneg_right hh (sq_nonneg (a x))
      have he : b x/a x * (a x)^2 = a x * b x := by field_simp
      rw [sub_mul, sub_mul, he] at hg
      rw [← ha x, ← hb x,heq,heq]
      nlinarith
    have hh := Finset.sum_le_sum (s:=Finset.univ) (fun x _ => H x)
    simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib,Law.total,sub_add_cancel] at hh
    rw [kl_ex]; exact hh
  have hab1 : (∑ x, (a x + b x)^2) ≤ 4 := by
    have H (x : α) : (a x+b x)^2 ≤ 2*P x+2*Q x := by
      rw [← ha x,← hb x]
      nlinarith [sq_nonneg (a x - b x)]
    have hh := Finset.sum_le_sum (s:=Finset.univ) (fun x _ => H x)
    simp only [Finset.sum_add_distrib,← Finset.mul_sum,Law.total] at hh
    linarith
  have hdiff (x : α) : |P x-Q x| = |a x - b x| * (a x+b x) := by
    rw [← ha x, ← hb x, sq_sub_sq, abs_mul,
      abs_of_nonneg (add_nonneg (sqrt_nonneg _) (sqrt_nonneg _))]
    exact mul_comm _ _
  have hh := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun x => |a x-b x|) (fun x => a x+b x)
  simp_rw [← hdiff,sq_abs] at hh
  have hi := mul_le_mul hkl hab1 (by positivity) (kl_nonneg h)
  unfold tv
  nlinarith [hh.trans hi]

lemma tv_le_sqrt_kl {P Q : Law α} (h : P.dominated Q) :
    P.tv Q ≤ √(P.kl Q) := by
  nlinarith [tv_sq_le_kl h, Real.sq_sqrt (kl_nonneg h), Real.sqrt_nonneg (P.kl Q)]

end FourierLLogL.Law

end OAI
