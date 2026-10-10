import Mathlib
import OAI.LinearAlgebra.MatrixFields.Histories.HistoryChildLaws

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.AllFieldHistory

open AllFieldParameters
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

def secondMass (t : Shape) : ℚ :=
  2 * (positiveInitial.map (fun g => initialLaw g * stageALaw g t)).sum

def littleMass (t u : Shape) : ℚ := 2 * secondMass t * stageBLaw t u

private theorem subtype_sum_indicator_inline_MatrixMultiplication_AllFieldHistorySums {A : Type*} [Fintype A]
    (P : A → Prop) [DecidablePred P] [Fintype {a // P a}] (f : A → ℝ) :
    (∑ a : {a // P a}, f a.val) = ∑ a, if P a then f a else 0 := by
  rw [← Finset.sum_filter]
  exact (Finset.sum_subtype _ (by simp) f).symm

private theorem list_filter_sum_inline_MatrixMultiplication_AllFieldHistorySums {A : Type*} (xs : List A) (p : A → Bool)
    (f : A → ℝ) :
    ((xs.filter p).map f).sum = (xs.map (fun a => if p a then f a else 0)).sum := by
  induction xs with
  | nil => simp
  | cons a xs ih => cases hp : p a <;> simp [hp, ih]

private theorem list_sum_congr {A : Type*} (xs : List A) (f g : A → ℝ)
    (h : ∀ a ∈ xs, f a = g a) : (xs.map f).sum = (xs.map g).sum :=
  congrArg List.sum (List.map_congr_left h)

private theorem list_sum_comm {A B : Type*} (xs : List A) (ys : List B)
    (f : A → B → ℝ) :
    (xs.map (fun a => (ys.map (f a)).sum)).sum =
      (ys.map (fun b => (xs.map (fun a => f a b)).sum)).sum := by
  induction xs with
  | nil => simp
  | cons a xs ih => simp [ih, List.sum_map_add]

private theorem list_rat_cast_inline_MatrixMultiplication_AllFieldHistorySums {A : Type*} (xs : List A) (f : A → ℚ) :
    ((xs.map f).sum : ℝ) = (xs.map (fun a => (f a : ℝ))).sum := by
  induction xs with
  | nil => simp
  | cons a xs ih => simp [ih]

 theorem secondMass_cast (t : Shape) :
    (secondMass t : ℝ) =
      2 * (positiveInitial.map (fun g => (initialLaw g : ℝ) * (stageALaw g t : ℝ))).sum := by
  simp only [secondMass, Rat.cast_mul, Rat.cast_ofNat, list_rat_cast_inline_MatrixMultiplication_AllFieldHistorySums]

 theorem littleMass_cast (t u : Shape) :
    (littleMass t u : ℝ) = 2 * (secondMass t : ℝ) * (stageBLaw t u : ℝ) := by
  simp only [littleMass, Rat.cast_mul, Rat.cast_ofNat]

 theorem initial_history_sum (K : ℕ) (f : Shape → ℝ) :
    (∑ h : Initial K, (initialAmount h : ℝ) * f (initialShape h)) =
      (K : ℝ) * (sortedInitial.map (fun g => (initialLaw g : ℝ) * f g)).sum := by
  simp only [Fintype.sum_prod_type, initialAmount, initialShape, List.get_eq_getElem]
  simp_rw [Fin.sum_univ_fun_getElem sortedInitial (fun g => (initialLaw g : ℝ) * f g)]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

theorem initial_positive_sum (K : ℕ) (f : Shape → ℝ) :
    (∑ h : InitialPositive K, f (initialShape h.val)) =
      (K : ℝ) * (positiveInitial.map f).sum := by
  rw [subtype_sum_indicator_inline_MatrixMultiplication_AllFieldHistorySums (fun h : Initial K => initialShape h ∈ positiveInitial)
    (fun h => f (initialShape h))]
  change (∑ history : Initial K,
    if sortedInitial[history.2.val] ∈ positiveInitial then f sortedInitial[history.2.val] else 0) = _
  simp only [Fintype.sum_prod_type]
  simp_rw [Fin.sum_univ_fun_getElem sortedInitial
    (fun g => if g ∈ positiveInitial then f g else 0)]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  apply congrArg (fun r : ℝ => (K : ℝ) * r)
  change _ = ((sortedInitial.filter positive).map f).sum
  rw [list_filter_sum_inline_MatrixMultiplication_AllFieldHistorySums]
  apply list_sum_congr
  intro g hg
  simp only [positiveInitial, List.mem_filter, hg, true_and]

private theorem stageA_parent_sum : ∀ g ∈ positiveInitial, g 0 + g 1 + g 2 = 16 := by
  decide +kernel

private theorem stageA_extend_sum (g : Shape) (hg : g ∈ positiveInitial)
    (f : Shape → ℝ) :
    ((below g).map (fun t => (stageALaw g t : ℝ) * f t)).sum =
      ((shapes 8).map (fun t => (stageALaw g t : ℝ) * f t)).sum := by
  have he : below g = (shapes 8).filter
      (fun t => t 0 ≤ g 0 && t 1 ≤ g 1 && t 2 ≤ g 2) := by
    simp only [below, stageA_parent_sum g hg]
  rw [he, list_filter_sum_inline_MatrixMultiplication_AllFieldHistorySums]
  apply list_sum_congr
  intro t ht
  by_cases hb : (t 0 ≤ g 0 && t 1 ≤ g 1 && t 2 ≤ g 2) = true
  · simp only [hb, ite_true]
  · have hnot : t ∉ below g := by rw [he]; simp [hb]
    have hz : stageALaw g t = 0 := splitLaw_outside_support _ _ g t hnot
    simp [hb, hz]

 theorem a_parent_history_sum {K : ℕ} (h : InitialPositive K) (f : Shape → ℝ) :
    (∑ p : ASplit h × Bool, (aAmount ⟨h, p⟩ : ℝ) * f (aShape ⟨h, p⟩)) =
      2 * (initialAmount h.val : ℝ) *
        ((below (initialShape h.val)).map
          (fun t => (stageALaw (initialShape h.val) t : ℝ) * f t)).sum := by
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, aAmount, aShape, aSplit,
    halfShape, Bool.false_eq_true, ite_false, ite_true, Rat.cast_mul,
    List.get_eq_getElem]
  simp only [mul_assoc, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [Fin.sum_univ_fun_getElem (below (initialShape h.val))
    (fun t => (stageALaw (initialShape h.val) t : ℝ) *
      f (complement (initialShape h.val) t)),
    Fin.sum_univ_fun_getElem (below (initialShape h.val))
      (fun t => (stageALaw (initialShape h.val) t : ℝ) * f t),
    stageA_complement_sum _ h.property]
  ring

 theorem a_history_sum_parents (K : ℕ) (f : Shape → ℝ) :
    (∑ h : AfterA K, (aAmount h : ℝ) * f (aShape h)) =
      (K : ℝ) * (positiveInitial.map (fun g => 2 * (initialLaw g : ℝ) *
        ((below g).map (fun t => (stageALaw g t : ℝ) * f t)).sum)).sum := by
  rw [Fintype.sum_sigma]
  simp only [a_parent_history_sum, initialAmount]
  exact initial_positive_sum K (fun g => 2 * (initialLaw g : ℝ) *
    ((below g).map (fun t => (stageALaw g t : ℝ) * f t)).sum)

 theorem a_history_sum (K : ℕ) (f : Shape → ℝ) :
    (∑ h : AfterA K, (aAmount h : ℝ) * f (aShape h)) =
      (K : ℝ) * ((shapes 8).map (fun t => (secondMass t : ℝ) * f t)).sum := by
  rw [a_history_sum_parents]
  apply congrArg (fun r : ℝ => (K : ℝ) * r)
  calc
    _ = (positiveInitial.map (fun g => ((shapes 8).map
        (fun t => 2 * (initialLaw g : ℝ) * ((stageALaw g t : ℝ) * f t))).sum)).sum := by
      apply list_sum_congr
      intro g hg
      rw [stageA_extend_sum g hg, List.sum_map_mul_left]
    _ = ((shapes 8).map (fun t => (positiveInitial.map
        (fun g => 2 * (initialLaw g : ℝ) * ((stageALaw g t : ℝ) * f t))).sum)).sum :=
      list_sum_comm _ _ _
    _ = _ := by
      apply list_sum_congr
      intro t _
      rw [secondMass_cast]
      calc
        _ = (positiveInitial.map
            (fun g => 2 * ((initialLaw g : ℝ) * (stageALaw g t : ℝ)) * f t)).sum := by
          apply list_sum_congr
          intro g _
          ring
        _ = _ := by rw [List.sum_map_mul_right, List.sum_map_mul_left]

 theorem a_positive_history_sum (K : ℕ) (f : Shape → ℝ) :
    (∑ h : APositive K, (aAmount h.val : ℝ) * f (aShape h.val)) =
      (K : ℝ) * (positiveSecond.map (fun t => (secondMass t : ℝ) * f t)).sum := by
  rw [subtype_sum_indicator_inline_MatrixMultiplication_AllFieldHistorySums (fun h : AfterA K => aShape h ∈ positiveSecond)
    (fun h => (aAmount h : ℝ) * f (aShape h))]
  trans ∑ h : AfterA K, (aAmount h : ℝ) *
    (if aShape h ∈ positiveSecond then f (aShape h) else 0)
  · apply Finset.sum_congr rfl
    intro h _
    split_ifs <;> simp_all
  rw [a_history_sum K (fun t => if t ∈ positiveSecond then f t else 0)]
  apply congrArg (fun r : ℝ => (K : ℝ) * r)
  change _ = (((shapes 8).filter positive).map
    (fun t => (secondMass t : ℝ) * f t)).sum
  rw [list_filter_sum_inline_MatrixMultiplication_AllFieldHistorySums]
  apply list_sum_congr
  intro t ht
  simp only [positiveSecond, List.mem_filter, ht, true_and]
  split_ifs <;> simp_all

 theorem b_parent_history_sum {K : ℕ} (h : APositive K) (f : Shape → ℝ) :
    (∑ p : BSplit h × Bool, (bAmount ⟨h, p⟩ : ℝ) * f (bShape ⟨h, p⟩)) =
      2 * (aAmount h.val : ℝ) *
        ((below (aShape h.val)).map
          (fun u => (stageBLaw (aShape h.val) u : ℝ) * f u)).sum := by
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, bAmount, bShape, bSplit,
    halfShape, Bool.false_eq_true, ite_false, ite_true, Rat.cast_mul,
    List.get_eq_getElem]
  simp only [mul_assoc, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [Fin.sum_univ_fun_getElem (below (aShape h.val))
    (fun u => (stageBLaw (aShape h.val) u : ℝ) *
      f (complement (aShape h.val) u)),
    Fin.sum_univ_fun_getElem (below (aShape h.val))
      (fun u => (stageBLaw (aShape h.val) u : ℝ) * f u),
    stageB_complement_sum _ h.property]
  ring

 theorem b_history_sum (K : ℕ) (f : Shape → Shape → ℝ) :
    (∑ h : AfterB K, (bAmount h : ℝ) * f (aShape h.1.val) (bShape h)) =
      (K : ℝ) * (positiveSecond.map (fun t =>
        ((below t).map (fun u => (littleMass t u : ℝ) * f t u)).sum)).sum := by
  rw [Fintype.sum_sigma]
  simp only [b_parent_history_sum]
  have he : (∑ h : APositive K, 2 * (aAmount h.val : ℝ) *
      ((below (aShape h.val)).map
        (fun u => (stageBLaw (aShape h.val) u : ℝ) * f (aShape h.val) u)).sum) =
      ∑ h : APositive K, (aAmount h.val : ℝ) *
        (2 * ((below (aShape h.val)).map
          (fun u => (stageBLaw (aShape h.val) u : ℝ) * f (aShape h.val) u)).sum) := by
    apply Finset.sum_congr rfl
    intro h _
    ring
  rw [he, a_positive_history_sum K (fun t =>
    2 * ((below t).map (fun u => (stageBLaw t u : ℝ) * f t u)).sum)]
  apply congrArg (fun r : ℝ => (K : ℝ) * r)
  apply list_sum_congr
  intro t _
  calc
    _ = 2 * (secondMass t : ℝ) *
        ((below t).map (fun u => (stageBLaw t u : ℝ) * f t u)).sum := by ring
    _ = _ := by
      rw [← List.sum_map_mul_left]
      apply list_sum_congr
      intro u _
      rw [littleMass_cast]
      ring

 theorem b_positive_history_sum (K : ℕ) (f : Shape → Shape → ℝ) :
    (∑ h : BPositive K, (bAmount h.val : ℝ) *
      f (aShape h.val.1.val) (bShape h.val)) =
      (K : ℝ) * (positiveSecond.map (fun t =>
        (((below t).filter positive).map
          (fun u => (littleMass t u : ℝ) * f t u)).sum)).sum := by
  rw [subtype_sum_indicator_inline_MatrixMultiplication_AllFieldHistorySums (fun h : AfterB K => positive (bShape h) = true)
    (fun h => (bAmount h : ℝ) * f (aShape h.1.val) (bShape h))]
  trans ∑ h : AfterB K, (bAmount h : ℝ) *
    (if positive (bShape h) then f (aShape h.1.val) (bShape h) else 0)
  · apply Finset.sum_congr rfl
    intro h _
    split_ifs <;> simp_all
  rw [b_history_sum K (fun t u => if positive u then f t u else 0)]
  apply congrArg (fun r : ℝ => (K : ℝ) * r)
  apply list_sum_congr
  intro t _
  rw [list_filter_sum_inline_MatrixMultiplication_AllFieldHistorySums]
  apply list_sum_congr
  intro u _
  split_ifs <;> simp_all

end MatrixMultiplication.AllFieldHistory

end
end

end MatrixAllFields

end OAI
