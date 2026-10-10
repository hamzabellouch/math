import OAI.Analysis.LipschitzHilbert.Estimates.WeightedOrder

namespace OAI

/-! The first member of a set in a size-biased random order has the normalized
weights on that set, regardless of the other elements being ordered. -/

noncomputable section

open scoped BigOperators

namespace LipschitzHilbert

variable {ι : Type*} [DecidableEq ι]

def firstFrom (S : Finset ι) : List ι → Option ι
  | [] => none
  | j :: l => if j ∈ S then some j else firstFrom S l

def arrivalEvent (S : Finset ι) (i : ι) (l : List ι) : ℝ :=
  if firstFrom S l = some i then 1 else 0

theorem arrivalEvent_cons_of_mem (S : Finset ι) (i j : ι) (hj : j ∈ S) :
    (fun l => arrivalEvent S i (j :: l)) = fun _ => if j = i then 1 else 0 := by
  funext l
  simp [arrivalEvent, firstFrom, hj]

theorem arrivalEvent_cons_of_not_mem (S : Finset ι) (i j : ι) (hj : j ∉ S) :
    (fun l => arrivalEvent S i (j :: l)) = arrivalEvent S i := by
  funext l
  simp [arrivalEvent, firstFrom, hj]

theorem first_step_identity (w : ι → ℝ) (s S : Finset ι) (i : ι)
    (hsub : S ⊆ s) (hi : i ∈ S) (hs : orderMass w s ≠ 0)
    (hS : orderMass w S ≠ 0) :
    (∑ j : s, w j / orderMass w s *
      (if j.val ∈ S then if j.val = i then 1 else 0 else w i / orderMass w S)) =
      w i / orderMass w S := by
  have heq (j : ι) : w j / orderMass w s *
      (if j ∈ S then if j = i then 1 else 0 else w i / orderMass w S) =
      (if j = i then w i / orderMass w s else 0) +
        (if j ∈ S then 0 else w j) / orderMass w s * (w i / orderMass w S) := by
    by_cases hj : j ∈ S
    · by_cases hji : j = i
      · subst j; simp [hi]
      · simp [hj, hji]
    · have hji : j ≠ i := fun h => hj (h ▸ hi)
      simp [hj, hji]
  rw [Finset.sum_coe_sort s (fun j => w j / orderMass w s *
    (if j ∈ S then if j = i then 1 else 0 else w i / orderMass w S))]
  simp_rw [heq]
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq' s i (fun _ => w i / orderMass w s)]
  simp only [hsub hi, ite_true]
  rw [← Finset.sum_mul, ← Finset.sum_div]
  have hout : (∑ j ∈ s, if j ∈ S then 0 else w j) = orderMass w s - orderMass w S := by
    have hpoint (j : ι) : (if j ∈ S then 0 else w j) = w j - if j ∈ S then w j else 0 := by
      split_ifs <;> ring
    simp_rw [hpoint]
    rw [Finset.sum_sub_distrib]
    congr 1
    rw [← Finset.sum_filter]
    congr 1
    ext j
    simp only [Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨hsub h, h⟩⟩
  rw [hout]
  field_simp
  ring

theorem orderAverage_arrivalEvent (w : ι → ℝ) (s S : Finset ι) (i : ι)
    (hw : ∀ j ∈ s, 0 < w j) (hsub : S ⊆ s) (hi : i ∈ S) :
    orderAverage w s (arrivalEvent S i) = w i / orderMass w S := by
  induction s using Finset.strongInductionOn with
  | _ s ih =>
    have hs : s.Nonempty := ⟨i, hsub hi⟩
    rw [orderAverage_nonempty w s hs]
    have hrec (j : s) :
        orderAverage w (s.erase j.val) (fun l => arrivalEvent S i (j.val :: l)) =
          if j.val ∈ S then if j.val = i then 1 else 0 else w i / orderMass w S := by
      by_cases hj : j.val ∈ S
      · rw [ite_eq_left hj, arrivalEvent_cons_of_mem S i j hj]
        exact orderAverage_const w (s.erase j.val)
          (fun k hk => hw k (Finset.mem_of_mem_erase hk)) _
      · rw [ite_eq_right hj, arrivalEvent_cons_of_not_mem S i j hj]
        apply ih _ (Finset.erase_ssubset j.property)
          (fun k hk => hw k (Finset.mem_of_mem_erase hk))
        · intro k hk
          exact Finset.mem_erase.mpr ⟨fun h => hj (h ▸ hk), hsub hk⟩
    simp_rw [hrec]
    exact first_step_identity w s S i hsub hi
      (orderMass_pos w s hw hs).ne'
      (orderMass_pos w S (fun j hj => hw j (hsub hj)) ⟨i, hi⟩).ne'

end LipschitzHilbert

end

end OAI
