import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.OfFn
import OAI.Combinatorics.BalancedRyser.Probability.ExposureInterleaving

namespace OAI

noncomputable section

namespace Balanced.ExposureInterleaving

abbrev stepLinearOrder {n m : ℕ} {γ : ℝ} (hγ : 0 < γ) : LinearOrder (Step n m) := by
  classical
  letI : IsStrictTotalOrder (Step n m) (Before γ) :=
    { irrefl := before_irrefl γ
      trans := fun _ _ _ => before_trans hγ
      trichotomous := fun s t hst hts =>
        ((before_trichotomy γ s t).resolve_left hst).resolve_right hts }
  exact linearOrderOfSTO (Before γ)

def timeEquiv {n m : ℕ} {γ : ℝ} (hγ : 0 < γ) : Fin (n + m) ≃ Step n m := by
  letI : LE (Step n m) := (stepLinearOrder (n := n) (m := m) hγ).toLE
  letI : LT (Step n m) := (stepLinearOrder (n := n) (m := m) hγ).toLT
  letI := stepLinearOrder (n := n) (m := m) hγ
  exact (Fintype.orderIsoFinOfCardEq (Step n m) (k := n + m) (by simp [Step])).toEquiv

theorem timeEquiv_before_iff {n m : ℕ} {γ : ℝ} (hγ : 0 < γ)
    (i j : Fin (n + m)) :
    Before γ (timeEquiv hγ i) (timeEquiv hγ j) ↔ i < j := by
  let : LE (Step n m) := (stepLinearOrder (n := n) (m := m) hγ).toLE
  let : LT (Step n m) := (stepLinearOrder (n := n) (m := m) hγ).toLT
  let := stepLinearOrder (n := n) (m := m) hγ
  exact @OrderIso.lt_iff_lt (Fin (n + m)) (Step n m) inferInstance
    (stepLinearOrder hγ).toPreorder
    (@Fintype.orderIsoFinOfCardEq (Step n m) (stepLinearOrder hγ) inferInstance
      (n + m) (by simp [Step])) i j

def scheduleList {n m : ℕ} {γ : ℝ} (hγ : 0 < γ) : List (Step n m) :=
  List.ofFn (timeEquiv hγ)

@[simp] theorem schedule_length {n m : ℕ} {γ : ℝ} (hγ : 0 < γ) :
    (scheduleList (n := n) (m := m) hγ).length = n + m := by
  simp [scheduleList]

@[simp] theorem mem_schedule {n m : ℕ} {γ : ℝ} (hγ : 0 < γ)
    (s : Step n m) : s ∈ scheduleList hγ := by
  exact List.mem_ofFn.mpr ((timeEquiv hγ).surjective s)

theorem schedule_pairwise {n m : ℕ} {γ : ℝ} (hγ : 0 < γ) :
    (scheduleList (n := n) (m := m) hγ).Pairwise (Before γ) := by
  rw [scheduleList, List.pairwise_ofFn]
  intro i j hij
  exact (timeEquiv_before_iff hγ i j).mpr hij

theorem schedule_nodup {n m : ℕ} {γ : ℝ} (hγ : 0 < γ) :
    (scheduleList (n := n) (m := m) hγ).Nodup := by
  exact (schedule_pairwise hγ).imp (fun {s t} h => by
    intro heq
    subst t
    exact before_irrefl γ s h)

def deletionTime {n m : ℕ} {γ : ℝ} (hγ : 0 < γ) (i : Fin n) : Fin (n + m) :=
  (timeEquiv hγ).symm (Sum.inl i)

def coverTime {n m : ℕ} {γ : ℝ} (hγ : 0 < γ) (j : Fin m) : Fin (n + m) :=
  (timeEquiv hγ).symm (Sum.inr j)

theorem mem_previousD_iff_time {n m : ℕ} {γ : ℝ} (hγ : 0 < γ)
    (t : Fin (n + m)) (i : Fin n) :
    i ∈ previousD γ (timeEquiv hγ t) ↔ deletionTime hγ i < t := by
  classical
  simp only [previousD, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [← timeEquiv_before_iff hγ]
  simp [deletionTime]

theorem mem_previousC_iff_time {n m : ℕ} {γ : ℝ} (hγ : 0 < γ)
    (t : Fin (n + m)) (j : Fin m) :
    j ∈ previousC γ (timeEquiv hγ t) ↔ coverTime hγ j < t := by
  classical
  simp only [previousC, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [← timeEquiv_before_iff hγ]
  simp [coverTime]

theorem mem_remainingD_iff_time {n m : ℕ} {γ : ℝ} (hγ : 0 < γ)
    (t : Fin (n + m)) (i : Fin n) :
    i ∈ remainingD γ (timeEquiv hγ t) ↔ t ≤ deletionTime hγ i := by
  classical
  have h := mem_previousD_iff_time hγ t i
  simpa only [previousD, remainingD, Finset.mem_filter, Finset.mem_univ,
    true_and, not_lt] using not_congr h

theorem mem_remainingC_iff_time {n m : ℕ} {γ : ℝ} (hγ : 0 < γ)
    (t : Fin (n + m)) (j : Fin m) :
    j ∈ remainingC γ (timeEquiv hγ t) ↔ t ≤ coverTime hγ j := by
  classical
  have h := mem_previousC_iff_time hγ t j
  simpa only [previousC, remainingC, Finset.mem_filter, Finset.mem_univ,
    true_and, not_lt] using not_congr h

theorem previousD_mono_time {n m : ℕ} {γ : ℝ} (hγ : 0 < γ)
    {s t : Fin (n + m)} (hst : s ≤ t) :
    previousD γ (timeEquiv hγ s) ⊆ previousD γ (timeEquiv hγ t) := by
  intro i hi
  exact (mem_previousD_iff_time hγ t i).mpr
    (((mem_previousD_iff_time hγ s i).mp hi).trans_le hst)

theorem previousC_mono_time {n m : ℕ} {γ : ℝ} (hγ : 0 < γ)
    {s t : Fin (n + m)} (hst : s ≤ t) :
    previousC γ (timeEquiv hγ s) ⊆ previousC γ (timeEquiv hγ t) := by
  intro j hj
  exact (mem_previousC_iff_time hγ t j).mpr
    (((mem_previousC_iff_time hγ s j).mp hj).trans_le hst)

theorem sum_timeEquiv {n m : ℕ} {γ : ℝ} (hγ : 0 < γ)
    (f : Step n m → ℝ) :
    (∑ t : Fin (n + m), f (timeEquiv hγ t)) =
      (∑ i : Fin n, f (Sum.inl i)) + ∑ j : Fin m, f (Sum.inr j) := by
  classical
  rw [(timeEquiv hγ).sum_comp f, Fintype.sum_sum_type]

theorem sum_parameters {n m : ℕ} {γ : ℝ} (hγ : 0 < γ) (f : ℝ → ℝ) :
    (∑ t : Fin (n + m), f (parameter γ (timeEquiv hγ t))) =
      (∑ i : Fin n, f (grid i)) + ∑ j : Fin m, f (coverGrid γ j) :=
  sum_timeEquiv hγ (fun s => f (parameter γ s))

end Balanced.ExposureInterleaving

end

end OAI
