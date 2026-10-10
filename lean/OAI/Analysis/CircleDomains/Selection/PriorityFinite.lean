import OAI.Analysis.CircleDomains.Modulus.PriorityWeights

namespace OAI

/-! Identification of the finite recursive interpolation with the
priority-weight formula, for passage from local finite sums to the
countable interpolation. -/
open Set Function
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

variable {E : Type*}

 theorem priorityBlend_append (L M : List ((E → ℝ) × ℝ)) (X : E → ℝ) :
    priorityBlend (L++M) X = priorityBlend L (priorityBlend M X) := by
  induction L with
  | nil => rfl
  | cons e L ih => simp only [List.cons_append, priorityBlend, ih]

 theorem priorityResidual_append (L M : List ((E → ℝ) × ℝ)) (p : E) :
    priorityResidual (L++M) p = priorityResidual L p*priorityResidual M p := by
  induction L with
  | nil => simp [priorityResidual]
  | cons e L ih => simp only [List.cons_append, priorityResidual, ih]; ring

 theorem priorityBlend_sub (L : List ((E → ℝ) × ℝ)) (X Y : E → ℝ) (p : E) :
    priorityBlend L X p-priorityBlend L Y p = priorityResidual L p*(X p-Y p) := by
  induction L with
  | nil => simp [priorityBlend, priorityResidual]
  | cons e L ih =>
    change e.1 p*e.2+(1-e.1 p)*priorityBlend L X p-
      (e.1 p*e.2+(1-e.1 p)*priorityBlend L Y p) =
      (1-e.1 p)*priorityResidual L p*(X p-Y p)
    calc
      _ = (1-e.1 p)*(priorityBlend L X p-priorityBlend L Y p) := by ring
      _ = _ := by rw [ih]; ring

 def priorityList (χ : ℕ → E → ℝ) (c : ℕ → ℝ) (n : ℕ) : List ((E → ℝ) × ℝ) :=
  (List.range n).map (fun i => (χ i, c i))

 theorem priorityList_succ (χ : ℕ → E → ℝ) (c : ℕ → ℝ) (n : ℕ) :
    priorityList χ c (n+1) = priorityList χ c n++[(χ n,c n)] := by
  simp [priorityList, List.range_succ]

 theorem priorityList_residual (χ : ℕ → E → ℝ) (c : ℕ → ℝ) (n : ℕ) (p : E) :
    priorityResidual (priorityList χ c n) p = priorityRemainder (fun i => χ i p) n := by
  induction n with
  | zero => simp [priorityList, priorityResidual, priorityRemainder]
  | succ n ih =>
    rw [priorityList_succ, priorityResidual_append, ih, priorityRemainder_succ]
    simp [priorityResidual]

 theorem priorityList_value (χ : ℕ → E → ℝ) (c : ℕ → ℝ) (X : E → ℝ) (n : ℕ) (p : E) :
    priorityBlend (priorityList χ c n) X p =
      priorityRemainder (fun i => χ i p) n*X p +
        ∑ i ∈ Finset.range n, priorityWeight (fun j => χ j p) i*c i := by
  induction n with
  | zero => simp [priorityList, priorityBlend, priorityRemainder]
  | succ n ih =>
    rw [priorityList_succ, priorityBlend_append]
    have h := priorityBlend_sub (priorityList χ c n) (priorityBlend [(χ n,c n)] X) X p
    rw [priorityList_residual, ih] at h
    simp only [priorityBlend] at h
    rw [priorityRemainder_succ, Finset.sum_range_succ]
    dsimp only [priorityBlend, priorityWeight] at h ⊢
    nlinarith only [h]

 theorem priorityInfiniteValue_eq_finite {χ : ℕ → E → ℝ} (c : ℕ → ℝ) (X : E → ℝ)
    {N : ℕ} {p : E} (hz : ∀ n, N ≤ n → χ n p = 0) :
    priorityInfiniteValue (fun n => χ n p) c (X p) = priorityBlend (priorityList χ c N) X p := by
  have hw (n : ℕ) (hn : n ∉ Finset.range N) : priorityWeight (fun i => χ i p) n = 0 := by
    rw [priorityWeight, hz n (by simpa only [Finset.mem_range, not_lt] using hn), zero_mul]
  have hs : (∑' n, priorityWeight (fun i => χ i p) n) =
      ∑ n ∈ Finset.range N, priorityWeight (fun i => χ i p) n := tsum_eq_sum hw
  have hsc : (∑' n, priorityWeight (fun i => χ i p) n*c n) =
      ∑ n ∈ Finset.range N, priorityWeight (fun i => χ i p) n*c n :=
    tsum_eq_sum (fun n hn => by rw [hw n hn, zero_mul])
  rw [priorityInfiniteValue, hs, hsc, priorityWeight_sum, priorityList_value]
  ring

end CircleDomainRigidity

end

end OAI
