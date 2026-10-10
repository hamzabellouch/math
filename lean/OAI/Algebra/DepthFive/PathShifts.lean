import Mathlib

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem335

/-- The signed occupation shift of a layered path. -/
def pathShift {α : Type*} {n : ℕ} (sgn : Fin n → ℤ)
    (p : Fin (n + 1) → α) : (Fin n × α × α) →₀ ℤ :=
  ∑ t, Finsupp.single (t, p t.castSucc, p t.succ) (sgn t)

/-- A coordinate in one layer can only come from that layer. -/
theorem pathShift_apply {α : Type*} [DecidableEq α] {n : ℕ} (sgn : Fin n → ℤ)
    (p : Fin (n + 1) → α) (t : Fin n) (a b : α) :
    pathShift sgn p (t, a, b) =
      if (p t.castSucc, p t.succ) = (a, b) then sgn t else 0 := by
  classical
  unfold pathShift
  rw [Finsupp.finsetSum_apply, Finset.sum_eq_single t]
  · simp [Finsupp.single_apply]
  · intro j hj hjt
    simp [hjt]
  · simp

/-- Nonzero signed shifts remember every edge of their path. -/
theorem pathShift_eq_imp_edges_eq {α : Type*} {n : ℕ}
    (sgn : Fin n → ℤ) (hs : ∀ t, sgn t ≠ 0)
    {p q : Fin (n + 1) → α} (heq : pathShift sgn p = pathShift sgn q)
    (t : Fin n) :
    (p t.castSucc, p t.succ) = (q t.castSucc, q t.succ) := by
  classical
  have h := congrArg (fun f => f (t, p t.castSucc, p t.succ)) heq
  rw [pathShift_apply, pathShift_apply] at h
  simp only [ite_true] at h
  split_ifs at h with he
  · exact he.symm
  · exact False.elim (hs t h)

/-- Even a zero-length path is determined by its starting vertex and shift. -/
theorem pathShift_eq_imp_eq_of_start_eq {α : Type*} {n : ℕ}
    (sgn : Fin n → ℤ) (hs : ∀ t, sgn t ≠ 0)
    {p q : Fin (n + 1) → α} (hstart : p 0 = q 0)
    (heq : pathShift sgn p = pathShift sgn q) : p = q := by
  funext i
  refine Fin.cases hstart (fun j => ?_) i
  exact congrArg Prod.snd (pathShift_eq_imp_edges_eq sgn hs heq j)

/-- For positive length, no endpoint assumption is needed. -/
theorem pathShift_injective {α : Type*} {n : ℕ} (hn : 0 < n)
    (sgn : Fin n → ℤ) (hs : ∀ t, sgn t ≠ 0) :
    Function.Injective (pathShift (α := α) sgn) := by
  intro p q heq
  apply pathShift_eq_imp_eq_of_start_eq sgn hs _ heq
  have h := congrArg Prod.fst (pathShift_eq_imp_edges_eq sgn hs heq ⟨0, hn⟩)
  simpa using h

/-- Translating the path shifts by one input occupation does not merge paths. -/
theorem translated_pathShift_injective {α : Type*} {n : ℕ} (hn : 0 < n)
    (sgn : Fin n → ℤ) (hs : ∀ t, sgn t ≠ 0)
    (input : (Fin n × α × α) →₀ ℤ) :
    Function.Injective (fun p : Fin (n + 1) → α => input + pathShift sgn p) := by
  intro p q heq
  exact pathShift_injective hn sgn hs (add_left_cancel heq)

/-- Global compatibility of four path shifts is exactly compatibility in
 each layer separately. The nonzero signs cancel, so the local condition
 is independent of whether that layer differentiates or multiplies. -/
theorem pathShift_sub_eq_iff {α : Type*} {n : ℕ}
    (sgn : Fin n → ℤ) (hs : ∀ t, sgn t ≠ 0)
    (p q r s : Fin (n + 1) → α) :
    pathShift sgn p - pathShift sgn q = pathShift sgn r - pathShift sgn s ↔
      ∀ t : Fin n,
        Finsupp.single (p t.castSucc, p t.succ) (1 : ℤ) -
          Finsupp.single (q t.castSucc, q t.succ) 1 =
        Finsupp.single (r t.castSucc, r t.succ) 1 -
          Finsupp.single (s t.castSucc, s t.succ) 1 := by
  classical
  constructor
  · intro heq t
    ext ab
    rcases ab with ⟨a, b⟩
    have h := congrArg (fun f => f (t, a, b)) heq
    simp only [Finsupp.sub_apply, pathShift_apply] at h
    apply mul_left_cancel₀ (hs t)
    simpa only [Finsupp.sub_apply, Finsupp.single_apply, mul_sub, mul_ite,
      mul_one, mul_zero] using h
  · intro heq
    ext tab
    rcases tab with ⟨t, a, b⟩
    have h := congrArg (fun f => sgn t * f (a, b)) (heq t)
    simpa only [Finsupp.sub_apply, pathShift_apply, Finsupp.single_apply,
      mul_sub, mul_ite, mul_one, mul_zero] using h

end Problem335

end

end OAI
