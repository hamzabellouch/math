import OAI.LinearAlgebra.MatrixMultiplication.FieldParameters.Traversal
import Mathlib.Data.List.Nodup

namespace OAI

/-! Tensor extraction over arbitrary fields and its asymptotic rate. -/

noncomputable section

namespace MatrixMultiplication.AllFieldParameters

theorem list_map_involution_perm {α : Type*} (xs : List α) (f : α → α)
    (hn : xs.Nodup) (hm : ∀ x ∈ xs, f x ∈ xs)
    (hi : ∀ x ∈ xs, f (f x) = x) : (xs.map f).Perm xs := by
  have hinj : ∀ x ∈ xs, ∀ y ∈ xs, f x = f y → x = y := by
    intro x hx y hy hxy
    simpa only [hi x hx, hi y hy] using congrArg f hxy
  apply (List.perm_ext_iff_of_nodup (List.Nodup.map_on hinj hn) hn).2
  intro y
  constructor
  · intro hy
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
    exact hm x hx
  · intro hy
    exact List.mem_map.mpr ⟨f y, hm y hy, hi y hy⟩

theorem list_weighted_involution_sum {α : Type*} (xs : List α) (f : α → α)
    (hn : xs.Nodup) (hm : ∀ x ∈ xs, f x ∈ xs)
    (hi : ∀ x ∈ xs, f (f x) = x) (w h : α → ℝ)
    (hw : ∀ x ∈ xs, w (f x) = w x) :
    (xs.map (fun x => w x * h (f x))).sum =
      (xs.map (fun x => w x * h x)).sum := by
  calc
    _ = ((xs.map f).map (fun x => w x * h x)).sum := by
      congr 1
      rw [List.map_map]
      apply List.map_congr_left
      intro x hx
      simp only [Function.comp_apply, hw x hx]
    _ = _ := ((list_map_involution_perm xs f hn hm hi).map _).sum_eq

theorem complement_involution_of_le (s u : Shape) (hu : ∀ i, u i ≤ s i) :
    complement s (complement s u) = u := by
  funext i
  exact Nat.sub_sub_self (hu i)

theorem stageA_complement_sum (s : Shape) (hs : s ∈ positiveInitial)
    (h : Shape → ℝ) :
    ((below s).map (fun u => (stageALaw s u : ℝ) * h (complement s u))).sum =
      ((below s).map (fun u => (stageALaw s u : ℝ) * h u)).sum := by
  apply list_weighted_involution_sum (below s) (complement s)
    (stageA_children_nodup s hs)
  · intro u hu
    exact (stageA_support_complement s hs u hu).1
  · intro u hu
    exact complement_involution_of_le s u (stageA_support_complement s hs u hu).2
  · intro u hu
    rw [stageALaw_complement s u hs hu]

theorem stageB_complement_sum (s : Shape) (hs : s ∈ positiveSecond)
    (h : Shape → ℝ) :
    ((below s).map (fun u => (stageBLaw s u : ℝ) * h (complement s u))).sum =
      ((below s).map (fun u => (stageBLaw s u : ℝ) * h u)).sum := by
  apply list_weighted_involution_sum (below s) (complement s)
    (stageB_children_nodup s hs)
  · intro u hu
    exact (stageB_support_complement s hs u hu).1
  · intro u hu
    exact complement_involution_of_le s u (stageB_support_complement s hs u hu).2
  · intro u hu
    rw [stageBLaw_complement s u hs hu]

end MatrixMultiplication.AllFieldParameters

end

end OAI
