import OAI.GroupTheory.PolycyclicRecognition.Analysis.SuccessfulWordPaths
import OAI.GroupTheory.PolycyclicRecognition.Algebra.SourceBundleStates
import Mathlib.Data.List.OfFn

namespace OAI

/-! # Successful switch words remain good at every bundle boundary -/

namespace PolycyclicRecognition

variable {G : Type*} [Group G]

theorem wordSheetsGood_append_iff (A : Set G) (x : G) (u v : List G) :
    WordSheetsGood A x (u ++ v) ↔
      WordSheetsGood A x u ∧ WordSheetsGood A (x * u.prod) v := by
  induction u generalizing x with
  | nil =>
    simp only [List.nil_append, List.prod_nil, mul_one, WordSheetsGood]
    exact ⟨fun h => ⟨h.start, h⟩, fun h => h.2⟩
  | cons g u ih =>
    simp only [List.cons_append, WordSheetsGood, List.prod_cons, ← mul_assoc, ih]
    tauto

theorem WordSheetsGood.grouped {A : Set G} {x : G} {u : List (List G)}
    (h : WordSheetsGood A x u.flatten) : WordSheetsGood A x (u.map List.prod) := by
  induction u generalizing x with
  | nil => exact h
  | cons v u ih =>
    rw [List.flatten_cons] at h
    obtain ⟨hv, hu⟩ := (wordSheetsGood_append_iff A x v u.flatten).mp h
    exact ⟨hv.start, ih hu⟩

omit [Group G] in
theorem ofFn_eq_flatten_bundles {h m : ℕ} (u : Fin (h * m) → G) :
    List.ofFn u = (List.ofFn (fun i : Fin h =>
      List.ofFn (fun j : Fin m => u (finProdFinEquiv (i, j))))).flatten := by
  rw [List.ofFn_mul]
  congr 1
  apply congrArg List.ofFn
  funext i
  apply congrArg List.ofFn
  funext j
  congr 1
  apply Fin.ext
  simp [finProdFinEquiv, Nat.mul_comm, Nat.add_comm]

theorem WordSheetsGood.bundle_products {A : Set G} {x : G} {h m : ℕ}
    {u : Fin (h * m) → G} (hg : WordSheetsGood A x (List.ofFn u)) :
    WordSheetsGood A x (List.ofFn (fun i : Fin h =>
      (List.ofFn (fun j : Fin m => u (finProdFinEquiv (i, j)))).prod)) := by
  rw [ofFn_eq_flatten_bundles] at hg
  simpa only [List.map_ofFn, Function.comp_def] using hg.grouped

variable [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]

theorem WordSheetsGood.prefix_states {A : Set G} {x : G} {h : ℕ}
    {u : Fin h → G} (hg : WordSheetsGood A x (List.ofFn u)) :
    ∀ i, x * prefixCoordinateEquiv h u i ∈ A := by
  induction h generalizing x with
  | zero => intro i; exact Fin.elim0 i
  | succ h ih =>
    rw [List.ofFn_succ] at hg
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · rw [prefixCoordinateEquiv_zero]
      exact hg.2.start
    · rw [prefixCoordinateEquiv_succ, ← mul_assoc]
      exact ih hg.2 j

end PolycyclicRecognition

end OAI
