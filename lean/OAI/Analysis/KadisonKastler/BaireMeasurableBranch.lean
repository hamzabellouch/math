import OAI.Analysis.KadisonKastler.BaireSelectionHulls
import Mathlib.MeasureTheory.MeasurableSpace.Constructions

namespace OAI

/-! # Measurable successive choices of Baire digits -/

namespace KadisonKastler

open MeasureTheory Set Filter
open scoped Topology

noncomputable section

variable {X : Type*} [MeasurableSpace X] [TopologicalSpace X] [BorelSpace X]

private instance : MeasurableSpace (List ℕ) := ⊤
private instance : MeasurableSingletonClass (List ℕ) := ⟨fun _ => trivial⟩

def baireNextPredicate (μ : Measure X) (F : (ℕ → ℕ) → X)
    (s : List ℕ) (x : X) (n : ℕ) : Prop :=
  x ∈ baireImageHull μ F (n :: s) ∨
    (n = 0 ∧ ¬∃ m, x ∈ baireImageHull μ F (m :: s))

omit [BorelSpace X] in
theorem baireNextPredicate_exists (μ : Measure X) (F : (ℕ → ℕ) → X) (s : List ℕ) (x : X) :
    ∃ n, baireNextPredicate μ F s x n := by
  classical
  by_cases h : ∃ n, x ∈ baireImageHull μ F (n :: s)
  · obtain ⟨n, hn⟩ := h
    exact ⟨n, Or.inl hn⟩
  · exact ⟨0, Or.inr ⟨rfl, h⟩⟩

@[irreducible] def baireNextDigit (μ : Measure X) (F : (ℕ → ℕ) → X) (s : List ℕ) (x : X) : ℕ := by
  classical
  exact Nat.find (baireNextPredicate_exists μ F s x)

omit [BorelSpace X] in
theorem baireNextDigit_mem (μ : Measure X) (F : (ℕ → ℕ) → X) (s : List ℕ) (x : X)
    (h : ∃ n, x ∈ baireImageHull μ F (n :: s)) :
    x ∈ baireImageHull μ F (baireNextDigit μ F s x :: s) := by
  classical
  unfold baireNextDigit
  have hs := Nat.find_spec (baireNextPredicate_exists μ F s x)
  exact hs.elim id (fun hh => False.elim (hh.2 h))

theorem measurable_baireNextDigit (μ : Measure X) (F : (ℕ → ℕ) → X) (s : List ℕ) :
    Measurable (baireNextDigit μ F s) := by
  classical
  unfold baireNextDigit
  apply measurable_find
  intro n
  by_cases hn : n = 0
  · convert (measurableSet_baireImageHull μ F (n :: s)).union
        (MeasurableSet.iUnion (fun m => measurableSet_baireImageHull μ F (m :: s))).compl using 1
    ext x
    simp only [Set.mem_ofPred_eq, baireNextPredicate, hn, true_and,
      Set.mem_union, Set.mem_compl_iff, Set.mem_iUnion]
  · convert measurableSet_baireImageHull μ F (n :: s) using 1
    ext x
    simp only [Set.mem_ofPred_eq, baireNextPredicate, hn, false_and, or_false]

def baireChosenWord (μ : Measure X) (F : (ℕ → ℕ) → X) : ℕ → X → List ℕ
  | 0, _ => []
  | n + 1, x => baireNextDigit μ F (baireChosenWord μ F n x) x :: baireChosenWord μ F n x

omit [BorelSpace X] in
@[simp] theorem baireChosenWord_length (μ : Measure X) (F : (ℕ → ℕ) → X) (n : ℕ) (x : X) :
    (baireChosenWord μ F n x).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [baireChosenWord, ih]

theorem measurable_baireChosenWord (μ : Measure X) (F : (ℕ → ℕ) → X) (n : ℕ) :
    Measurable (baireChosenWord μ F n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    have hnext : Measurable (fun p : List ℕ × X => baireNextDigit μ F p.1 p.2) :=
      measurable_from_prod_countable_right (measurable_baireNextDigit μ F)
    have hcons : Measurable (fun p : ℕ × List ℕ => p.1 :: p.2) := measurable_of_countable _
    exact hcons.comp ((hnext.comp (ih.prodMk measurable_id)).prodMk ih)

def baireChosenBranch (μ : Measure X) (F : (ℕ → ℕ) → X) (x : X) (n : ℕ) : ℕ :=
  baireNextDigit μ F (baireChosenWord μ F n x) x

theorem measurable_baireChosenDigit (μ : Measure X) (F : (ℕ → ℕ) → X) (n : ℕ) :
    Measurable (fun x => baireNextDigit μ F (baireChosenWord μ F n x) x) := by
  have hnext : Measurable (fun p : List ℕ × X => baireNextDigit μ F p.1 p.2) :=
    measurable_from_prod_countable_right (measurable_baireNextDigit μ F)
  exact hnext.comp ((measurable_baireChosenWord μ F n).prodMk measurable_id)

theorem measurable_baireChosenBranch (μ : Measure X) (F : (ℕ → ℕ) → X) :
    Measurable (baireChosenBranch μ F) := by
  exact Measurable.of_eval (measurable_baireChosenDigit μ F)

omit [BorelSpace X] in
theorem baireChosenBranch_res (μ : Measure X) (F : (ℕ → ℕ) → X) (x : X) (n : ℕ) :
    PiNat.res (baireChosenBranch μ F x) n = baireChosenWord μ F n x := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [PiNat.res_succ, ih, baireChosenBranch, baireChosenWord]

omit [BorelSpace X] in
theorem baireChosenBranch_hull (μ : Measure X) (F : (ℕ → ℕ) → X) (x : X)
    (hx : x ∈ baireImageHull μ F [])
    (hchildren : ∀ s : List ℕ, x ∈ baireImageHull μ F s →
      ∃ n, x ∈ baireImageHull μ F (n :: s)) (n : ℕ) :
    x ∈ baireImageHull μ F (baireChosenWord μ F n x) := by
  induction n with
  | zero => exact hx
  | succ n ih => exact baireNextDigit_mem μ F _ x (hchildren _ ih)

end

end KadisonKastler

end OAI
