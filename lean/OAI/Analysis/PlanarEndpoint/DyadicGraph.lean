import OAI.Analysis.PlanarEndpoint.Fourier
import OAI.Analysis.PlanarEndpoint.GraphDual
import OAI.Analysis.PlanarEndpoint.TimeTree

namespace OAI

/-! Gaussian regularization, Fourier evolution and endpoint maximal estimates. -/


noncomputable section
open MeasureTheory Set
namespace PlanarEndpoint.DyadicGraph

def width (s : List Bool) : ℝ := (1 / 2 : ℝ) ^ s.length

def left : List Bool → ℝ
  | [] => 0
  | false :: s => left s
  | true :: s => left s + width s / 2

def interval (s : List Bool) : Set ℝ := Ico (left s) (left s + width s)

lemma width_pos (s : List Bool) : 0 < width s := pow_pos (by norm_num) _

lemma width_cons (b : Bool) (s : List Bool) : width (b :: s) = width s / 2 := by
  simp only [width, List.length_cons, pow_succ]
  ring

@[simp] lemma interval_nil : interval [] = Ico 0 1 := by norm_num [interval, left, width]

lemma interval_false (s : List Bool) :
    interval (false :: s) = Ico (left s) (left s + width s / 2) := by
  simp only [interval, left, width_cons]

lemma interval_true (s : List Bool) :
    interval (true :: s) = Ico (left s + width s / 2) (left s + width s) := by
  simp only [interval, left, width_cons]
  congr 1
  ring

lemma interval_split (s : List Bool) :
    interval s = interval (false :: s) ∪ interval (true :: s) := by
  rw [interval_false, interval_true]
  exact (Ico_union_Ico_eq_Ico (by linarith [width_pos s]) (by linarith [width_pos s])).symm

lemma interval_disjoint (s : List Bool) :
    Disjoint (interval (false :: s)) (interval (true :: s)) := by
  rw [interval_false, interval_true]
  apply Set.disjoint_left.mpr
  intro t ht hf
  exact (not_lt_of_ge hf.1) ht.2

lemma interval_child_subset (b : Bool) (s : List Bool) :
    interval (b :: s) ⊆ interval s := by
  rw [interval_split s]
  cases b
  · exact subset_union_left
  · exact subset_union_right

lemma interval_subset_root (s : List Bool) : interval s ⊆ Ico 0 1 := by
  induction s with
  | nil => rw [interval_nil]
  | cons b s ih => exact (interval_child_subset b s).trans ih

lemma interval_measurable (s : List Bool) : MeasurableSet (interval s) := measurableSet_Ico

lemma interval_level_partition (n : ℕ) :
    ⋃ s ∈ TimeTree.level n, interval s = Ico 0 1 := by
  induction n with
  | zero => simp [TimeTree.level]
  | succ n ih =>
    calc
      _ = ⋃ s ∈ TimeTree.level n, (interval (false :: s) ∪ interval (true :: s)) := by
        ext t
        simp only [TimeTree.level, Finset.mem_union, Finset.mem_image, Set.mem_iUnion,
          Set.mem_union]
        constructor
        · rintro ⟨s, (⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩), ht⟩
          · exact ⟨a, ha, Or.inl ht⟩
          · exact ⟨a, ha, Or.inr ht⟩
        · rintro ⟨s, hs, ht | ht⟩
          · exact ⟨false :: s, Or.inl ⟨s, hs, rfl⟩, ht⟩
          · exact ⟨true :: s, Or.inr ⟨s, hs, rfl⟩, ht⟩
      _ = _ := by simp_rw [← interval_split]; exact ih

def index : List Bool → ℕ
  | [] => 0
  | false :: s => 2 * index s
  | true :: s => 2 * index s + 1

lemma index_lt (s : List Bool) : index s < 2 ^ s.length := by
  induction s with
  | nil => simp [index]
  | cons b s ih => cases b <;> simp only [index, List.length_cons, pow_succ] <;> omega

lemma index_injective {s t : List Bool} (hlen : s.length = t.length)
    (hi : index s = index t) : s = t := by
  induction s generalizing t with
  | nil => simpa using hlen.symm
  | cons b s ih =>
    cases t with
    | nil => simp at hlen
    | cons c t =>
      have hl : s.length = t.length := by simpa using hlen
      cases b <;> cases c <;> simp only [index] at hi
      · exact congrArg (List.cons false) (ih hl (by omega))
      · omega
      · omega
      · exact congrArg (List.cons true) (ih hl (by omega))

lemma left_eq (s : List Bool) : left s = (index s : ℝ) * width s := by
  induction s with
  | nil => simp [left, index]
  | cons b s ih =>
    cases b <;> simp only [left, index, width_cons, Nat.cast_add, Nat.cast_mul,
      Nat.cast_ofNat, Nat.cast_one, ih] <;> ring

lemma interval_eq (s : List Bool) :
    interval s = Ico ((index s : ℝ) * width s) (((index s : ℝ)+1) * width s) := by
  rw [interval, left_eq]
  congr 1
  ring

lemma sum_level {E : Type*} [AddCommMonoid E] (G : List Bool → E)
    (hsplit : ∀ s, G s = G (false :: s) + G (true :: s)) (n : ℕ) :
    ∑ s ∈ TimeTree.level n, G s = G [] := by
  classical
  induction n with
  | zero => simp [TimeTree.level]
  | succ n ih =>
    rw [TimeTree.level, Finset.sum_union (TimeTree.level_children_disjoint n)]
    rw [Finset.sum_image (fun a _ b _ h => List.cons.inj h |>.2),
      Finset.sum_image (fun a _ b _ h => List.cons.inj h |>.2)]
    rw [← Finset.sum_add_distrib]
    simp_rw [← hsplit]
    exact ih

def fiber {X : Type*} (T : X → ℝ) (s : List Bool) : Set X := T ⁻¹' interval s

lemma fiber_split {X : Type*} (T : X → ℝ) (s : List Bool) :
    fiber T s = fiber T (false :: s) ∪ fiber T (true :: s) := by
  simp only [fiber, interval_split s, preimage_union]

lemma fiber_disjoint {X : Type*} (T : X → ℝ) (s : List Bool) :
    Disjoint (fiber T (false :: s)) (fiber T (true :: s)) :=
  (interval_disjoint s).preimage T

lemma fiber_measurable {X : Type*} [MeasurableSpace X] {T : X → ℝ}
    (hT : Measurable T) (s : List Bool) : MeasurableSet (fiber T s) :=
  hT (interval_measurable s)

def massTree {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]
    (T : X → ℝ) (hT : Measurable T) : TimeTree.MassTree where
  mass s := μ.real (fiber T s)
  nonneg _ := ENNReal.toReal_nonneg
  split s := by
    rw [fiber_split T s, measureReal_union (fiber_disjoint T s) (fiber_measurable hT _)]

lemma massTree_root {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]
    (T : X → ℝ) (hT : Measurable T) (ht : ∀ᵐ x ∂μ, T x ∈ Ico 0 1) :
    (massTree μ T hT).mass [] = μ.real univ := by
  dsimp [massTree]
  apply measureReal_congr
  filter_upwards [ht] with x hx
  apply propext
  change (T x ∈ interval []) ↔ True
  simpa only [interval_nil, iff_true] using hx

lemma restrict_fiber_split {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (T : X → ℝ) (hT : Measurable T) (s : List Bool) :
    μ.restrict (fiber T s) = μ.restrict (fiber T (false :: s)) +
      μ.restrict (fiber T (true :: s)) := by
  rw [fiber_split T s, Measure.restrict_union (fiber_disjoint T s) (fiber_measurable hT _)]

def vector (χ : Plane → ℂ) (hχ : MemLp χ 2 volume)
    (μ : Measure Plane) [IsFiniteMeasure μ]
    (T : Plane → ℝ) (w : Plane → ℂ) (hT : Measurable T) (hw : Measurable w)
    (hb : ∀ x, ‖w x‖ ≤ 1) (s : List Bool) : L2 :=
  graphLp χ hχ (μ.restrict (fiber T s)) T w hT hw hb

lemma vector_split (χ : Plane → ℂ) (hχ : MemLp χ 2 volume)
    (μ : Measure Plane) [IsFiniteMeasure μ]
    (T : Plane → ℝ) (w : Plane → ℂ) (hT : Measurable T) (hw : Measurable w)
    (hb : ∀ x, ‖w x‖ ≤ 1) (s : List Bool) :
    vector χ hχ μ T w hT hw hb s = vector χ hχ μ T w hT hw hb (false :: s) +
      vector χ hχ μ T w hT hw hb (true :: s) := by
  unfold vector
  simpa only [restrict_fiber_split μ T hT s] using
    graphLp_add_measure χ hχ (μ.restrict (fiber T (false :: s)))
      (μ.restrict (fiber T (true :: s))) T w hT hw hb

lemma vector_level_sum (χ : Plane → ℂ) (hχ : MemLp χ 2 volume)
    (μ : Measure Plane) [IsFiniteMeasure μ]
    (T : Plane → ℝ) (w : Plane → ℂ) (hT : Measurable T) (hw : Measurable w)
    (hb : ∀ x, ‖w x‖ ≤ 1) (n : ℕ) :
    ∑ s ∈ TimeTree.level n, vector χ hχ μ T w hT hw hb s =
      vector χ hχ μ T w hT hw hb [] :=
  sum_level _ (vector_split χ hχ μ T w hT hw hb) n

lemma mass_level_sum {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]
    (T : X → ℝ) (hT : Measurable T) (n : ℕ) :
    ∑ s ∈ TimeTree.level n, (massTree μ T hT).mass s = (massTree μ T hT).mass [] :=
  sum_level _ (massTree μ T hT).split n

end PlanarEndpoint.DyadicGraph
end

end OAI
