import Mathlib.Basic.Real.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace OAI

/-!
# Finite weighted probability and independent Bernoulli coordinates

Events are finite sets and their weights are finite sums. Normalization and
nonnegativity are explicit hypotheses for the generic probability inequalities.
The product identities are algebraic, so their statements also hold at the
boundary parameters zero and one without dividing by any point weight.
-/

universe uOmega uI uKey uAlpha uBeta

namespace QuantitativeVanDerWaerden.FiniteProbability

open scoped BigOperators

noncomputable section

variable {Ω : Type uOmega} {I : Type uI}

/-- The weight of a finite event. -/
def prob (w : Ω → ℝ) (A : Finset Ω) : ℝ := ∑ ω ∈ A, w ω

@[simp] theorem prob_empty (w : Ω → ℝ) : prob w ∅ = 0 := by
  simp [prob]

@[simp] theorem prob_univ [Fintype Ω] (w : Ω → ℝ) :
    prob w Finset.univ = ∑ ω, w ω := rfl

theorem prob_nonneg {w : Ω → ℝ} (hw : ∀ ω, 0 ≤ w ω) (A : Finset Ω) :
    0 ≤ prob w A :=
  Finset.sum_nonneg (fun ω _ => hw ω)

theorem prob_mono {w : Ω → ℝ} (hw : ∀ ω, 0 ≤ w ω)
    {A B : Finset Ω} (hAB : A ⊆ B) : prob w A ≤ prob w B :=
  Finset.sum_le_sum_of_subset_of_nonneg hAB (fun ω _ _ => hw ω)

section DecidableEvents
variable [DecidableEq Ω]

theorem prob_union_le {w : Ω → ℝ} (hw : ∀ ω, 0 ≤ w ω)
    (A B : Finset Ω) : prob w (A ∪ B) ≤ prob w A + prob w B := by
  have hid : prob w (A ∪ B) + prob w (A ∩ B) = prob w A + prob w B :=
    Finset.sum_union_inter
  have hn := prob_nonneg hw (A ∩ B)
  linarith

/-- Finite union bound; events need not be independent. -/
theorem prob_biUnion_le {w : Ω → ℝ} (hw : ∀ ω, 0 ≤ w ω)
    (J : Finset I) (A : I → Finset Ω) :
    prob w (J.biUnion A) ≤ ∑ i ∈ J, prob w (A i) := by
  classical
  induction J using Finset.induction_on with
  | empty => simp [prob]
  | @insert i J hi ih =>
      rw [Finset.biUnion_insert, Finset.sum_insert hi]
      exact (prob_union_le hw (A i) (J.biUnion A)).trans (add_le_add le_rfl ih)

/-- A normalized event of weight strictly below one misses a point. -/
theorem exists_not_mem_of_prob_lt_one [Fintype Ω] {w : Ω → ℝ}
    (hw : ∑ ω, w ω = 1) (A : Finset Ω) (hA : prob w A < 1) :
    ∃ ω, ω ∉ A := by
  classical
  by_contra h
  have hfull : A = Finset.univ := by
    apply Finset.ext
    intro ω
    simp only [Finset.mem_univ, iff_true]
    by_contra hω
    exact h ⟨ω, hω⟩
  have heq : prob w A = 1 := by simpa [hfull] using hw
  linarith

/-- If the sum of bad-event probabilities is below one, avoid all of them. -/
theorem exists_avoiding_of_sum_probs_lt_one [Fintype Ω] {w : Ω → ℝ}
    (hw : ∀ ω, 0 ≤ w ω) (htotal : ∑ ω, w ω = 1)
    (J : Finset I) (A : I → Finset Ω)
    (hbudget : (∑ i ∈ J, prob w (A i)) < 1) :
    ∃ ω, ∀ i ∈ J, ω ∉ A i := by
  obtain ⟨ω, hω⟩ := exists_not_mem_of_prob_lt_one htotal (J.biUnion A)
    ((prob_biUnion_le hw J A).trans_lt hbudget)
  refine ⟨ω, ?_⟩
  intro i hi hmem
  exact hω (Finset.mem_biUnion.mpr ⟨i, hi, hmem⟩)

end DecidableEvents

/-- A single Bernoulli coordinate gives weight `p` to `true`. -/
def bitWeight (p : ℝ) (b : Bool) : ℝ := if b then p else 1 - p

variable {Key : Type uKey} [Fintype Key]

/-- Product weight on the actual finite space of all bit assignments. -/
def bernoulliWeight (p : ℝ) (ω : Key → Bool) : ℝ :=
  ∏ i, bitWeight p (ω i)

theorem bernoulliWeight_nonneg {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1)
    (ω : Key → Bool) : 0 ≤ bernoulliWeight p ω := by
  apply Finset.prod_nonneg
  intro i _
  cases ω i <;> simp only [bitWeight, Bool.false_eq_true, ↓reduceIte]
  · exact sub_nonneg.mpr hp'
  · exact hp

variable [DecidableEq Key]

/-- The product Bernoulli weights sum to one, including `p = 0` and `p = 1`. -/
theorem sum_bernoulliWeight (p : ℝ) :
    ∑ ω : Key → Bool, bernoulliWeight p ω = 1 := by
  classical
  have hbit : (∑ b : Bool, bitWeight p b) = 1 := by
    simp [bitWeight]
  unfold bernoulliWeight
  rw [← Fintype.prod_sum]
  simp only [hbit, Finset.prod_const_one]

/-- Product expectation for independent bits, expressed entirely by finite sums. -/
theorem expectation_prod (p : ℝ) (f : Key → Bool → ℝ) :
    (∑ ω : Key → Bool, bernoulliWeight p ω * ∏ i, f i (ω i)) =
      ∏ i, ((1 - p) * f i false + p * f i true) := by
  classical
  calc
    (∑ ω : Key → Bool, bernoulliWeight p ω * ∏ i, f i (ω i)) =
        ∑ ω : Key → Bool, ∏ i, bitWeight p (ω i) * f i (ω i) := by
      simp only [bernoulliWeight, Finset.prod_mul_distrib]
    _ = ∏ i, ∑ b : Bool, bitWeight p b * f i b :=
      (Fintype.prod_sum (fun i b => bitWeight p b * f i b)).symm
    _ = ∏ i, ((1 - p) * f i false + p * f i true) := by
      apply Finset.prod_congr rfl
      intro i _
      simp [bitWeight, add_comm]

/-- Each coordinate may restrict its bit independently. -/
def coordinateEvent (P : Key → Bool → Prop) : Finset (Key → Bool) := by
  classical
  exact Finset.univ.filter (fun ω => ∀ i, P i (ω i))

/-- Exact weight of arbitrary coordinatewise restrictions. -/
theorem prob_coordinateEvent (p : ℝ) (P : Key → Bool → Prop)
    [∀ i, DecidablePred (P i)] :
    prob (bernoulliWeight p) (coordinateEvent P) =
      ∏ i, ∑ b : Bool, if P i b then bitWeight p b else 0 := by
  classical
  unfold prob coordinateEvent
  rw [Finset.sum_filter]
  calc
    _ = ∑ ω : Key → Bool, ∏ i, if P i (ω i) then bitWeight p (ω i) else 0 := by
      apply Finset.sum_congr rfl
      intro ω _
      rw [Fintype.prod_ite_zero]
      by_cases h : ∀ i, P i (ω i)
      · simp only [ite_eq_left h, bernoulliWeight]
      · simp only [ite_eq_right h]
    _ = ∏ i, ∑ b : Bool, if P i b then bitWeight p b else 0 :=
      (Fintype.prod_sum (fun i b => if P i b then bitWeight p b else 0)).symm

/-- Assign prescribed bits on a named finite set of distinct keys. -/
def cylinder (S : Finset Key) (a : Key → Bool) : Finset (Key → Bool) := by
  classical
  exact Finset.univ.filter (fun ω => ∀ i ∈ S, ω i = a i)

@[simp] theorem mem_cylinder (S : Finset Key) (a ω : Key → Bool) :
    ω ∈ cylinder S a ↔ ∀ i ∈ S, ω i = a i := by
  classical
  simp [cylinder]

/-- Exact cylinder probability; coordinates outside `S` are summed out. -/
theorem prob_bernoulli_cylinder (p : ℝ) (S : Finset Key) (a : Key → Bool) :
    prob (bernoulliWeight p) (cylinder S a) =
      ∏ i ∈ S, if a i then p else 1 - p := by
  classical
  have hc : cylinder S a = coordinateEvent (fun i b => i ∈ S → b = a i) := by
    ext ω
    simp [cylinder, coordinateEvent]
  rw [hc, prob_coordinateEvent]
  calc
    (∏ i, ∑ b : Bool, if i ∈ S → b = a i then bitWeight p b else 0) =
        ∏ i, if i ∈ S then bitWeight p (a i) else 1 := by
      apply Finset.prod_congr rfl
      intro i _
      by_cases hi : i ∈ S <;> cases a i <;>
        simp [bitWeight, hi]
    _ = ∏ i ∈ S, if a i then p else 1 - p := by
      simpa only [bitWeight] using
        (Fintype.prod_ite_mem S (fun i => bitWeight p (a i)))

/-- A finite event is determined by the coordinates in its declared support. -/
def DependsOn (S : Finset Key) (E : Finset (Key → Bool)) : Prop :=
  ∀ ω η, (∀ i ∈ S, ω i = η i) → (ω ∈ E ↔ η ∈ E)

private def splice (S : Finset Key) (ω η : Key → Bool) : Key → Bool :=
  fun i => if i ∈ S then ω i else η i

/-- Exchange the complementary coordinates between two complete assignments. -/
private def coordinateSwap (S : Finset Key) :
    ((Key → Bool) × (Key → Bool)) ≃ ((Key → Bool) × (Key → Bool)) where
  toFun z := (splice S z.1 z.2, splice S z.2 z.1)
  invFun z := (splice S z.1 z.2, splice S z.2 z.1)
  left_inv z := by
    apply Prod.ext <;> funext i <;> by_cases hi : i ∈ S <;> simp [splice, hi]
  right_inv z := by
    apply Prod.ext <;> funext i <;> by_cases hi : i ∈ S <;> simp [splice, hi]

private theorem bernoulliWeight_splice (p : ℝ) (S : Finset Key)
    (ω η : Key → Bool) :
    bernoulliWeight p (splice S ω η) * bernoulliWeight p (splice S η ω) =
      bernoulliWeight p ω * bernoulliWeight p η := by
  unfold bernoulliWeight
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  by_cases hi : i ∈ S <;> simp [splice, hi, mul_comm]

private theorem sum_pair_product {α : Type uAlpha} {β : Type uBeta} [Fintype α] [Fintype β]
    (f : α → ℝ) (g : β → ℝ) :
    (∑ z : α × β, f z.1 * g z.2) = (∑ x, f x) * (∑ y, g y) := by
  simp only [Fintype.sum_prod_type, Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_comm

/-- Arbitrary functions of disjoint sets of coordinates factor under the
actual finite Bernoulli weights. The proof swaps two complete assignments. -/
theorem expectation_mul_of_disjoint_supports (p : ℝ) (S T : Finset Key)
    (hST : Disjoint S T) (f g : (Key → Bool) → ℝ)
    (hf : ∀ ω η, (∀ i ∈ S, ω i = η i) → f ω = f η)
    (hg : ∀ ω η, (∀ i ∈ T, ω i = η i) → g ω = g η) :
    (∑ ω : Key → Bool, bernoulliWeight p ω * f ω * g ω) =
      (∑ ω : Key → Bool, bernoulliWeight p ω * f ω) *
      (∑ ω : Key → Bool, bernoulliWeight p ω * g ω) := by
  classical
  have hsum :
      (∑ z : (Key → Bool) × (Key → Bool),
        (bernoulliWeight p z.1 * f z.1 * g z.1) * bernoulliWeight p z.2) =
      ∑ z : (Key → Bool) × (Key → Bool),
        (bernoulliWeight p z.1 * f z.1) * (bernoulliWeight p z.2 * g z.2) := by
    apply Fintype.sum_equiv (coordinateSwap S)
    intro z
    change (bernoulliWeight p z.1 * f z.1 * g z.1) * bernoulliWeight p z.2 =
      (bernoulliWeight p (splice S z.1 z.2) * f (splice S z.1 z.2)) *
      (bernoulliWeight p (splice S z.2 z.1) * g (splice S z.2 z.1))
    have hf' : f (splice S z.1 z.2) = f z.1 := by
      apply hf
      intro i hi
      simp [splice, hi]
    have hg' : g (splice S z.2 z.1) = g z.1 := by
      apply hg
      intro i hi
      have hin : i ∉ S := fun his => Finset.disjoint_left.mp hST his hi
      simp [splice, hin]
    rw [hf', hg']
    calc
      (bernoulliWeight p z.1 * f z.1 * g z.1) * bernoulliWeight p z.2 =
          (bernoulliWeight p z.1 * bernoulliWeight p z.2) * (f z.1 * g z.1) := by ring
      _ = (bernoulliWeight p (splice S z.1 z.2) *
          bernoulliWeight p (splice S z.2 z.1)) * (f z.1 * g z.1) := by
        rw [bernoulliWeight_splice]
      _ = (bernoulliWeight p (splice S z.1 z.2) * f z.1) *
          (bernoulliWeight p (splice S z.2 z.1) * g z.1) := by ring
  have hleft := sum_pair_product
    (fun ω : Key → Bool => bernoulliWeight p ω * f ω * g ω)
    (fun η : Key → Bool => bernoulliWeight p η)
  have hright := sum_pair_product
    (fun ω : Key → Bool => bernoulliWeight p ω * f ω)
    (fun η : Key → Bool => bernoulliWeight p η * g η)
  rw [hleft, hright, sum_bernoulliWeight, mul_one] at hsum
  exact hsum

/-- Finite-event mass as the expectation of its zero-one indicator. -/
theorem prob_eq_sum_indicator [Fintype Ω] [DecidableEq Ω]
    (w : Ω → ℝ) (E : Finset Ω) :
    prob w E = ∑ ω, w ω * (if ω ∈ E then (1 : ℝ) else 0) := by
  classical
  have hfilter : Finset.univ.filter (fun ω => ω ∈ E) = E := by
    ext ω
    simp
  calc
    prob w E = ∑ ω ∈ Finset.univ.filter (fun ω => ω ∈ E), w ω := by
      rw [hfilter]
      rfl
    _ = ∑ ω, w ω * (if ω ∈ E then (1 : ℝ) else 0) := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro ω _
      by_cases hω : ω ∈ E <;> simp [hω]

/-- Actual events depending on disjoint key sets are independent. No cylinder
restriction or probability-factorization hypothesis is imposed on the events. -/
theorem prob_inter_of_disjoint_supports (p : ℝ)
    (E F : Finset (Key → Bool)) (S T : Finset Key)
    (hE : DependsOn S E) (hF : DependsOn T F) (hST : Disjoint S T) :
    prob (bernoulliWeight p) (E ∩ F) =
      prob (bernoulliWeight p) E * prob (bernoulliWeight p) F := by
  classical
  simp only [prob_eq_sum_indicator]
  calc
    (∑ ω : Key → Bool, bernoulliWeight p ω *
        (if ω ∈ E ∩ F then (1 : ℝ) else 0)) =
      ∑ ω : Key → Bool, bernoulliWeight p ω *
        (if ω ∈ E then (1 : ℝ) else 0) * (if ω ∈ F then (1 : ℝ) else 0) := by
      apply Finset.sum_congr rfl
      intro ω _
      by_cases he : ω ∈ E <;> by_cases hf : ω ∈ F <;> simp [he, hf]
    _ = (∑ ω : Key → Bool, bernoulliWeight p ω * (if ω ∈ E then (1 : ℝ) else 0)) *
        (∑ ω : Key → Bool, bernoulliWeight p ω * (if ω ∈ F then (1 : ℝ) else 0)) := by
      apply expectation_mul_of_disjoint_supports p S T hST
      · intro ω η h
        simp only [hE ω η h]
      · intro ω η h
        simp only [hF ω η h]

end

end QuantitativeVanDerWaerden.FiniteProbability

end OAI
