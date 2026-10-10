import Mathlib

namespace OAI

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter

namespace SKRatioGaussian

abbrev Spin (n : ℕ) := Fin n → Bool
abbrev Edge (n : ℕ) := {p : Fin n × Fin n // p.1 < p.2}
abbrev Disorder (n : ℕ) := Edge n → ℝ

def spinValue (b : Bool) : ℝ := if b then 1 else -1

def coupling {n : ℕ} (g : Disorder n) (i k : Fin n) : ℝ :=
  if h : i < k then g ⟨(i, k), h⟩ else
    if h : k < i then g ⟨(k, i), h⟩ else 0

def hamiltonian {n : ℕ} (g : Disorder n) (h : Fin n → ℝ) (x : Spin n) : ℝ :=
  (1 / 2 : ℝ) * ∑ i, ∑ k, spinValue (x i) * coupling g i k * spinValue (x k) +
    ∑ i, h i * spinValue (x i)

def weight {n : ℕ} (g : Disorder n) (h : Fin n → ℝ) (x : Spin n) : ℝ :=
  Real.exp (hamiltonian g h x)

def partition {n : ℕ} (g : Disorder n) (h : Fin n → ℝ) : ℝ :=
  ∑ x, weight g h x

def mass {n : ℕ} (g : Disorder n) (h : Fin n → ℝ) (x : Spin n) : ℝ :=
  weight g h x / partition g h

def expectation {n : ℕ} (g : Disorder n) (h : Fin n → ℝ) (f : Spin n → ℝ) : ℝ :=
  ∑ x, mass g h x * f x

def variance {n : ℕ} (g : Disorder n) (h : Fin n → ℝ) (f : Spin n → ℝ) : ℝ :=
  expectation g h (fun x => (f x - expectation g h f) ^ 2)

def flip {n : ℕ} (i : Fin n) (x : Spin n) : Spin n :=
  Function.update x i (!(x i))

def conditionalExpectation {n : ℕ} (g : Disorder n) (h : Fin n → ℝ)
    (i : Fin n) (f : Spin n → ℝ) (x : Spin n) : ℝ :=
  (weight g h x * f x + weight g h (flip i x) * f (flip i x)) /
    (weight g h x + weight g h (flip i x))

def dirichlet {n : ℕ} (g : Disorder n) (h : Fin n → ℝ) (f : Spin n → ℝ) : ℝ :=
  ∑ i, expectation g h (fun x => (f x - conditionalExpectation g h i f x) ^ 2)

def disorderLaw (β : ℝ) (n : ℕ) : Measure (Disorder n) :=
  Measure.pi (fun _ : Edge n => gaussianReal 0 (Real.toNNReal (β ^ 2 / n)))

def poincareEvent (n : ℕ) (C : ℝ) : Set (Disorder n) :=
  {g | ∀ f : Spin n → ℝ, variance g 0 f ≤ C * dirichlet g 0 f}

def discreteGap {n : ℕ} (g : Disorder n) : ℝ :=
  sInf {r : ℝ | ∃ f : Spin n → ℝ, 0 < variance g 0 f ∧
    r = dirichlet g 0 f / ((n : ℝ) * variance g 0 f)}

def MainStatement (β : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧
    Tendsto (fun n : ℕ => disorderLaw β n (poincareEvent n C)) atTop (nhds 1) ∧
    Tendsto (fun n : ℕ => disorderLaw β n {g | 1 / (C * (n : ℝ)) ≤ discreteGap g})
      atTop (nhds 1)

section FiniteSpinCalculus

variable {n : ℕ}

@[simp] theorem spinValue_true : spinValue true = 1 := rfl
@[simp] theorem spinValue_false : spinValue false = -1 := rfl
@[simp] theorem spinValue_not (b : Bool) : spinValue (!b) = -spinValue b := by
  cases b <;> norm_num [spinValue]
@[simp] theorem spinValue_sq (b : Bool) : spinValue b ^ 2 = 1 := by
  cases b <;> norm_num [spinValue]

@[simp] theorem coupling_diag (g : Disorder n) (i : Fin n) : coupling g i i = 0 := by
  simp [coupling]

theorem coupling_symm (g : Disorder n) (i k : Fin n) : coupling g i k = coupling g k i := by
  rcases lt_trichotomy i k with hik | rfl | hki
  · simp [coupling, hik, not_lt_of_gt hik]
  · rfl
  · simp [coupling, hki, not_lt_of_gt hki]

@[simp] theorem flip_same (i : Fin n) (x : Spin n) : flip i x i = !(x i) := by
  simp [flip]

@[simp] theorem flip_other (i k : Fin n) (x : Spin n) (h : k ≠ i) : flip i x k = x k := by
  simp [flip, h]

@[simp] theorem flip_flip (i : Fin n) (x : Spin n) : flip i (flip i x) = x := by
  ext k
  by_cases h : k = i
  · subst k; simp
  · simp [flip_other, h]

def flipEquiv (i : Fin n) : Spin n ≃ Spin n :=
  Function.Involutive.toPerm (flip i) (flip_flip i)

theorem sum_flip (i : Fin n) (f : Spin n → ℝ) : ∑ x, f (flip i x) = ∑ x, f x :=
  (flipEquiv i).sum_comp f

theorem weight_pos (g : Disorder n) (h : Fin n → ℝ) (x : Spin n) :
    0 < weight g h x := Real.exp_pos _

theorem partition_pos (g : Disorder n) (h : Fin n → ℝ) : 0 < partition g h := by
  exact Finset.sum_pos (fun x _ => weight_pos g h x) Finset.univ_nonempty

theorem mass_pos (g : Disorder n) (h : Fin n → ℝ) (x : Spin n) :
    0 < mass g h x := div_pos (weight_pos g h x) (partition_pos g h)

theorem mass_nonneg (g : Disorder n) (h : Fin n → ℝ) (x : Spin n) :
    0 ≤ mass g h x := (mass_pos g h x).le

@[simp] theorem sum_mass (g : Disorder n) (h : Fin n → ℝ) : ∑ x, mass g h x = 1 := by
  simp only [mass, ← Finset.sum_div]
  exact div_self (ne_of_gt (partition_pos g h))

@[simp] theorem expectation_const (g : Disorder n) (h : Fin n → ℝ) (c : ℝ) :
    expectation g h (fun _ => c) = c := by
  simp [expectation, ← Finset.sum_mul]

theorem expectation_add (g : Disorder n) (h : Fin n → ℝ) (f k : Spin n → ℝ) :
    expectation g h (fun x => f x + k x) = expectation g h f + expectation g h k := by
  simp [expectation, mul_add, Finset.sum_add_distrib]

theorem expectation_sub (g : Disorder n) (h : Fin n → ℝ) (f k : Spin n → ℝ) :
    expectation g h (fun x => f x - k x) = expectation g h f - expectation g h k := by
  simp [expectation, mul_sub, Finset.sum_sub_distrib]

theorem expectation_mul_const (g : Disorder n) (h : Fin n → ℝ) (f : Spin n → ℝ) (c : ℝ) :
    expectation g h (fun x => f x * c) = expectation g h f * c := by
  simp only [expectation, Finset.sum_mul, mul_assoc]

theorem expectation_const_mul (g : Disorder n) (h : Fin n → ℝ) (f : Spin n → ℝ) (c : ℝ) :
    expectation g h (fun x => c * f x) = c * expectation g h f := by
  simp only [mul_comm c, expectation_mul_const]

theorem expectation_nonneg (g : Disorder n) (h : Fin n → ℝ) {f : Spin n → ℝ}
    (hf : ∀ x, 0 ≤ f x) : 0 ≤ expectation g h f :=
  Finset.sum_nonneg (fun x _ => mul_nonneg (mass_nonneg g h x) (hf x))

theorem variance_nonneg (g : Disorder n) (h : Fin n → ℝ) (f : Spin n → ℝ) :
    0 ≤ variance g h f := expectation_nonneg g h (fun _ => sq_nonneg _)

theorem dirichlet_nonneg (g : Disorder n) (h : Fin n → ℝ) (f : Spin n → ℝ) :
    0 ≤ dirichlet g h f :=
  Finset.sum_nonneg (fun _ _ => expectation_nonneg g h (fun _ => sq_nonneg _))

theorem variance_eq_zero_iff (g : Disorder n) (h : Fin n → ℝ) (f : Spin n → ℝ) :
    variance g h f = 0 ↔ ∀ x, f x = expectation g h f := by
  unfold variance expectation
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun x _ =>
    mul_nonneg (mass_nonneg g h x) (sq_nonneg _))]
  simp only [Finset.mem_univ, true_implies, mul_eq_zero, ne_of_gt (mass_pos g h _),
    false_or, sq_eq_zero_iff, sub_eq_zero]

theorem variance_pos_of_ne (g : Disorder n) (h : Fin n → ℝ) {f : Spin n → ℝ}
    {x y : Spin n} (hxy : f x ≠ f y) : 0 < variance g h f := by
  refine lt_of_le_of_ne (variance_nonneg g h f) ?_
  intro heq
  have hf := (variance_eq_zero_iff g h f).mp heq.symm
  exact hxy ((hf x).trans (hf y).symm)

theorem exists_positive_variance (g : Disorder n) (hn : 0 < n) :
    ∃ f : Spin n → ℝ, 0 < variance g 0 f := by
  let i : Fin n := ⟨0, hn⟩
  refine ⟨fun x => spinValue (x i), variance_pos_of_ne g 0 (x := fun _ => true)
    (y := fun _ => false) ?_⟩
  norm_num

theorem lower_bound_discreteGap (g : Disorder n) (hn : 0 < n) {C : ℝ} (hC : 0 < C)
    (hP : ∀ f : Spin n → ℝ, variance g 0 f ≤ C * dirichlet g 0 f) :
    1 / (C * (n : ℝ)) ≤ discreteGap g := by
  obtain ⟨f, hf⟩ := exists_positive_variance g hn
  apply le_csInf
  · exact ⟨_, f, hf, rfl⟩
  · rintro r ⟨f, hv, rfl⟩
    have hn' : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
    apply (div_le_div_iff₀ (mul_pos hC hn') (mul_pos hn' hv)).mpr
    nlinarith [mul_le_mul_of_nonneg_left (hP f) hn'.le]

instance disorderLaw_probability (β : ℝ) (n : ℕ) : IsProbabilityMeasure (disorderLaw β n) := by
  unfold disorderLaw
  infer_instance

theorem gap_probability_of_poincare (β C : ℝ) (hC : 0 < C)
    (hP : Tendsto (fun n : ℕ => disorderLaw β n (poincareEvent n C)) atTop (nhds 1)) :
    Tendsto (fun n : ℕ => disorderLaw β n {g | 1 / (C * (n : ℝ)) ≤ discreteGap g})
      atTop (nhds 1) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hP tendsto_const_nhds
  · filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    apply measure_mono
    intro g hg
    exact lower_bound_discreteGap g hn hC hg
  · filter_upwards [] with n
    exact (measure_mono (Set.subset_univ _)).trans_eq (measure_univ)

end FiniteSpinCalculus

end SKRatioGaussian

end

section

noncomputable section

end
end
end

end OAI
