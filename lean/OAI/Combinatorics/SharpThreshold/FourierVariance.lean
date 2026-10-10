import OAI.Combinatorics.SharpThreshold.FourierBasis
import OAI.Combinatorics.SharpThreshold.Probability

namespace OAI

universe u v

noncomputable section

open scoped BigOperators Classical

namespace Problem313.BiasedFourier

variable {ι : Type u} [Fintype ι]

@[simp] theorem coeff_empty (p : ℝ) (g : (ι → Bool) → ℝ) :
    coeff p g ∅ = ∑ x, weight p x * g x := by
  classical
  simp [coeff]

/-- Algebraic expansion of finite weighted variance. Positivity is not needed. -/
theorem weighted_variance_eq_second_moment {α : Type v} [Fintype α]
    (w g : α → ℝ) (hw : ∑ x, w x = 1) :
    (∑ x, w x * (g x - ∑ y, w y * g y) ^ 2) =
      (∑ x, w x * g x ^ 2) - (∑ x, w x * g x) ^ 2 := by
  classical
  let μ := ∑ x, w x * g x
  change (∑ x, w x * (g x - μ) ^ 2) = (∑ x, w x * g x ^ 2) - μ ^ 2
  calc
    (∑ x, w x * (g x - μ) ^ 2) =
        ∑ x, (w x * g x ^ 2 - 2 * μ * (w x * g x) + μ ^ 2 * w x) := by
      apply Finset.sum_congr rfl
      intro x hx
      ring
    _ = (∑ x, w x * g x ^ 2) - 2 * μ * (∑ x, w x * g x) +
        μ ^ 2 * (∑ x, w x) := by
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
    _ = (∑ x, w x * g x ^ 2) - μ ^ 2 := by
      rw [hw]
      change (∑ x, w x * g x ^ 2) - 2 * μ * μ + μ ^ 2 * 1 = _
      ring

/-- The total mass of the finite Bernoulli product is one, algebraically for every bias. -/
theorem weight_mass_one (p : ℝ) : ∑ x : ι → Bool, weight p x = 1 := by
  unfold weight
  rw [← Fintype.prod_sum]
  simp [scalarWeight]

/-- Parseval implies that the variance is exactly the nonconstant spectral mass. -/
theorem variance_eq_nonempty_of_parseval (p : ℝ) (g : (ι → Bool) → ℝ)
    (hparseval : (∑ x, weight p x * g x ^ 2) = ∑ S : Finset ι, coeff p g S ^ 2) :
    (∑ x, weight p x * (g x - coeff p g ∅) ^ 2) =
      ∑ S ∈ (Finset.univ : Finset (Finset ι)).erase ∅, coeff p g S ^ 2 := by
  rw [coeff_empty, weighted_variance_eq_second_moment _ _ (weight_mass_one p), hparseval]
  rw [Finset.sum_erase_eq_sub (Finset.mem_univ ∅), coeff_empty]

/-- The same identity with a nonempty filter, convenient for degree cutoffs. -/
theorem variance_eq_nonempty_filter_of_parseval (p : ℝ) (g : (ι → Bool) → ℝ)
    (hparseval : (∑ x, weight p x * g x ^ 2) = ∑ S : Finset ι, coeff p g S ^ 2) :
    (∑ x, weight p x * (g x - coeff p g ∅) ^ 2) =
      ∑ S ∈ (Finset.univ : Finset (Finset ι)).filter (fun S => S ≠ ∅), coeff p g S ^ 2 := by
  rw [Finset.filter_ne']
  exact variance_eq_nonempty_of_parseval p g hparseval

theorem variance_eq_nonempty {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (g : (ι → Bool) → ℝ) :
    (∑ x, weight p x * (g x - coeff p g ∅) ^ 2) =
      ∑ S ∈ (Finset.univ : Finset (Finset ι)).erase ∅, coeff p g S ^ 2 := by
  exact variance_eq_nonempty_of_parseval p g (parseval hp hp1 g).symm

theorem weight_nonneg {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) (x : ι → Bool) :
    0 ≤ weight p x := by
  apply Finset.prod_nonneg
  intro i hi
  unfold scalarWeight
  split_ifs <;> linarith

/-- A Boolean function has total Fourier mass at most one. -/
theorem boolean_spectral_mass_le_one {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (f : (ι → Bool) → Bool) :
    (∑ S : Finset ι, coeff p (fun x => boolReal (f x)) S ^ 2) ≤ 1 := by
  rw [parseval hp hp1]
  calc
    (∑ x, weight p x * boolReal (f x) ^ 2) ≤ ∑ x : ι → Bool, weight p x := by
      apply Finset.sum_le_sum
      intro x hx
      rw [boolReal_sq]
      exact mul_le_of_le_one_right (weight_nonneg hp.le hp1.le x) (boolReal_le_one (f x))
    _ = 1 := weight_mass_one p

end Problem313.BiasedFourier

namespace Problem313

open BiasedFourier

@[simp] theorem fourier_weight_eq_graphWeight {n : ℕ} (p : ℝ) (x : GraphConfig n) :
    BiasedFourier.weight p x = graphWeight p x := rfl

@[simp] theorem fourier_coeff_empty_eq_graphMean {n : ℕ} (p : ℝ)
    (f : GraphConfig n → Bool) :
    coeff p (fun x => boolReal (f x)) ∅ = graphMean p f := by
  rw [coeff_empty]
  unfold graphMean
  apply Finset.sum_congr (by ext; simp)
  intro x hx
  rw [fourier_weight_eq_graphWeight]

theorem graph_second_moment_eq_mean {n : ℕ} (p : ℝ) (f : GraphConfig n → Bool) :
    (∑ x, BiasedFourier.weight p x * boolReal (f x) ^ 2) = graphMean p f := by
  apply Finset.sum_congr rfl
  intro x hx
  simp only [fourier_weight_eq_graphWeight]
  congr 1
  cases f x <;> norm_num [boolReal]

/-- The graph variance bridge needs only Parseval on the real-valued Boolean encoding. -/
theorem graphVariance_eq_fourier_nonempty_of_parseval {n : ℕ} (p : ℝ)
    (f : GraphConfig n → Bool)
    (hparseval : (∑ x, BiasedFourier.weight p x * boolReal (f x) ^ 2) =
      ∑ S : Finset (GraphEdge n), coeff p (fun x => boolReal (f x)) S ^ 2) :
    graphVariance p f =
      ∑ S ∈ (Finset.univ : Finset (Finset (GraphEdge n))).erase ∅,
        coeff p (fun x => boolReal (f x)) S ^ 2 := by
  rw [Finset.sum_erase_eq_sub (Finset.mem_univ ∅), ← hparseval,
    graph_second_moment_eq_mean, fourier_coeff_empty_eq_graphMean,
    graphVariance_eq_mean_mul]
  ring

theorem graphVariance_eq_fourier_nonempty {n : ℕ} {p : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (f : GraphConfig n → Bool) :
    graphVariance p f =
      ∑ S ∈ (Finset.univ : Finset (Finset (GraphEdge n))).erase ∅,
        coeff p (fun x => boolReal (f x)) S ^ 2 := by
  exact graphVariance_eq_fourier_nonempty_of_parseval p f
    (parseval hp hp1 (fun x : GraphConfig n => boolReal (f x))).symm

theorem graphVariance_eq_fourier_nonempty_filter {n : ℕ} {p : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (f : GraphConfig n → Bool) :
    graphVariance p f =
      ∑ S ∈ (Finset.univ : Finset (Finset (GraphEdge n))).filter (fun S => S ≠ ∅),
        coeff p (fun x => boolReal (f x)) S ^ 2 := by
  rw [Finset.filter_ne']
  exact graphVariance_eq_fourier_nonempty hp hp1 f

theorem graph_fourier_mass_eq_mean {n : ℕ} {p : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (f : GraphConfig n → Bool) :
    (∑ S : Finset (GraphEdge n), coeff p (fun x => boolReal (f x)) S ^ 2) =
      graphMean p f := by
  rw [parseval hp hp1]
  exact graph_second_moment_eq_mean p f

/-- The variance identity as a sum over nonempty Fourier supports. -/
theorem graphVariance_eq_fourier_sum_nonempty {n : ℕ} {p : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (f : GraphConfig n → Bool) :
    graphVariance p f =
      ∑ S : Finset (GraphEdge n) with S.Nonempty,
        coeff p (fun x => boolReal (f x)) S ^ 2 := by
  simpa only [Finset.nonempty_iff_ne_empty] using
    graphVariance_eq_fourier_nonempty_filter hp hp1 f

end Problem313

end

end OAI
