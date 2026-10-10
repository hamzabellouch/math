import OAI.Combinatorics.SharpThreshold.FourierDerivative
import OAI.Combinatorics.SharpThreshold.BooleanDerivative
import OAI.Combinatorics.SharpThreshold.DirichletEnergy

namespace OAI

universe u

noncomputable section

namespace Problem313.BiasedFourier

open Finset
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

/-- The coordinate Dirichlet identity, with only the two derivative coefficient
identities isolated as hypotheses. -/
theorem coordinate_energy_of_coeff_derivative {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (g dg : (ι → Bool) → ℝ) (i : ι)
    (hzero : ∀ S, i ∈ S → coeff p dg S = 0)
    (hinsert : ∀ S, i ∉ S → coeff p g (insert i S) =
      Real.sqrt (p * (1 - p)) * coeff p dg S) :
    (∑ S : Finset ι, if i ∈ S then (coeff p g S)^2 else 0) =
      p * (1 - p) * ∑ x, weight p x * (dg x)^2 := by
  rw [Problem313.spectral_coordinate_energy i (coeff p g) (coeff p dg)
    (Real.sqrt (p * (1 - p))) hzero hinsert]
  rw [parseval hp hp1, Real.sq_sqrt (mul_nonneg hp.le (sub_nonneg.mpr hp1.le))]

/-- Summing coordinate Dirichlet identities gives degree-weighted Fourier energy. -/
theorem total_energy_of_coordinate_energy {p : ℝ}
    (g : (ι → Bool) → ℝ) (E : ι → ℝ)
    (hcoord : ∀ i, (∑ S : Finset ι, if i ∈ S then (coeff p g S)^2 else 0) =
      p * (1 - p) * E i) :
    (∑ S : Finset ι, (S.card : ℝ) * (coeff p g S)^2) =
      p * (1 - p) * ∑ i, E i := by
  rw [Problem313.sum_card_mul_eq_sum_mem]
  simp_rw [hcoord]
  rw [Finset.mul_sum]

/-- The Fourier mass on supports containing a fixed coordinate equals its
weighted squared discrete derivative. -/
theorem coordinate_dirichlet {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (g : (ι → Bool) → ℝ) (i : ι) :
    (∑ S : Finset ι, if i ∈ S then (coeff p g S)^2 else 0) =
      p * (1 - p) * ∑ x, weight p x * (delta i g x)^2 := by
  exact coordinate_energy_of_coeff_derivative hp hp1 g (delta i g) i
    (fun S hS => coeff_delta_eq_zero_of_mem hp hp1 g i S hS)
    (fun S hS => coeff_insert_eq_sqrt_mul_delta hp hp1 g i S hS)

/-- The full finite-cube Fourier Dirichlet identity for real observables. -/
theorem dirichlet {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (g : (ι → Bool) → ℝ) :
    (∑ S : Finset ι, (S.card : ℝ) * (coeff p g S)^2) =
      p * (1 - p) * ∑ i, ∑ x, weight p x * (delta i g x)^2 := by
  exact total_energy_of_coordinate_energy g _ (coordinate_dirichlet hp hp1 g)

/-- For Boolean observables, squared derivative energy is pivotal influence. -/
theorem boolean_coordinate_dirichlet {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (f : (ι → Bool) → Bool) (i : ι) :
    (∑ S : Finset ι, if i ∈ S then (coeff p (fun x => boolReal (f x)) S)^2 else 0) =
      p * (1 - p) * Reindex.influence p f i := by
  rw [coordinate_dirichlet hp hp1]
  congr 1
  simpa only [delta, weight, scalarWeight, Reindex.weight] using
    Reindex.boolean_delta_sq_moment p f i

/-- The degree-weighted Fourier mass of a Boolean function is its total pivotal
influence times the Bernoulli variance. -/
theorem boolean_dirichlet {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (f : (ι → Bool) → Bool) :
    (∑ S : Finset ι, (S.card : ℝ) * (coeff p (fun x => boolReal (f x)) S)^2) =
      p * (1 - p) * ∑ i, Reindex.influence p f i := by
  exact total_energy_of_coordinate_energy _ _ (boolean_coordinate_dirichlet hp hp1 f)

end Problem313.BiasedFourier

namespace Problem313

/-- The graph Dirichlet identity for pivotal total influence. -/
theorem graph_fourier_dirichlet {n : ℕ} {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (f : GraphConfig n → Bool) :
    (∑ S : Finset (GraphEdge n), (S.card : ℝ) *
      (BiasedFourier.coeff p (fun x => boolReal (f x)) S)^2) =
      p * (1 - p) * totalInfluence p f := by
  classical
  have hi : (∑ e : GraphEdge n, Reindex.influence p f e) = totalInfluence p f := by
    unfold totalInfluence
    apply Finset.sum_congr rfl
    intro e he
    unfold Reindex.influence edgeInfluence
    apply Finset.sum_congr (by ext; simp)
    intro x hx
    congr 1
    congr 4 <;> exact Subsingleton.elim _ _
  have h := BiasedFourier.boolean_dirichlet hp hp1 f
  rw [hi] at h
  exact h

end Problem313

end

end OAI
