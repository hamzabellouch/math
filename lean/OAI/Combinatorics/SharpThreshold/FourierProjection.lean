import OAI.Combinatorics.SharpThreshold.FourierOrthogonality
import OAI.Combinatorics.SharpThreshold.ProjectionIdentities
import OAI.Combinatorics.SharpThreshold.LowDegreeL4
import OAI.Combinatorics.SharpThreshold.ProjectionNorm

namespace OAI

universe u

noncomputable section

namespace Problem313.BiasedFourier

open scoped BigOperators Classical

variable {ι : Type u} [Fintype ι]

/-- The projection onto the specified finite collection of Fourier characters. -/
def project (p : ℝ) (L : Finset (Finset ι))
    (g : (ι → Bool) → ℝ) (x : ι → Bool) : ℝ :=
  ∑ S ∈ L, coeff p g S * char p S x

/-- Pairing a function with its projection gives its selected Fourier energy. -/
theorem project_inner (p : ℝ) (L : Finset (Finset ι)) (g : (ι → Bool) → ℝ) :
    (∑ x, weight p x * g x * project p L g x) =
      ∑ S ∈ L, (coeff p g S) ^ 2 := by
  classical
  unfold project
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro S hS
  calc
    (∑ x, weight p x * g x * (coeff p g S * char p S x)) =
        coeff p g S * (∑ x, weight p x * g x * char p S x) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x hx
      ring
    _ = (coeff p g S) ^ 2 := by
      change coeff p g S * coeff p g S = (coeff p g S) ^ 2
      ring

/-- The squared norm of a Fourier projection is its selected Fourier energy. -/
theorem project_second_moment {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (L : Finset (Finset ι)) (g : (ι → Bool) → ℝ) :
    (∑ x, weight p x * (project p L g x) ^ 2) =
      ∑ S ∈ L, (coeff p g S) ^ 2 := by
  classical
  simpa only [project, WeightedProjection.synthesis] using
    WeightedProjection.second_moment_synthesis (weight p) (char p)
      (char_inner_product hp hp1) L (coeff p g)

/-- The defining orthogonality identity needed by the projection/Hölder estimate. -/
theorem project_inner_eq_second_moment {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (L : Finset (Finset ι)) (g : (ι → Bool) → ℝ) :
    (∑ x, weight p x * g x * project p L g x) =
      ∑ x, weight p x * (project p L g x) ^ 2 := by
  rw [project_inner, project_second_moment hp hp1]

/-- Specialization of inverse-noise hypercontractivity to the canonical Fourier
projection.  The hypothesis is precisely the coefficient-form noise estimate. -/
theorem project_fourth_moment_of_noise (p rho k : ℝ)
    (hrho : 0 < rho) (hrho1 : rho ≤ 1)
    (hnoise : ∀ a : Finset ι → ℝ,
      (∑ x, weight p x *
        (∑ S, rho ^ S.card * a S * char p S x) ^ 4) ≤
          (∑ S, (a S) ^ 2) ^ 2)
    (L : Finset (Finset ι)) (g : (ι → Bool) → ℝ)
    (hdegree : ∀ S ∈ L, (S.card : ℝ) ≤ k) :
    (∑ x, weight p x * (project p L g x) ^ 4) ≤
      rho ^ (-4 * k) * (∑ S ∈ L, (coeff p g S) ^ 2) ^ 2 := by
  classical
  let c : Finset ι → ℝ := fun S => if S ∈ L then coeff p g S else 0
  have hdegree' : ∀ S, c S ≠ 0 → (S.card : ℝ) ≤ k := by
    intro S hc
    by_cases hS : S ∈ L
    · exact hdegree S hS
    · simp [c, hS] at hc
  have hnoise' : ∀ a : Finset ι → ℝ,
      (∑ x, weight p x *
        (∑ S, rho ^ (S.card : ℝ) * a S * char p S x) ^ 4) ≤
          (∑ S, (a S) ^ 2) ^ 2 := by
    intro a
    simpa only [Real.rpow_natCast] using hnoise a
  have hbound := Problem313.lowDegree_fourth_of_noise Finset.card (char p)
    (weight p) rho k hrho hrho1 hnoise' c hdegree'
  have hsynth (x : ι → Bool) : (∑ S, c S * char p S x) = project p L g x := by
    simp [c, project, ite_mul, Finset.sum_ite_mem]
  have henergy : (∑ S, (c S) ^ 2) = ∑ S ∈ L, (coeff p g S) ^ 2 := by
    simp [c, ite_pow, Finset.sum_ite_mem]
  simpa only [hsynth, henergy] using hbound

/-- The concrete Fourier projection estimate for ternary-valued functions,
including Boolean coordinate differences. -/
theorem project_energy_le_of_noise {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (rho k : ℝ) (hrho : 0 < rho) (hrho1 : rho ≤ 1)
    (hnoise : ∀ a : Finset ι → ℝ,
      (∑ x, weight p x *
        (∑ S, rho ^ S.card * a S * char p S x) ^ 4) ≤
          (∑ S, (a S) ^ 2) ^ 2)
    (L : Finset (Finset ι)) (g : (ι → Bool) → ℝ)
    (hg : ∀ x, g x = -1 ∨ g x = 0 ∨ g x = 1)
    (hdegree : ∀ S ∈ L, (S.card : ℝ) ≤ k) :
    (∑ S ∈ L, (coeff p g S) ^ 2) ≤
      rho ^ (-2 * k) *
        (∑ x, if g x ≠ 0 then weight p x else 0) ^ (3 / 2 : ℝ) := by
  have hw (x : ι → Bool) : 0 ≤ weight p x := by
    unfold weight
    apply Finset.prod_nonneg
    intro i hi
    unfold scalarWeight
    split_ifs <;> linarith
  have hfour := project_fourth_moment_of_noise p rho k hrho hrho1 hnoise L g hdegree
  have hbound := Problem313.weighted_projection_noise_bound (weight p) g (project p L g)
    hw hg rho k hrho.le (project_inner_eq_second_moment hp hp1 L g)
    (by simpa only [project_second_moment hp hp1] using hfour)
  simpa only [project_second_moment hp hp1] using hbound

end Problem313.BiasedFourier

end

end OAI
