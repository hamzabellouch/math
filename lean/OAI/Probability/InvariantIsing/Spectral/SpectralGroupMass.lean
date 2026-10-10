import OAI.Probability.InvariantIsing.Spectral.SpectralProjectionMass

namespace OAI

/-! The changed coordinates in an eigenspace carry precisely their fraction
of its Haar-averaged squared spin norm. -/

noncomputable section
open MeasureTheory IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

lemma sum_changed_group_mass_le {ι A : Type*} [Fintype ι] [Fintype A]
    [DecidableEq ι] [DecidableEq A] (label : ι → A) (changed : Finset ι)
    (mass : A → ℝ) (hmass : ∀ a, 0 ≤ mass a) (r : ℝ)
    (hcount : ∀ a, ((changed.filter fun i => label i = a).card : ℝ) ≤
      r * ((Finset.univ.filter fun i => label i = a).card : ℝ)) :
    ∑ i ∈ changed, mass (label i) ≤ r * ∑ i, mass (label i) := by
  have hchanged := Finset.sum_fiberwise' changed label mass
  have hall := Finset.sum_fiberwise' Finset.univ label mass
  rw [← hchanged, ← hall, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro a _
  simpa only [Finset.sum_const, nsmul_eq_mul, mul_assoc] using
    mul_le_mul_of_nonneg_right (hcount a) (hmass a)

lemma abs_weighted_spectral_change_le {ι A : Type*} [Fintype ι] [Fintype A]
    [DecidableEq ι] [DecidableEq A] (label : ι → A) (changed : Finset ι)
    (mass : A → ℝ) (hmass : ∀ a, 0 ≤ mass a) (delta : ι → ℝ)
    (hzero : ∀ i, i ∉ changed → delta i = 0)
    (L r : ℝ) (hL : 0 ≤ L) (hdelta : ∀ i, |delta i| ≤ L)
    (hcount : ∀ a, ((changed.filter fun i => label i = a).card : ℝ) ≤
      r * ((Finset.univ.filter fun i => label i = a).card : ℝ)) :
    |∑ i, delta i * mass (label i)| ≤ L * r * ∑ i, mass (label i) := by
  have he : (∑ i, delta i * mass (label i)) =
      ∑ i ∈ changed, delta i * mass (label i) := by
    symm
    exact Finset.sum_subset (Finset.subset_univ changed) (fun i _ hi => by rw [hzero i hi, zero_mul])
  rw [he]
  calc
    _ ≤ ∑ i ∈ changed, |delta i * mass (label i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ changed, L * mass (label i) := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul, abs_of_nonneg (hmass _)]
      exact mul_le_mul_of_nonneg_right (hdelta i) (hmass _)
    _ = L * ∑ i ∈ changed, mass (label i) := (Finset.mul_sum _ _ _).symm
    _ ≤ L * (r * ∑ i, mass (label i)) :=
      mul_le_mul_of_nonneg_left (sum_changed_group_mass_le label changed mass hmass r hcount) hL
    _ = _ := by ring

end InvariantIsing

end

end OAI
