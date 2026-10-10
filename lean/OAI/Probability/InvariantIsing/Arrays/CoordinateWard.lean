import OAI.Probability.InvariantIsing.Haar.PlaneRotation
import OAI.Probability.InvariantIsing.Core.Ward

namespace OAI

/-!
# The coordinate Haar Ward identity for the Ising Hamiltonian

This proves the finite-dimensional identity for the unperturbed model with an
arbitrary deterministic spin prior and magnetic field.
-/

noncomputable section

open MeasureTheory IsingPerceptron
open scoped BigOperators Matrix

namespace InvariantIsing

/-- Spectral coordinate of a rotated Ising spin. -/
def spinCoordinate {N : ℕ} (U : Orthogonal N) (σ : Spin N) (i : Fin N) : ℝ :=
  matrixRotation U (spinVector σ) i

def coordinateProduct {N : ℕ} (i j : Fin N) (U : Orthogonal N) (σ : Spin N) : ℝ :=
  spinCoordinate U σ i * spinCoordinate U σ j

def orbitHamiltonian {N : ℕ} (eig c : Fin N → ℝ) (U : Orthogonal N) (σ : Spin N) : ℝ :=
  rotatedEnergy eig (matrixRotation U) σ + fieldEnergy c σ

lemma measurable_spinCoordinate {N : ℕ} (σ : Spin N) (i : Fin N) :
    Measurable (fun U : Orthogonal N => spinCoordinate U σ i) := by
  simp only [spinCoordinate, matrixRotation_apply, spinVector_apply]
  apply Finset.measurable_sum
  intro j _
  have he : Measurable (fun U : Orthogonal N =>
      (U : Matrix (Fin N) (Fin N) ℝ) i j) :=
    (measurable_pi_apply j).comp ((measurable_pi_apply i).comp measurable_subtype_coe)
  exact he.mul_const _

lemma measurable_orbitHamiltonian {N : ℕ} (eig c : Fin N → ℝ) (σ : Spin N) :
    Measurable (fun U : Orthogonal N => orbitHamiltonian eig c U σ) := by
  exact ((Finset.measurable_sum _ fun i _ =>
    ((measurable_spinCoordinate σ i).pow_const 2).const_mul (eig i)).const_mul
      (1 / 2 : ℝ)).add_const _

lemma spinCoordinate_sq_le {N : ℕ} (U : Orthogonal N) (σ : Spin N) (i : Fin N) :
    spinCoordinate U σ i ^ 2 ≤ N := by
  rw [← rotated_spin_sq_sum (matrixRotation U) σ]
  exact Finset.single_le_sum (fun j _ => sq_nonneg _) (Finset.mem_univ i)

lemma abs_coordinateProduct_le {N : ℕ} (i j : Fin N) (U : Orthogonal N) (σ : Spin N) :
    |coordinateProduct i j U σ| ≤ N := by
  have hi := spinCoordinate_sq_le U σ i
  have hj := spinCoordinate_sq_le U σ j
  have hs : |coordinateProduct i j U σ| ^ 2 ≤ (N : ℝ) ^ 2 := by
    rw [sq_abs, coordinateProduct, mul_pow]
    simpa only [pow_two] using mul_le_mul hi hj (sq_nonneg _) (Nat.cast_nonneg _)
  exact (sq_le_sq₀ (abs_nonneg _) (Nat.cast_nonneg _)).mp hs

lemma abs_coordinateSquareDifference_le {N : ℕ} (i j : Fin N)
    (U : Orthogonal N) (σ : Spin N) :
    |spinCoordinate U σ j ^ 2 - spinCoordinate U σ i ^ 2| ≤ N := by
  have hi := spinCoordinate_sq_le U σ i
  have hj := spinCoordinate_sq_le U σ j
  exact abs_le.mpr ⟨by nlinarith [sq_nonneg (spinCoordinate U σ j)],
    by nlinarith [sq_nonneg (spinCoordinate U σ i)]⟩

lemma hasDerivAt_plane_coordinateProduct {N : ℕ} (i j : Fin N) (hij : i ≠ j)
    (U : Orthogonal N) (σ : Spin N) (t : ℝ) :
    HasDerivAt (fun s => coordinateProduct i j (planeRotation i j s * U) σ)
      (spinCoordinate (planeRotation i j t * U) σ j ^ 2 -
        spinCoordinate (planeRotation i j t * U) σ i ^ 2) t := by
  have hd := (hasDerivAt_planeRotation_coordinate i j i U (spinVector σ) t).mul
    (hasDerivAt_planeRotation_coordinate i j j U (spinVector σ) t)
  convert hd using 1
  · rfl
  · simp only [spinCoordinate, ite_true, hij, Ne.symm hij, ite_false, sub_zero, zero_sub]
    ring

lemma gibbsAverage_const_mul {S : Type*} [Fintype S] (w H A : S → ℝ) (a : ℝ) :
    gibbsAverage w H (fun σ => a * A σ) = a * gibbsAverage w H A := by
  simp only [gibbsAverage, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro σ _
  ring

/-- An exact coordinate Ward equation for every finite dimension, arbitrary
nonzero positive spin prior, and deterministic magnetic field. -/
theorem coordinate_ward_identity {N : ℕ} (i j : Fin N) (hij : i ≠ j)
    (μ : Measure (Orthogonal N)) [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant]
    {w : Spin N → ℝ} (hw : GibbsReference w) (eig c : Fin N → ℝ)
    (K : ℝ) (hK : 0 ≤ K) (heig : ∀ k, |eig k| ≤ K) :
    (∫ U,
      gibbsAverage w (orbitHamiltonian eig c U)
        (fun σ => spinCoordinate U σ j ^ 2 - spinCoordinate U σ i ^ 2) +
      (eig i - eig j) *
        (gibbsAverage w (orbitHamiltonian eig c U) (fun σ => coordinateProduct i j U σ ^ 2) -
          gibbsAverage w (orbitHamiltonian eig c U) (coordinateProduct i j U) ^ 2) ∂μ) = 0 := by
  let R := planeRotation i j
  let H := orbitHamiltonian eig c
  let A := coordinateProduct i j
  let dH : ℝ → Orthogonal N → Spin N → ℝ := fun t U σ =>
    (eig i - eig j) * coordinateProduct i j (R t * U) σ
  let dA : ℝ → Orthogonal N → Spin N → ℝ := fun t U σ =>
    spinCoordinate (R t * U) σ j ^ 2 - spinCoordinate (R t * U) σ i ^ 2
  have hR : R 0 = 1 := planeRotation_zero i j
  have hAm (σ : Spin N) : Measurable (fun U => A U σ) :=
    (measurable_spinCoordinate σ i).mul (measurable_spinCoordinate σ j)
  have hdHm (σ : Spin N) : Measurable (fun U => dH 0 U σ) := by
    simp only [dH, hR, one_mul]
    exact (hAm σ).const_mul _
  have hdAm (σ : Spin N) : Measurable (fun U => dA 0 U σ) := by
    simp only [dA, hR, one_mul]
    exact ((measurable_spinCoordinate σ j).pow_const 2).sub
      ((measurable_spinCoordinate σ i).pow_const 2)
  have hHd : ∀ U t, t ∈ Set.Ioo (-1 : ℝ) 1 → ∀ σ,
      HasDerivAt (fun s => H (R s * U) σ) (dH t U σ) t := by
    intro U t _ σ
    simpa only [H, R, orbitHamiltonian, dH, coordinateProduct, spinCoordinate,
      mul_assoc] using
      (hasDerivAt_planeRotation_energy i j U eig σ t).add_const (fieldEnergy c σ)
  have hAd : ∀ U t, t ∈ Set.Ioo (-1 : ℝ) 1 → ∀ σ,
      HasDerivAt (fun s => A (R s * U) σ) (dA t U σ) t := by
    intro U t _ σ
    exact hasDerivAt_plane_coordinateProduct i j hij U σ t
  have heigd : |eig i - eig j| ≤ 2 * K := by
    have ht := (abs_sub (eig i) (eig j)).trans (add_le_add (heig i) (heig j))
    linarith
  have hHb : ∀ U t, t ∈ Set.Ioo (-1 : ℝ) 1 → ∀ σ, |dH t U σ| ≤ 2 * K * N := by
    intro U t _ σ
    dsimp only [dH]
    rw [abs_mul]
    exact mul_le_mul heigd (abs_coordinateProduct_le i j (R t * U) σ)
      (abs_nonneg _) (by positivity)
  have hAb : ∀ U t, t ∈ Set.Ioo (-1 : ℝ) 1 → ∀ σ, |dA t U σ| ≤ N := by
    intro U t _ σ
    exact abs_coordinateSquareDifference_le i j (R t * U) σ
  have hwrd := integral_gibbs_rotation_identity μ R hR hw H A
    (measurable_orbitHamiltonian eig c) hAm dH dA hdHm hdAm hHd hAd
    (N : ℝ) (2 * K * N) (N : ℝ) (Nat.cast_nonneg _)
    (fun U σ => abs_coordinateProduct_le i j U σ) hHb hAb
  simp only [dH, dA, hR, one_mul] at hwrd
  convert hwrd using 1
  congr 1
  funext U
  have hp : (fun σ => A U σ * ((eig i - eig j) * coordinateProduct i j U σ)) =
      (fun σ => (eig i - eig j) * coordinateProduct i j U σ ^ 2) := by
    funext σ
    dsimp only [A]
    ring
  rw [hp, gibbsAverage_const_mul, gibbsAverage_const_mul]
  dsimp only [A, H]
  ring

end InvariantIsing

end

end OAI
