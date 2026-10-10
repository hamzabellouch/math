import OAI.Geometry.RCD.Harmonic.GramDirectionalError
import OAI.Geometry.RCD.Coordinates.NormalizedLocalL2

namespace OAI

/-! # From finite row errors to every covector in the same frame -/

open Set MeasureTheory
open scoped BigOperators ENNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

/-- The energy of a finite coordinate combination is bounded by the sum
of the row energies. No pointwise bound on the row errors is needed. -/
theorem localGamma_column_le_diagonal_sum {n : ℕ}
    (u : Fin n → SobolevSpace μ hQ) (b : Euclidean n) :
    ∀ᵐ x ∂μ, localGamma μ hQ (sobolevColumnMap μ hQ u b) (sobolevColumnMap μ hQ u b) x ≤
      (n : ℝ) * ‖b‖ ^ 2 * ∑ j, localGamma μ hQ (u j) (u j) x := by
  have hdiag : ∀ᵐ x ∂μ, ∀ i, localGamma μ hQ (u i) (u i) x =
      (SobolevSpace.minimalSlope μ hQ (u i) x) ^ 2 :=
    ae_all_iff.mpr fun i => localGamma_self μ hQ (u i)
  have hcross : ∀ᵐ x ∂μ, ∀ i j, |localGamma μ hQ (u i) (u j) x| ≤
      (localGamma μ hQ (u i) (u i) x + localGamma μ hQ (u j) (u j) x) / 2 := by
    have hb : ∀ᵐ x ∂μ, ∀ i j, |localGamma μ hQ (u i) (u j) x| ≤
        SobolevSpace.minimalSlope μ hQ (u i) x * SobolevSpace.minimalSlope μ hQ (u j) x :=
      ae_all_iff.mpr fun i => ae_all_iff.mpr fun j => localGamma_abs_le μ hQ (u i) (u j)
    filter_upwards [hb, hdiag] with x hx hd
    intro i j
    rw [hd i, hd j]
    nlinarith only [hx i j, sq_nonneg (SobolevSpace.minimalSlope μ hQ (u i) x -
      SobolevSpace.minimalSlope μ hQ (u j) x)]
  filter_upwards [hdiag, hcross, localGamma_column_pair μ hQ u b b] with x hd hc he
  rw [he]
  have hterm (i j : Fin n) : (b i * b j) * localGamma μ hQ (u i) (u j) x ≤
      ‖b‖ ^ 2 * ((localGamma μ hQ (u i) (u i) x + localGamma μ hQ (u j) (u j) x) / 2) := by
    have hi : |b i| ≤ ‖b‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le b i
    have hj : |b j| ≤ ‖b‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le b j
    have hp : |b i * b j| ≤ ‖b‖ ^ 2 := by
      rw [abs_mul, pow_two]
      exact mul_le_mul hi hj (abs_nonneg _) (norm_nonneg b)
    calc
      _ ≤ |(b i * b j) * localGamma μ hQ (u i) (u j) x| := le_abs_self _
      _ = |b i * b j| * |localGamma μ hQ (u i) (u j) x| := abs_mul _ _
      _ ≤ _ := mul_le_mul hp (hc i j) (abs_nonneg _) (sq_nonneg _)
  calc
    _ ≤ ∑ i : Fin n, ∑ j : Fin n,
        ‖b‖ ^ 2 * ((localGamma μ hQ (u i) (u i) x + localGamma μ hQ (u j) (u j) x) / 2) :=
      Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hterm i j
    _ = _ := by
      simp only [add_div, mul_add, Finset.sum_add_distrib, ← Finset.mul_sum,
        Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        ← Finset.sum_div]
      ring

/-- A common bound for the integrated row errors controls every
covector error in the same coordinate frame. -/
theorem column_energy_bound {n : ℕ} (u : Fin n → SobolevSpace μ hQ) (Ω : Set X)
    {E : ℝ} (hE : ∀ j, (∫ x in Ω, localGamma μ hQ (u j) (u j) x ∂μ) ≤ E)
    (b : Euclidean n) :
    (∫ x in Ω, localGamma μ hQ (sobolevColumnMap μ hQ u b) (sobolevColumnMap μ hQ u b) x ∂μ) ≤
      (n : ℝ) ^ 2 * E * ‖b‖ ^ 2 := by
  have hsum := integral_mono_ae (μ := μ.restrict Ω) (localGamma_memL1 μ hQ _ _).integrableOn
    ((integrable_finsetSum Finset.univ (fun j _ =>
      (localGamma_memL1 μ hQ (u j) (u j)).integrableOn)).const_mul ((n : ℝ) * ‖b‖ ^ 2))
    (ae_restrict_of_ae (localGamma_column_le_diagonal_sum μ hQ u b))
  rw [integral_const_mul, integral_finsetSum Finset.univ (fun j _ =>
    (localGamma_memL1 μ hQ (u j) (u j)).integrableOn)] at hsum
  have hh := mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j (_ : j ∈ (Finset.univ : Finset (Fin n))) => hE j)
    (show 0 ≤ (n : ℝ) * ‖b‖ ^ 2 by positivity)
  apply hsum.trans
  calc
    _ ≤ (n : ℝ) * ‖b‖ ^ 2 * ((n : ℝ) * E) := by simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using hh
    _ = _ := by ring

/-- The same estimate works for averaged energy, without requiring the
averaging measure to have a strictly positive volume. -/
theorem weighted_column_energy_bound {n : ℕ} (u : Fin n → SobolevSpace μ hQ)
    (Ω : Set X) {w E : ℝ} (hw : 0 ≤ w)
    (hE : ∀ j, w * (∫ x in Ω, localGamma μ hQ (u j) (u j) x ∂μ) ≤ E)
    (b : Euclidean n) :
    w * (∫ x in Ω, localGamma μ hQ (sobolevColumnMap μ hQ u b) (sobolevColumnMap μ hQ u b) x ∂μ) ≤
      (n : ℝ) ^ 2 * E * ‖b‖ ^ 2 := by
  have hi := integral_mono_ae (μ := μ.restrict Ω) (localGamma_memL1 μ hQ _ _).integrableOn
    ((integrable_finsetSum Finset.univ (fun j _ =>
      (localGamma_memL1 μ hQ (u j) (u j)).integrableOn)).const_mul ((n : ℝ) * ‖b‖ ^ 2))
    (ae_restrict_of_ae (localGamma_column_le_diagonal_sum μ hQ u b))
  rw [integral_const_mul, integral_finsetSum Finset.univ (fun j _ =>
    (localGamma_memL1 μ hQ (u j) (u j)).integrableOn)] at hi
  have hh := mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j (_ : j ∈ (Finset.univ : Finset (Fin n))) => hE j)
    (show 0 ≤ (n : ℝ) * ‖b‖ ^ 2 by positivity)
  apply (mul_le_mul_of_nonneg_left hi hw).trans
  calc
    _ = (n : ℝ) * ‖b‖ ^ 2 * ∑ j, w * (∫ x in Ω, localGamma μ hQ (u j) (u j) x ∂μ) := by rw [← Finset.mul_sum]; ring
    _ ≤ (n : ℝ) * ‖b‖ ^ 2 * ((n : ℝ) * E) := by simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using hh
    _ = _ := by ring

omit [BorelSpace X] [ProperSpace X] in
/-- Finite rowwise value bounds also control the normalized local L2
value of every coordinate combination. -/
theorem normalized_column_norm_le {n : ℕ} (u : Fin n → SobolevSpace μ hQ)
    (Ω : Set X) (hfin : μ Ω ≠ ∞) {D : ℝ}
    (hrow : ∀ j, ‖normalizeLocalL2 μ Ω hfin (SobolevSpace.restrictLp μ hQ Ω (u j))‖ ≤ D)
    (b : Euclidean n) :
    ‖normalizeLocalL2 μ Ω hfin (SobolevSpace.restrictLp μ hQ Ω (sobolevColumnMap μ hQ u b))‖ ≤
      (n : ℝ) * D * ‖b‖ := by
  have hid : normalizeLocalL2 μ Ω hfin (SobolevSpace.restrictLp μ hQ Ω (sobolevColumnMap μ hQ u b)) =
      ∑ j, b j • normalizeLocalL2 μ Ω hfin (SobolevSpace.restrictLp μ hQ Ω (u j)) := by
    simp only [sobolevColumnMap_apply, map_sum, map_smul, normalizeLocalL2, Finset.smul_sum]
    exact Finset.sum_congr rfl fun j _ => smul_comm _ _ _
  rw [hid]
  calc
    _ ≤ ∑ j, ‖b j • normalizeLocalL2 μ Ω hfin (SobolevSpace.restrictLp μ hQ Ω (u j))‖ := norm_sum_le _ _
    _ ≤ ∑ _j : Fin n, ‖b‖ * D := by
      apply Finset.sum_le_sum
      intro j _
      rw [norm_smul]
      exact mul_le_mul (PiLp.norm_apply_le b j) (hrow j) (norm_nonneg _) (norm_nonneg b)
    _ = _ := by simp; ring

omit [BorelSpace X] [ProperSpace X] in
/-- Squared row errors remain squared after passage to every covector. -/
theorem normalized_column_sq_le {n : ℕ} (u : Fin n → SobolevSpace μ hQ)
    (Ω : Set X) (hfin : μ Ω ≠ ∞) {E : ℝ} (hE : 0 ≤ E)
    (hrow : ∀ j, ‖normalizeLocalL2 μ Ω hfin (SobolevSpace.restrictLp μ hQ Ω (u j))‖ ^ 2 ≤ E)
    (b : Euclidean n) :
    ‖normalizeLocalL2 μ Ω hfin (SobolevSpace.restrictLp μ hQ Ω (sobolevColumnMap μ hQ u b))‖ ^ 2 ≤
      (n : ℝ) ^ 2 * E * ‖b‖ ^ 2 := by
  have hnorm := normalized_column_norm_le μ hQ u Ω hfin
    (fun j => by simpa only [Real.sqrt_sq (norm_nonneg _)] using Real.sqrt_le_sqrt (hrow j)) b
  have hh := (sq_le_sq₀ (norm_nonneg _) (by positivity : 0 ≤ (n : ℝ) * Real.sqrt E * ‖b‖)).mpr hnorm
  simpa only [mul_pow, Real.sq_sqrt hE] using hh

end RegularPointCoordinates

end

end OAI
