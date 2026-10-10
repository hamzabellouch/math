import OAI.Geometry.RCD.Heat.ActualHeatGrams
import OAI.Geometry.RCD.Coordinates.MatrixNormConversion

namespace OAI

/-!
# Relative error of actual heat Gram matrices

After normalizing the coordinate columns, local Gram error and missing
heat mass control the operator error. The estimates use the actual
carré du champ and the same kernel as the heat construction.
-/

open Set MeasureTheory
open scoped InnerProductSpace NNReal

noncomputable section

namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

/-- Weighted first-order splitting errors bound the Gram operator relative
to the mass of the weight. No normalization of the weight is assumed. -/
theorem weightedGram_sub_mass_id_norm_le {n : ℕ}
    (u : Fin n → SobolevSpace μ hQ) {w : X → ℝ}
    (hw : AEStronglyMeasurable w μ) {C : ℝ≥0}
    (hb : ∀ᵐ x ∂μ, ‖w x‖ ≤ (C : ℝ)) (hiw : Integrable w μ)
    (hpos : ∀ᵐ x ∂μ, 0 ≤ w x) {epsilon : ℝ} (heps : 0 ≤ epsilon)
    (herr : ∀ i j : Fin n, ∫ x, w x *
      |localGamma μ hQ (u i) (u j) x - (if i = j then 1 else 0)| ∂μ ≤ epsilon) :
    ‖sobolevGram μ hQ (sobolevColumnMap μ hQ u) hw hb -
      (∫ x, w x ∂μ) • ContinuousLinearMap.id ℝ (Euclidean n)‖ ≤ (n : ℝ) ^ 2 * epsilon := by
  apply euclidean_operator_norm_le_of_entries _ heps
  intro i j
  let d : ℝ := if j = i then 1 else 0
  have hΓ : Integrable (fun x => w x * localGamma μ hQ (u j) (u i) x) μ :=
    (localGamma_memL1 μ hQ (u j) (u i)).bdd_mul hw hb
  have he : (sobolevGram μ hQ (sobolevColumnMap μ hQ u) hw hb
      (EuclideanSpace.single j 1)) i =
      ∫ x, w x * localGamma μ hQ (u j) (u i) x ∂μ := by
    have he' := sobolevGram_inner μ hQ (sobolevColumnMap μ hQ u) hw hb
      (EuclideanSpace.single j 1) (EuclideanSpace.single i 1)
    simpa only [EuclideanSpace.inner_single_right, conj_trivial, one_mul,
      sobolevColumnMap_single, weightedGamma] using he'
  have heq : (∫ x, w x * localGamma μ hQ (u j) (u i) x ∂μ) -
      (∫ x, w x ∂μ) * d = ∫ x, w x * (localGamma μ hQ (u j) (u i) x - d) ∂μ := by
    simp only [mul_sub, integral_sub hΓ (hiw.mul_const d), integral_mul_const]
  have habs : (∫ x, |w x * (localGamma μ hQ (u j) (u i) x - d)| ∂μ) =
      ∫ x, w x * |localGamma μ hQ (u j) (u i) x - d| ∂μ := by
    apply integral_congr_ae
    filter_upwards [hpos] with x hx
    rw [abs_mul, abs_of_nonneg hx]
  have hbound : |(∫ x, w x * localGamma μ hQ (u j) (u i) x ∂μ) -
      (∫ x, w x ∂μ) * d| ≤ epsilon := by
    rw [heq]
    exact (abs_integral_le_integral_abs.trans_eq habs).trans (herr j i)
  simpa only [sub_apply, smul_apply, ContinuousLinearMap.id_apply,
    PiLp.sub_apply, PiLp.smul_apply, PiLp.single_apply, smul_eq_mul, he, d, eq_comm] using hbound

variable [μ.Regular] [IsLocallyFiniteMeasure μ]
  {p : ℝ → X → X → ℝ} (hp : IsContinuousHeatKernel μ hQ p)
  {χ : X → ℝ} (hχ : Continuous χ) (hsχ : HasCompactSupport χ)

omit [IsLocallyFiniteMeasure μ] in
/-- In normalized columns the heat Gram error is bounded by the weighted
Gram defect, the lost heat mass, and the exact scalar regularizer. -/
theorem cutoffHeatGram_sub_id_norm_le {n : ℕ}
    (u : Fin n → SobolevSpace μ hQ) (hχpos : ∀ y, 0 ≤ χ y)
    {t : ℝ} (ht : 0 < t) (x : X) (lambda : ℝ) {epsilon : ℝ} (heps : 0 ≤ epsilon)
    (herr : ∀ i j : Fin n, ∫ y, (χ y * p t x y) *
      |localGamma μ hQ (u i) (u j) y - (if i = j then 1 else 0)| ∂μ ≤ epsilon) :
    ‖cutoffHeatGram μ hQ hp hχ hsχ (sobolevColumnMap μ hQ u) ht x lambda -
      ContinuousLinearMap.id ℝ (Euclidean n)‖ ≤
      (n : ℝ) ^ 2 * epsilon + |(∫ y, χ y * p t x y ∂μ) - 1| + |lambda * t| := by
  let w := fun y => χ y * p t x y
  let m := ∫ y, w y ∂μ
  let I := ContinuousLinearMap.id ℝ (Euclidean n)
  let hw : AEStronglyMeasurable w μ :=
    (hχ.mul (hp.continuous_right t ht x)).aestronglyMeasurable
  let hb : ∀ᵐ y ∂μ, ‖w y‖ ≤ (cutoffHeatWeightBound μ hQ hp hχ hsχ ht x : ℝ) :=
    Filter.Eventually.of_forall (cutoffHeatWeight_le μ hQ hp hχ hsχ ht x)
  let G := sobolevGram μ hQ (sobolevColumnMap μ hQ u) hw hb
  have hiw : Integrable w μ :=
    (hχ.mul (hp.continuous_right t ht x)).integrable_of_hasCompactSupport hsχ.mul_right
  have herror : ‖G - m • I‖ ≤ (n : ℝ) ^ 2 * epsilon :=
    weightedGram_sub_mass_id_norm_le μ hQ u hw hb hiw
      (Filter.Eventually.of_forall fun y => mul_nonneg (hχpos y) (hp.nonneg t ht x y)) heps herr
  have hid : ‖I‖ ≤ 1 := ContinuousLinearMap.norm_id_le
  have hmi : ‖(m - 1) • I‖ ≤ |m - 1| := by
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_of_le_one_right (abs_nonneg _) hid
  have hli : ‖(lambda * t) • I‖ ≤ |lambda * t| := by
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_of_le_one_right (abs_nonneg _) hid
  have heq : cutoffHeatGram μ hQ hp hχ hsχ (sobolevColumnMap μ hQ u) ht x lambda - I =
      (G - m • I) + (m - 1) • I + (lambda * t) • I := by
    change G + (lambda * t) • I - I = _
    module
  rw [heq]
  exact (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans
    (add_le_add herror hmi)) hli)

omit [IsLocallyFiniteMeasure μ] in
/-- The scalar regularizer transforms into `A* A`. This identity keeps
the conjugated original heat matrix distinct from a freshly regularized
Gram matrix of the transformed columns. -/
theorem cutoffHeatGram_conjugate {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E]
    (U : E →L[ℝ] SobolevSpace μ hQ) (A : E →L[ℝ] E)
    {t : ℝ} (ht : 0 < t) (x : X) (lambda : ℝ) :
    A.adjoint.comp ((cutoffHeatGram μ hQ hp hχ hsχ U ht x lambda).comp A) =
      sobolevGram μ hQ (U.comp A)
        ((hχ.mul (hp.continuous_right t ht x)).aestronglyMeasurable)
        (Filter.Eventually.of_forall (cutoffHeatWeight_le μ hQ hp hχ hsχ ht x)) +
      (lambda * t) • A.adjoint.comp A := by
  rw [sobolevGram_comp]
  ext v
  simp only [cutoffHeatGram, regularizedSobolevGram, ContinuousLinearMap.comp_apply,
    add_apply, smul_apply, ContinuousLinearMap.id_apply, map_add, map_smul]

omit [BorelSpace X] [ProperSpace X] [μ.Regular] [IsLocallyFiniteMeasure μ] in
/-- Reconstruct a finite coordinate column from its values on the
Euclidean basis. -/
theorem sobolevColumnMap_basis_values {n : ℕ}
    (U : Euclidean n →L[ℝ] SobolevSpace μ hQ) :
    sobolevColumnMap μ hQ (fun i => U (EuclideanSpace.single i 1)) = U := by
  ext v
  rw [sobolevColumnMap_apply]
  simp only [← map_smul, ← map_sum]
  congr 1
  simpa only [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply] using
    (EuclideanSpace.basisFun (Fin n) ℝ).sum_repr v

omit [IsLocallyFiniteMeasure μ] in
/-- Relative comparison in an arbitrary normalized frame. The cost of
the regularizer is the squared norm of that frame, as required at small scales. -/
theorem cutoffHeatGram_conjugated_sub_id_norm_le {n : ℕ}
    (U : Euclidean n →L[ℝ] SobolevSpace μ hQ) (A : Euclidean n →L[ℝ] Euclidean n)
    (hχpos : ∀ y, 0 ≤ χ y) {t : ℝ} (ht : 0 < t) (x : X) (lambda : ℝ)
    {epsilon : ℝ} (heps : 0 ≤ epsilon)
    (herr : ∀ i j : Fin n, ∫ y, (χ y * p t x y) *
      |localGamma μ hQ (U (A (EuclideanSpace.single i 1)))
        (U (A (EuclideanSpace.single j 1))) y - (if i = j then 1 else 0)| ∂μ ≤ epsilon) :
    ‖A.adjoint.comp ((cutoffHeatGram μ hQ hp hχ hsχ U ht x lambda).comp A) -
      ContinuousLinearMap.id ℝ (Euclidean n)‖ ≤
      (n : ℝ) ^ 2 * epsilon + |(∫ y, χ y * p t x y ∂μ) - 1| +
        |lambda * t| * ‖A‖ ^ 2 := by
  let w := fun y => χ y * p t x y
  let m := ∫ y, w y ∂μ
  let I := ContinuousLinearMap.id ℝ (Euclidean n)
  let hw : AEStronglyMeasurable w μ :=
    (hχ.mul (hp.continuous_right t ht x)).aestronglyMeasurable
  let hb : ∀ᵐ y ∂μ, ‖w y‖ ≤ (cutoffHeatWeightBound μ hQ hp hχ hsχ ht x : ℝ) :=
    Filter.Eventually.of_forall (cutoffHeatWeight_le μ hQ hp hχ hsχ ht x)
  let G := sobolevGram μ hQ (U.comp A) hw hb
  have hiw : Integrable w μ :=
    (hχ.mul (hp.continuous_right t ht x)).integrable_of_hasCompactSupport hsχ.mul_right
  have he := weightedGram_sub_mass_id_norm_le μ hQ
    (fun i => (U.comp A) (EuclideanSpace.single i 1)) hw hb hiw
    (Filter.Eventually.of_forall fun y => mul_nonneg (hχpos y) (hp.nonneg t ht x y)) heps herr
  rw [sobolevColumnMap_basis_values] at he
  have hid : ‖I‖ ≤ 1 := ContinuousLinearMap.norm_id_le
  have hmi : ‖(m - 1) • I‖ ≤ |m - 1| := by
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_of_le_one_right (abs_nonneg _) hid
  have hAA : ‖A.adjoint.comp A‖ ≤ ‖A‖ ^ 2 := by
    rw [ContinuousLinearMap.norm_adjoint_comp_self]
    exact le_of_eq (by ring)
  have hreg : ‖(lambda * t) • A.adjoint.comp A‖ ≤ |lambda * t| * ‖A‖ ^ 2 := by
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left hAA (abs_nonneg _)
  rw [cutoffHeatGram_conjugate]
  change ‖G + (lambda * t) • A.adjoint.comp A - I‖ ≤ _
  have heq : G + (lambda * t) • A.adjoint.comp A - I =
      (G - m • I) + (m - 1) • I + (lambda * t) • A.adjoint.comp A := by module
  rw [heq]
  exact (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans
    (add_le_add he hmi)) hreg)

end RegularPointCoordinates

end

end OAI
