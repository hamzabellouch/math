import OAI.Analysis.IrrationalRotation.Product.ProductFieldRepresentation

namespace OAI

noncomputable section
open MeasureTheory Filter
namespace Invariant233.ProductModel

private abbrev S (m : ℤ) : Fiber →L[ℂ] Fiber :=
  (WeightedShift.shift m).toLinearIsometry.toContinuousLinearMap

private theorem rotationIterate_one_eq (θ : ℕ → ℝ) (x : Base) :
    rotationIterate θ 1 x = rotation θ x := by
  funext i
  change x i + (((1 : ℤ) : ℝ) * θ i : ℝ) = x i + (θ i : Circle)
  simp only [Int.cast_one, one_mul]

theorem IsCovariantFieldRepresentation.covariance_all
    {θ : ℕ → ℝ} {A : Hilbert →L[ℂ] Hilbert}
    {F : Base → Fiber →L[ℂ] Fiber} {B : ℝ}
    (h : IsCovariantFieldRepresentation θ A F B) :
    ∀ᵐ x ∂baseMeasure, ∀ m : ℤ,
      F x * S m = S m * F (rotationIterate θ m x) := by
  have hpm : S 1 * S (-1) = 1 := by
    rw [← WeightedShift.shift_add]
    norm_num [WeightedShift.shift_zero]
  have hmp : S (-1) * S 1 = 1 := by
    rw [← WeightedShift.shift_add]
    norm_num [WeightedShift.shift_zero]
  have h1 : ∀ᵐ x ∂baseMeasure, F x * S 1 = S 1 * F (rotationIterate θ 1 x) := by
    filter_upwards [h.2.2.2.2] with x hx
    rw [rotationIterate_one_eq, hx]
    simp only [← mul_assoc, hpm, one_mul]
  have hn1 : ∀ᵐ x ∂baseMeasure, F x * S (-1) = S (-1) * F (rotationIterate θ (-1) x) := by
    filter_upwards [(rotationIterate_measurePreserving θ (-1)).quasiMeasurePreserving.ae h1]
      with x hx
    have hrot : rotationIterate θ 1 (rotationIterate θ (-1) x) = x := by
      rw [← rotationIterate_add]
      norm_num
    rw [hrot] at hx
    calc
      F x * S (-1) = (S (-1) * S 1) * F x * S (-1) := by rw [hmp, one_mul]
      _ = S (-1) * (S 1 * F x) * S (-1) := by simp only [mul_assoc]
      _ = S (-1) * (F (rotationIterate θ (-1) x) * S 1) * S (-1) := by rw [← hx]
      _ = S (-1) * F (rotationIterate θ (-1) x) := by simp only [mul_assoc, hpm, mul_one]
  have hadd (m n : ℤ)
      (hm : ∀ᵐ x ∂baseMeasure, F x * S m = S m * F (rotationIterate θ m x))
      (hn : ∀ᵐ x ∂baseMeasure, F x * S n = S n * F (rotationIterate θ n x)) :
      ∀ᵐ x ∂baseMeasure, F x * S (m+n) = S (m+n) * F (rotationIterate θ (m+n) x) := by
    filter_upwards [hm, (rotationIterate_measurePreserving θ m).quasiMeasurePreserving.ae hn]
      with x hmx hnx
    have hs : S (m+n) = S m * S n := WeightedShift.shift_add m n
    rw [hs, ← mul_assoc, hmx, mul_assoc, hnx, ← mul_assoc, ← rotationIterate_add]
  apply ae_all_iff.mpr
  intro m
  induction m using Int.induction_on with
  | zero => exact Eventually.of_forall (fun x => by simp [S])
  | succ n ih => exact hadd n 1 ih h1
  | pred n ih => simpa only [sub_eq_add_neg] using hadd (-(n : ℤ)) (-1) ih hn1

theorem IsCovariantFieldRepresentation.matrix_covariance
    {θ : ℕ → ℝ} {A : Hilbert →L[ℂ] Hilbert}
    {F : Base → Fiber →L[ℂ] Fiber} {B : ℝ}
    (h : IsCovariantFieldRepresentation θ A F B) :
    ∀ m k l : ℤ, ∀ᵐ x ∂baseMeasure,
      inner ℂ ((default : HilbertBasis ℤ ℂ Fiber) k)
        (F (rotationIterate θ m x) ((default : HilbertBasis ℤ ℂ Fiber) l)) =
      inner ℂ ((default : HilbertBasis ℤ ℂ Fiber) (k+m))
        (F x ((default : HilbertBasis ℤ ℂ Fiber) (l+m))) := by
  apply FieldTraceCyclic.ae_matrix_covariance_of_commute
    (default : HilbertBasis ℤ ℂ Fiber) A F
    (fun m => DirectIntegral.shiftedPullback (S m)
      (rotationIterate θ m) (rotationIterate_measurePreserving θ m))
    (fun m => (WeightedShift.shift m).toLinearIsometry)
    (rotationIterate θ) (rotationIterate_measurePreserving θ)
  · exact FieldKoopman.shift_default_basis
  · exact h.2.2.2.1
  · intro m
    exact FieldTraceCyclic.shiftedPullback_ae _ _ _
  · intro m
    apply FieldTraceCyclic.commute_shiftedPullback_of_covariance
      A F (S m) (rotationIterate θ m) (rotationIterate_measurePreserving θ m) h.2.2.2.1
    filter_upwards [h.covariance_all] with x hx
    exact hx m

theorem signedShift_mem_factor (θ : ℕ → ℝ) (m : ℤ) :
    (S m).compLpL 2 baseMeasure ∈ factor θ := by
  let Q : ℤ → Hilbert →L[ℂ] Hilbert := fun k => (S k).compLpL 2 baseMeasure
  have hQadd (k l : ℤ) : Q (k+l) = Q k * Q l := WeightedShift.fieldShift_add k l
  have hQ0 : Q 0 = 1 := WeightedShift.fieldShift_zero
  have hQ1 : Q 1 ∈ factor θ := subset_vonNeumannGenerated _ (Or.inl rfl)
  have hQunit : Q 1 ∈ unitary (Hilbert →L[ℂ] Hilbert) := WeightedShift.fieldShift_mem_unitary 1
  have hQinv : Q 1 * Q (-1) = 1 := by rw [← hQadd]; norm_num [hQ0]
  have hQneg : Q (-1) = star (Q 1) := by
    calc
      Q (-1) = (star (Q 1) * Q 1) * Q (-1) := by
        rw [Unitary.star_mul_self_of_mem hQunit, one_mul]
      _ = star (Q 1) * (Q 1 * Q (-1)) := mul_assoc _ _ _
      _ = star (Q 1) := by rw [hQinv, mul_one]
  have hQn1 : Q (-1) ∈ factor θ := hQneg ▸ star_mem hQ1
  change Q m ∈ factor θ
  induction m using Int.induction_on with
  | zero => rw [hQ0]; exact one_mem _
  | succ n ih => rw [hQadd]; exact mul_mem ih hQ1
  | pred n ih =>
    rw [sub_eq_add_neg, hQadd]
    exact mul_mem ih hQn1

def fieldCoefficient (F : Base → Fiber →L[ℂ] Fiber) (r : ℤ) (x : Base) : ℂ :=
  inner ℂ ((default : HilbertBasis ℤ ℂ Fiber) r)
    (F x ((default : HilbertBasis ℤ ℂ Fiber) 0))

theorem IsCovariantFieldRepresentation.measurable_fieldCoefficient
    {θ : ℕ → ℝ} {A : Hilbert →L[ℂ] Hilbert}
    {F : Base → Fiber →L[ℂ] Fiber} {B : ℝ}
    (h : IsCovariantFieldRepresentation θ A F B) (r : ℤ) :
    Measurable (fieldCoefficient F r) := by
  exact ((continuous_const.inner continuous_id).comp_stronglyMeasurable
    (h.2.2.1 ((default : HilbertBasis ℤ ℂ Fiber) 0))).measurable

theorem IsCovariantFieldRepresentation.norm_fieldCoefficient_le
    {θ : ℕ → ℝ} {A : Hilbert →L[ℂ] Hilbert}
    {F : Base → Fiber →L[ℂ] Fiber} {B : ℝ}
    (h : IsCovariantFieldRepresentation θ A F B) (r : ℤ) (x : Base) :
    ‖fieldCoefficient F r x‖ ≤ B := by
  let b := (default : HilbertBasis ℤ ℂ Fiber)
  calc
    ‖fieldCoefficient F r x‖ ≤ ‖b r‖ * ‖F x (b 0)‖ := norm_inner_le_norm _ _
    _ ≤ ‖b r‖ * (‖F x‖ * ‖b 0‖) :=
      mul_le_mul_of_nonneg_left ((F x).le_opNorm _) (norm_nonneg _)
    _ = ‖F x‖ := by rw [b.orthonormal.norm_eq_one, b.orthonormal.norm_eq_one]; ring
    _ ≤ B := h.2.1 x

theorem IsCovariantFieldRepresentation.diagonal_coefficient
    {θ : ℕ → ℝ} {A : Hilbert →L[ℂ] Hilbert}
    {F : Base → Fiber →L[ℂ] Fiber} {B : ℝ}
    (h : IsCovariantFieldRepresentation θ A F B) (r k : ℤ) :
    ∀ᵐ x ∂baseMeasure,
      inner ℂ ((default : HilbertBasis ℤ ℂ Fiber) (k+r))
        (F x ((default : HilbertBasis ℤ ℂ Fiber) k)) =
          fieldCoefficient F r (rotationIterate θ k x) := by
  filter_upwards [h.matrix_covariance k r 0] with x hx
  simpa only [fieldCoefficient, zero_add, add_comm k r] using hx.symm

theorem IsCovariantFieldRepresentation.diagonalOperator_mem_factor
    {θ : ℕ → ℝ} {A : Hilbert →L[ℂ] Hilbert}
    {F : Base → Fiber →L[ℂ] Fiber} {B : ℝ}
    (h : IsCovariantFieldRepresentation θ A F B) (r : ℤ) :
    (S r).compLpL 2 baseMeasure *
      multiplier θ (fieldCoefficient F r) B h.1
        (h.measurable_fieldCoefficient r) (h.norm_fieldCoefficient_le r) ∈ factor θ := by
  apply mul_mem (signedShift_mem_factor θ r)
  apply subset_vonNeumannGenerated _
  exact Or.inr ⟨fieldCoefficient F r, B, h.1, h.measurable_fieldCoefficient r,
    h.norm_fieldCoefficient_le r, rfl⟩

theorem IsCovariantFieldRepresentation.diagonalOperator_ae
    {θ : ℕ → ℝ} {A : Hilbert →L[ℂ] Hilbert}
    {F : Base → Fiber →L[ℂ] Fiber} {B : ℝ}
    (h : IsCovariantFieldRepresentation θ A F B) (r : ℤ) (ξ : Hilbert) :
    ((S r).compLpL 2 baseMeasure *
      multiplier θ (fieldCoefficient F r) B h.1
        (h.measurable_fieldCoefficient r) (h.norm_fieldCoefficient_le r)) ξ =ᵐ[baseMeasure]
      fun x => S r (WeightedShift.diagonal
        (multiplierField θ (fieldCoefficient F r) B (h.norm_fieldCoefficient_le r) x) (ξ x)) := by
  filter_upwards [WeightedShift.fieldShift_ae r
    (multiplier θ (fieldCoefficient F r) B h.1 (h.measurable_fieldCoefficient r)
      (h.norm_fieldCoefficient_le r) ξ),
    multiplier_ae θ (fieldCoefficient F r) B h.1 (h.measurable_fieldCoefficient r)
      (h.norm_fieldCoefficient_le r) ξ] with x hs hd
  exact hs.trans (congrArg (S r) hd)

theorem IsCovariantFieldRepresentation.diagonalOperator_basis
    {θ : ℕ → ℝ} {A : Hilbert →L[ℂ] Hilbert}
    {F : Base → Fiber →L[ℂ] Fiber} {B : ℝ}
    (h : IsCovariantFieldRepresentation θ A F B) (r k : ℤ) :
    ∀ᵐ x ∂baseMeasure,
      S r (WeightedShift.diagonal
        (multiplierField θ (fieldCoefficient F r) B (h.norm_fieldCoefficient_le r) x)
          ((default : HilbertBasis ℤ ℂ Fiber) k)) =
      (inner ℂ ((default : HilbertBasis ℤ ℂ Fiber) (k+r))
        (F x ((default : HilbertBasis ℤ ℂ Fiber) k))) •
          ((default : HilbertBasis ℤ ℂ Fiber) (k+r)) := by
  let b := (default : HilbertBasis ℤ ℂ Fiber)
  have hdiag (w : WeightedShift.Weight) : WeightedShift.diagonal w (b k) = w k • b k := by
    have hb : b k = (lp.single 2 k (1 : ℂ) : Fiber) :=
      (HilbertBasis.repr_symm_single b k).symm
    rw [hb]
    ext j
    by_cases hj : j = k <;> simp [WeightedShift.diagonal_apply, lp.single_apply, hj]
  filter_upwards [h.diagonal_coefficient r k] with x hx
  rw [hdiag, map_smul]
  change _ • WeightedShift.shift r (b k) = _
  rw [FieldKoopman.shift_default_basis]
  change fieldCoefficient F r (rotationIterate θ k x) • b (k+r) = _
  rw [← hx]

end Invariant233.ProductModel

end

end OAI
