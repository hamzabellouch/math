import OAI.GroupTheory.PolycyclicRecognition.Geometry.WeightedBoxVolume

namespace OAI

/-! # All-word intervals fit in a maximizing box

The normalized coordinate bound controls the whole Minkowski sum of the
weighted word intervals, uniformly over every letter weighting and scale.
-/

noncomputable section

namespace PolycyclicRecognition

open scoped BigOperators

variable {I : Type*} [Fintype I] {n : ℕ}

/-- The sum of all weighted intervals from the fixed vector list. -/
def weightedZonotope (v : I → Fin n → ℝ) (w : I → ℝ) (r R : ℝ) : Set (Fin n → ℝ) :=
  {x | ∃ t : I → ℝ, (∀ i, |t i| ≤ R) ∧
    x = ∑ i, t i • (Real.exp (r * w i) • v i)}

/-- The entire all-word interval sum is contained in a fixed enlargement of
any maximizing scaled basis box. -/
theorem exists_uniform_zonotope_box_bound (v : I → Fin n → ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (w : I → ℝ) (b : Fin n → I),
      IsMaximizingColumnBasis v w b → ∀ (r R : ℝ), 0 ≤ r → 0 ≤ R →
        weightedZonotope v w r R ⊆ weightedCoordinateBox v w b r (C * R) := by
  obtain ⟨C, hC, hbound⟩ := exists_uniform_normalized_coordinate_bound v
  refine ⟨(Fintype.card I : ℝ) * C, mul_nonneg (Nat.cast_nonneg _) hC, ?_⟩
  intro w b hb r R hr hR x hx
  obtain ⟨t, ht, rfl⟩ := hx
  let q : Fin n → ℝ := fun j => ∑ y,
    t y * (columnCoordinates v b y j * Real.exp (r * (w y - w (b j))))
  have hq (j : Fin n) : |q j| ≤ ((Fintype.card I : ℝ) * C) * R := by
    calc
      |q j| ≤ ∑ y, |t y *
          (columnCoordinates v b y j * Real.exp (r * (w y - w (b j))))| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _y : I, R * C := Finset.sum_le_sum (fun y _ => by
        rw [abs_mul]
        exact mul_le_mul (ht y) (hbound w b hb y j r hr)
          (abs_nonneg _) hR)
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
  refine ⟨q, ⟨fun j => (abs_le.mp (hq j)).1, fun j => (abs_le.mp (hq j)).2⟩, ?_⟩
  ext k
  change (∑ j, scaledColumnMatrix v w b r k j * q j) = _
  simp only [q, scaledColumnMatrix, Finset.mul_sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  have h := scaled_columnCoordinates_repr v w b hb.1 y r k
  calc
    _ = t y * ∑ j, (columnCoordinates v b y j * Real.exp (r * (w y - w (b j)))) *
        (Real.exp (r * w (b j)) * v (b j) k) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = t y * (Real.exp (r * w y) * v y k) := by rw [h]

/-- Conversely every selected box lies in a fixed enlargement of the
all-word interval sum. This direction does not need maximality. -/
theorem weightedCoordinateBox_subset_zonotope (v : I → Fin n → ℝ) (w : I → ℝ)
    (b : Fin n → I) (r R : ℝ) (hR : 0 ≤ R) :
    weightedCoordinateBox v w b r R ⊆ weightedZonotope v w r ((n : ℝ) * R) := by
  classical
  rintro x ⟨q, hq, rfl⟩
  let t : I → ℝ := fun y => ∑ j : Fin n, if b j = y then q j else 0
  refine ⟨t, ?_, ?_⟩
  · intro y
    calc
      |t y| ≤ ∑ j : Fin n, |if b j = y then q j else 0| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j : Fin n, R := Finset.sum_le_sum (fun j _ => by
        split_ifs
        · exact abs_le.mpr ⟨hq.1 j, hq.2 j⟩
        · simpa only [abs_zero] using hR)
      _ = _ := by simp
  · ext k
    change (∑ j, scaledColumnMatrix v w b r k j * q j) = _
    simp only [t, scaledColumnMatrix, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    simp only [ite_mul, zero_mul]
    simp [eq_comm, mul_comm, mul_left_comm]

end PolycyclicRecognition

end

end OAI
