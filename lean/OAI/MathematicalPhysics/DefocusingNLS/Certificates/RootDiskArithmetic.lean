import OAI.MathematicalPhysics.DefocusingNLS.Certificates.SeparatorArithmetic

namespace OAI

/-!
# Rational disk data for the degree-fifteen separator polynomials

Centers are Gaussian integers divided by one million; disk radius is
`100 / 1000000`. The coefficient bounds are exact integer inequalities.
-/

namespace DefocusingNLS.SeparatorArithmetic

def diskScale : ℤ := 1000000
def diskRadius : ℤ := 100

def diskCenters (ℓ : Fin 4) : Fin 15 → GaussianInt :=
  ![![⟨-8123630, -31766832⟩, ⟨-8123630, 31766832⟩, ⟨-2852297, -508076⟩,
      ⟨-2852297, 508076⟩, ⟨-2433515, -6697195⟩, ⟨-2433515, 6697195⟩,
      ⟨-1820287, -2411053⟩, ⟨-1820287, 2411053⟩, ⟨-1757121, -1089576⟩,
      ⟨-1757121, 1089576⟩, ⟨-612406, -638366⟩, ⟨-612406, 638366⟩,
      ⟨-395408, 0⟩, ⟨31393, 0⟩, ⟨1031280, 0⟩],
    ![⟨-9281712, -32071684⟩, ⟨-9281712, 32071684⟩, ⟨-2664076, -7044582⟩,
      ⟨-2664076, 7044582⟩, ⟨-2482266, 0⟩, ⟨-2468408, 0⟩,
      ⟨-1944315, -2670218⟩, ⟨-1944315, 2670218⟩, ⟨-1773434, -956885⟩,
      ⟨-1773434, 956885⟩, ⟨-1102082, -305188⟩, ⟨-1102082, 305188⟩,
      ⟨-464821, 0⟩, ⟨-115059, 0⟩, ⟨530543, 0⟩],
    ![⟨-10389538, -32400115⟩, ⟨-10389538, 32400115⟩, ⟨-2898298, -7383939⟩,
      ⟨-2898298, 7383939⟩, ⟨-2180223, -559919⟩, ⟨-2180223, 559919⟩,
      ⟨-2114597, -2913593⟩, ⟨-2114597, 2913593⟩, ⟨-1873174, 0⟩,
      ⟨-1636518, -1162120⟩, ⟨-1636518, 1162120⟩, ⟨-1015304, -461931⟩,
      ⟨-1015304, 461931⟩, ⟨-94561, -919837⟩, ⟨-94561, 919837⟩],
    ![⟨-11448031, -32743955⟩, ⟨-11448031, 32743955⟩, ⟨-3144105, -7703209⟩,
      ⟨-3144105, 7703209⟩, ⟨-2548633, 0⟩, ⟨-2332359, -3241382⟩,
      ⟨-2332359, 3241382⟩, ⟨-2107135, -1004078⟩, ⟨-2107135, 1004078⟩,
      ⟨-1171235, -202886⟩, ⟨-1171235, 202886⟩, ⟨-979187, -1251033⟩,
      ⟨-979187, 1251033⟩, ⟨-809256, -2065587⟩, ⟨-809256, 2065587⟩]] ℓ

/-- Coefficients of `D^15 P((c + X)/D)`; all denominators are cleared. -/
def centeredCoefficient (ℓ : ℕ) (c : GaussianInt) (i : ℕ) : GaussianInt :=
  ((List.range (16 - i)).map fun j =>
    ((windingCoefficient ℓ (j + i) * (Nat.choose (j + i) i : ℤ) *
      diskScale ^ (15 - (j + i)) : ℤ) : GaussianInt) * c ^ j).sum

def coefficientUpper (z : GaussianInt) : ℤ := |z.re| + |z.im|
def coefficientLower (z : GaussianInt) : ℤ := max |z.re| |z.im|

def diskErrorBound (ℓ : ℕ) (c : GaussianInt) : ℤ :=
  coefficientUpper (centeredCoefficient ℓ c 0) +
    ((List.range 14).map fun j =>
      coefficientUpper (centeredCoefficient ℓ c (j + 2)) * diskRadius ^ (j + 2)).sum

def diskBound (ℓ : Fin 4) (j : Fin 15) : Prop :=
  diskErrorBound ℓ (diskCenters ℓ j) ≤
    coefficientLower (centeredCoefficient ℓ (diskCenters ℓ j) 1) * diskRadius

instance (ℓ : Fin 4) (j : Fin 15) : Decidable (diskBound ℓ j) := by
  unfold diskBound
  infer_instance

theorem disk_bounds_zero : ∀ j, diskBound 0 j := by decide +kernel
theorem disk_bounds_one : ∀ j, diskBound 1 j := by decide +kernel
theorem disk_bounds_two : ∀ j, diskBound 2 j := by decide +kernel
theorem disk_bounds_three : ∀ j, diskBound 3 j := by decide +kernel

theorem disk_bound (ℓ : Fin 4) (j : Fin 15) : diskBound ℓ j := by
  fin_cases ℓ
  · exact disk_bounds_zero j
  · exact disk_bounds_one j
  · exact disk_bounds_two j
  · exact disk_bounds_three j

theorem disk_linear_nonzero (ℓ : Fin 4) : ∀ j : Fin 15,
    centeredCoefficient ℓ (diskCenters ℓ j) 1 ≠ 0 := by
  fin_cases ℓ <;> decide +kernel

theorem disk_centers_separated (ℓ : Fin 4) : ∀ i j : Fin 15, i ≠ j →
    2 * diskRadius < |(diskCenters ℓ i).re - (diskCenters ℓ j).re| ∨
    2 * diskRadius < |(diskCenters ℓ i).im - (diskCenters ℓ j).im| := by
  fin_cases ℓ <;> decide +kernel

theorem disk_centers_avoid_axis (ℓ : Fin 4) : ∀ j : Fin 15,
    diskRadius < |(diskCenters ℓ j).re| := by
  fin_cases ℓ <;> decide +kernel

def positiveRootCount : Fin 4 → ℕ := ![2, 1, 0, 0]

theorem positive_disk_count (ℓ : Fin 4) :
    (Finset.univ.filter fun j : Fin 15 => 0 < (diskCenters ℓ j).re).card =
      positiveRootCount ℓ := by
  fin_cases ℓ <;> decide +kernel

end DefocusingNLS.SeparatorArithmetic

end OAI
