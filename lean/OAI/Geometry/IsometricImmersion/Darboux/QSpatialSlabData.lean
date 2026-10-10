import OAI.Geometry.IsometricImmersion.Darboux.QInitialEnergy
import OAI.Geometry.IsometricImmersion.Energy.LocalQResidualL2
import OAI.Geometry.IsometricImmersion.Metrics.MetricHorizontalRequests

namespace OAI

noncomputable section
open Set
open scoped ContDiff NNReal

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry SmoothLocal.Weighted SmoothLocal.ODE SmoothLocal.Hyperbolic

def QLowBounds (g : MetricField) (z : Coord → ℝ) (S : Set Coord)
    (s0 M speed : ℝ) : Prop :=
  ∀ p ∈ S, s0 ≤ heightQCoefficient g z 5 p ∧
    |heightQCoefficient g z 2 p| ≤ M ∧ |heightQCoefficient g z 3 p| ≤ M ∧
    |heightQCoefficient g z 5 p| ≤ M ∧
    |coordPartial 0 (heightQCoefficient g z 4) p| ≤ M ∧
    |coordPartial 0 (heightQCoefficient g z 5) p| ≤ M ∧
    |coordPartial 1 (heightQCoefficient g z 5) p| ≤ M ∧
    |heightQCoefficient g z 4 p| + Real.sqrt (heightQCoefficient g z 5 p) ≤ speed

theorem QLowBounds.mono_set {g : MetricField} {z : Coord → ℝ} {S T : Set Coord}
    {s0 M speed : ℝ} (h : QLowBounds g z S s0 M speed) (hTS : T ⊆ S) :
    QLowBounds g z T s0 M speed := fun p hp => h p (hTS hp)

theorem QLowBounds.high_coefficients
    {g : MetricField} {z : Coord → ℝ} {S : Set Coord} {s0 M speed : ℝ}
    (h : QLowBounds g z S s0 M speed) (hM : 0 ≤ M) (ell : ℕ) {p : Coord} (hp : p ∈ S) :
    |qHighBTheta g z ell p| ≤ M * (ell + 1) ∧
    |qHighBXi g z ell p| ≤ M * (ell + 1) ∧
    |coordPartial 0 (heightQCoefficient g z 4) p| ≤ M * (ell + 1) ∧
    |coordPartial 0 (heightQCoefficient g z 5) p| ≤ M * (ell + 1) ∧
    |coordPartial 1 (heightQCoefficient g z 5) p| ≤ M * (ell + 1) := by
  obtain ⟨_, h2, h3, _, h4x, h5x, h5t, _⟩ := h p hp
  have he : 0 ≤ (ell : ℝ) := Nat.cast_nonneg ell
  have hB : M ≤ M * (ell + 1) := by nlinarith
  have hbt : |qHighBTheta g z ell p| ≤ M * (ell + 1) := by
    unfold qHighBTheta
    calc
      _ ≤ |heightQCoefficient g z 3 p| + |(ell : ℝ) * coordPartial 0 (heightQCoefficient g z 4) p| := abs_add_le _ _
      _ ≤ M + (ell : ℝ) * M := by
        rw [abs_mul, abs_of_nonneg he]
        exact add_le_add h3 (mul_le_mul_of_nonneg_left h4x he)
      _ = _ := by ring
  have hbx : |qHighBXi g z ell p| ≤ M * (ell + 1) := by
    unfold qHighBXi
    calc
      _ ≤ |heightQCoefficient g z 2 p| + |(ell : ℝ) * coordPartial 0 (heightQCoefficient g z 5) p| := abs_add_le _ _
      _ ≤ M + (ell : ℝ) * M := by
        rw [abs_mul, abs_of_nonneg he]
        exact add_le_add h2 (mul_le_mul_of_nonneg_left h5x he)
      _ = _ := by ring
  exact ⟨hbt, hbx, h4x.trans hB, h5x.trans hB, h5t.trans hB⟩

theorem shrinkingSlab_mono_top {xl xr a b t speed : ℝ} (ht : t ≤ b) :
    shrinkingSlab xl xr a t speed ⊆ shrinkingSlab xl xr a b speed := by
  intro p hp
  exact ⟨⟨hp.1.1, hp.1.2.trans ht⟩, hp.2⟩

theorem SpatialSliceL2Bound.mono_order_budget
    {ι : Type*} {F : ι → Coord → ℝ} {theta left right : ℝ}
    {N n : ℕ} {H H' : ℝ≥0}
    (h : SpatialSliceL2Bound F theta left right N H) (hn : n ≤ N) (hH : H ≤ H') :
    SpatialSliceL2Bound F theta left right n H' := by
  intro i k hk
  exact (h i k (hk.trans hn)).trans (by exact_mod_cast hH)

end SmoothLocal.HighEquation

end

end OAI
