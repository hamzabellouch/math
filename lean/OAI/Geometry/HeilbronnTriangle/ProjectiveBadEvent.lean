import OAI.Geometry.HeilbronnTriangle.HomogeneousGeometry
import OAI.Geometry.HeilbronnTriangle.GeometricAlteration
import OAI.Geometry.HeilbronnTriangle.LiftedBadEvent

namespace OAI


namespace Problem355.Homogeneous

open Finset
noncomputable section
attribute [local instance] Classical.propDecidable

def projectedDistinct (u v w : Column) : Prop :=
  project u ≠ project v ∧ project u ≠ project w ∧ project v ≠ project w

def integerColumn (A : Matrix (Fin 3) (Fin 3) ℤ) (j : Fin 3) : Column :=
  fun i => (A i j : ℝ)

 theorem integer_columns_det (A : Matrix (Fin 3) (Fin 3) ℤ) :
    (columns (integerColumn A 0) (integerColumn A 1) (integerColumn A 2)).det =
      (A.det : ℝ) := by
  simp [columns, integerColumn, Matrix.det_fin_three]

theorem smallTriangle_low_determinant {N τ : ℝ} (hN : 0 < N) (hτ : 0 ≤ τ)
    {u v w : Column} (hu : InBox N u) (hv : InBox N v) (hw : InBox N w)
    (hsmall : Alteration.smallTriangle (τ / (16 * N ^ 3))
      (project u) (project v) (project w)) :
    projectedDistinct u v w ∧ |(columns u v w).det| < τ := by
  refine ⟨⟨hsmall.1, hsmall.2.1, hsmall.2.2.1⟩, ?_⟩
  by_contra hn
  have hbound := project_area_lower_bound_of_box hN hτ hu hv hw (le_of_not_gt hn)
  exact (not_le_of_gt hsmall.2.2.2) hbound

theorem smallTriangle_integer_determinant {N : ℝ} {τ : ℤ}
    (hN : 0 < N) (hτ : 0 ≤ τ) {u v w : Column}
    (hu : InBox N u) (hv : InBox N v) (hw : InBox N w)
    (d : ℤ) (hd : (columns u v w).det = (d : ℝ))
    (hsmall : Alteration.smallTriangle ((τ : ℝ) / (16 * N ^ 3))
      (project u) (project v) (project w)) :
    projectedDistinct u v w ∧ |d| ≤ τ := by
  have h := smallTriangle_low_determinant hN (by exact_mod_cast hτ) hu hv hw hsmall
  refine ⟨h.1, ?_⟩
  have hreal : |(d : ℝ)| < (τ : ℝ) := by simpa only [hd] using h.2
  have hint : |d| < τ := by exact_mod_cast hreal
  exact hint.le

theorem smallTriangle_mass_le_distinct_low_determinant
    {X : Type*} [DecidableEq X] (S : Finset X)
    (u v w : X → Column) (d : X → ℤ) (μ : X → ℝ)
    {N : ℝ} {τ : ℤ} (hN : 0 < N) (hτ : 0 ≤ τ)
    (hu : ∀ x ∈ S, InBox N (u x)) (hv : ∀ x ∈ S, InBox N (v x))
    (hw : ∀ x ∈ S, InBox N (w x))
    (hd : ∀ x ∈ S, (columns (u x) (v x) (w x)).det = (d x : ℝ))
    (hμ : ∀ x ∈ S, 0 ≤ μ x) :
    (∑ x ∈ S.filter (fun x => Alteration.smallTriangle
      ((τ : ℝ) / (16 * N ^ 3)) (project (u x)) (project (v x)) (project (w x))), μ x) ≤
    ∑ x ∈ (S.filter (fun x => projectedDistinct (u x) (v x) (w x))).filter
      (fun x => |d x| ≤ τ), μ x := by
  classical
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro x hx
    obtain ⟨hxS, hxsmall⟩ := Finset.mem_filter.mp hx
    have h := smallTriangle_integer_determinant hN hτ
      (hu x hxS) (hv x hxS) (hw x hxS) (d x) (hd x hxS) hxsmall
    exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hxS, h.1⟩, h.2⟩
  · intro x hx _
    exact hμ x (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).1

end
end Problem355.Homogeneous

end OAI
